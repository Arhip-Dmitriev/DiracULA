# Copyright 2026 Arkhip A. Dmitriev
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""The mirror of ``DiracULA.LSym``, ``LDigit``, ``LTable``, ``LCanon`` and ``LPass``: symbolic
sums with integer atoms, their normaliser and the passes under facts, on tuples.

An atom is ``(id, f, ks, dp, args)``, each argument ``(IPoly, DMon)``; a term is
``(CMon, sums, atoms, dels, phs)``. Every function follows its Lean namesake, so that
:func:`nf_a` predicts ``nfA``.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from fractions import Fraction
from typing import Any

from diracula import lean_sym as Y

Atom = tuple[int, int, tuple[int, ...], tuple[Y.DMon, ...], tuple[tuple[Y.IPoly, Y.DMon], ...]]
ATm = tuple[
    Y.CMon, tuple[tuple[int, Y.DMon], ...], tuple[Atom, ...], tuple[Y.Fac, ...], tuple[Y.Fac, ...]
]

ABASE = 3000000
RBASE = 2000000
AROUNDS = 8


# variables


def ip_vs(p: Y.IPoly) -> list[int]:
    return [x for m, _ in p for x in m]


def at_vs(a: Atom) -> list[int]:
    return [x for p, _ in a[4] for x in ip_vs(p)]


def arg_vs(l: Sequence[Atom]) -> list[int]:
    return [x for a in l for x in at_vs(a)]


def ids(l: Sequence[Atom]) -> list[int]:
    return [a[0] for a in l]


def fvs(t: ATm) -> list[int]:
    return [x for f in (*t[3], *t[4]) for x in ip_vs(f[1])]


def rvs(t: ATm) -> list[int]:
    return fvs(t) + arg_vs(t[2]) + ids(t[2])


def abvs(t: ATm) -> list[int]:
    return [x for x, _ in t[1]]


def all_v(t: ATm) -> list[int]:
    return rvs(t) + abvs(t)


def ax_vs(e: Sequence[ATm]) -> list[int]:
    return [x for t in e for x in rvs(t)]


# renaming


def im_ren(m: Callable[[int], int], mon: Sequence[int]) -> tuple[int, ...]:
    acc: tuple[int, ...] = ()
    for x in reversed(mon):
        acc = Y.im_ins(m(x), acc)
    return acc


def ip_ren(m: Callable[[int], int], p: Y.IPoly) -> Y.IPoly:
    acc: Y.IPoly = ()
    for mon, c in reversed(p):
        acc = Y.ip_ins(im_ren(m, mon), c, acc)
    return acc


def fac_ren(m: Callable[[int], int], f: Y.Fac) -> Y.Fac:
    return (f[0], ip_ren(m, f[1]))


def at_ren(m: Callable[[int], int], a: Atom) -> Atom:
    return (m(a[0]), a[1], a[2], a[3], tuple((ip_ren(m, p), d) for p, d in a[4]))


def t_ren(m: Callable[[int], int], t: ATm) -> ATm:
    return (
        t[0],
        tuple((m(x), d) for x, d in t[1]),
        tuple(at_ren(m, a) for a in t[2]),
        tuple(fac_ren(m, f) for f in t[3]),
        tuple(fac_ren(m, f) for f in t[4]),
    )


def inj_on(m: Callable[[int], int], s: Sequence[int]) -> bool:
    return all(m(a) != m(b) or a == b for a in s for b in s)


# products


def t_mul(s: ATm, t: ATm) -> ATm:
    return (Y.cm_mul(s[0], t[0]), s[1] + t[1], s[2] + t[2], s[3] + t[3], s[4] + t[4])


def t_mul_ok(s: ATm, t: ATm) -> bool:
    rt_, rs = set(rvs(t)), set(rvs(s))
    return all(x not in rt_ for x in abvs(s) + ids(s[2])) and all(
        x not in rs for x in abvs(t) + ids(t[2])
    )


def ax_mul(a: Sequence[ATm], b: Sequence[ATm]) -> list[ATm]:
    return [t_mul(s, t) for s in a for t in b]


def ax_mul_ok(a: Sequence[ATm], b: Sequence[ATm]) -> bool:
    return all(t_mul_ok(s, t) for s in a for t in b)


# eliminations


def at_sub(x: int, v: Y.IPoly, a: Atom) -> Atom:
    return (a[0], a[1], a[2], a[3], tuple((Y.ip_subst(x, v, p), d) for p, d in a[4]))


def args_per(x: int, m: Y.DMon, l: Sequence[Atom]) -> bool:
    return all(not Y.ip_has(x, p) or Y.dm_dvd(d, m) for a in l for p, d in a[4])


def plain_p(l: Sequence[Atom], p: Y.IPoly) -> bool:
    i = set(ids(l))
    return all(y not in i for y in ip_vs(p))


AElim = tuple[Y.CMon, tuple[Atom, ...], tuple[Y.Fac, ...], tuple[Y.Fac, ...]]


def elim_plain(
    x: int, d: Y.DMon, ats: tuple[Atom, ...], ds: tuple[Y.Fac, ...], ps: tuple[Y.Fac, ...]
) -> AElim | None:
    if x in arg_vs(ats) + ids(ats):
        return None
    e = Y.elim_var(x, d, ds, ps)
    if e is None:
        return None
    return e[0], ats, e[1], e[2]


def elim_pin1(
    x: int,
    d: Y.DMon,
    ats: tuple[Atom, ...],
    pre: tuple[Y.Fac, ...],
    f: Y.Fac,
    post: tuple[Y.Fac, ...],
    ps: tuple[Y.Fac, ...],
) -> AElim | None:
    lin = Y.ip_lin(x, f[1])
    if lin is None:
        return None
    a, b = lin
    s = Y.ip_const(a)
    if s is None:
        return None
    if (
        s in (1, -1)
        and d[0] != 0
        and Y.dm_dvd(f[0], d)
        and x not in ids(ats)
        and plain_p(ats, b)
        and args_per(x, f[0], ats)
        and all(not Y.fac_has(x, g) or Y.dm_dvd(g[0], f[0]) for g in (*pre, *post, *ps))
    ):
        v = Y.pin_val(s, b)
        return (
            Y.rt_d(Y.dm_div(d, f[0]), 2),
            tuple(at_sub(x, v, t) for t in ats),
            tuple(Y.fac_sub(x, v, g) for g in (*pre, *post)),
            tuple(Y.fac_sub(x, v, g) for g in ps),
        )
    return None


def elim_pin(
    x: int, d: Y.DMon, ats: tuple[Atom, ...], ds: tuple[Y.Fac, ...], ps: tuple[Y.Fac, ...]
) -> AElim | None:
    for pre, f, post in Y._splits(ds):
        e = elim_pin1(x, d, ats, pre, f, post, ps)
        if e is not None:
            return e
    return None


def dig_at(x: int, d: Y.DMon, n: Y.DMon, a: Atom) -> Y.IPoly | None:
    if not (a[1] == 0 and a[2] == () and a[3] == (d, n)):
        return None
    if len(a[4]) != 2:
        return None
    (p, m1), (q, m2) = a[4]
    if m1 == n and m2 == n and p == Y.ip_v(x) and not Y.ip_has(x, q):
        return q
    if m1 == n and m2 == n and q == Y.ip_v(x) and not Y.ip_has(x, p):
        return p
    return None


def coefs(zs: Sequence[int], r: Y.IPoly) -> tuple[list[int], Y.IPoly] | None:
    if not zs:
        return [], r
    lin = Y.ip_lin(zs[0], r)
    if lin is None:
        return None
    k = Y.ip_const(lin[0])
    rest = coefs(zs[1:], lin[1])
    if k is None or rest is None:
        return None
    return [k, *rest[0]], rest[1]


def fac_any(zs: Sequence[int], f: Y.Fac) -> bool:
    return any(Y.fac_has(z, f) for z in zs)


def psum(ps: Sequence[Y.Fac]) -> Y.IPoly:
    acc: Y.IPoly = ()
    for f in reversed(ps):
        acc = Y.ip_add(f[1], acc)
    return acc


def elim_digit(
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    x: int,
    dd_: Y.DMon,
    ats: tuple[Atom, ...],
    ds: tuple[Y.Fac, ...],
    ps: tuple[Y.Fac, ...],
) -> AElim | None:
    others = tuple(a for a in ats if x not in at_vs(a))
    dd = tuple(a for a in ats if x in at_vs(a))
    if not dd or len(dd[0][3]) != 2:
        return None
    a0 = dd[0]
    d, n = a0[3]
    As = [dig_at(x, d, n, a) for a in dd]
    if any(a is None for a in As):
        return None
    zs = ids(dd)

    def sel(f: Y.Fac) -> bool:
        return f[0] == d and (Y.fac_has(x, f) or fac_any(zs, f))

    lin = Y.ip_lin(x, psum([f for f in ps if sel(f)]))
    if lin is None:
        return None
    b, r0 = lin
    co = coefs(zs, r0)
    if co is None:
        return None
    cs, r = co
    rest = tuple(f for f in ps if not sel(f))
    zset = set(zs)
    ok = (
        ats == others + dd
        and dd_ == n
        and (d, n) in pw
        and dd_[0] != 0
        and len(zs) == len(zset)
        and x not in ids(ats)
        and x not in arg_vs(others)
        and all(z not in arg_vs(ats) and z not in ip_vs(b) and z not in ip_vs(r) for z in zs)
        and all(plain_p(ats, a) for a in As)  # type: ignore[arg-type]
        and all(not Y.fac_has(x, f) and not fac_any(zs, f) for f in ds)
        and all(not Y.fac_has(x, f) and not fac_any(zs, f) for f in rest)
        and not Y.ip_has(x, r)
        and not Y.ip_has(x, b)
    )
    if not ok:
        return None
    dz: Atom = (a0[0], 3, tuple(cs), (d, n), tuple((a, n) for a in As) + ((b, d),))  # type: ignore[assignment]
    return Y.rt_d(n, 2), others + (dz,), ds + ((n, Y.ip_v(a0[0])),), rest + ((d, r),)


def elim_pin_c1(
    x: int,
    d: Y.DMon,
    ats: tuple[Atom, ...],
    pre: tuple[Y.Fac, ...],
    f: Y.Fac,
    post: tuple[Y.Fac, ...],
    ps: tuple[Y.Fac, ...],
) -> AElim | None:
    lin = Y.ip_lin(x, f[1])
    if lin is None or not (Y.dm_const(d) and d[0] != 0 and f[0] == d) or x in ids(ats):
        return None
    s, b = Y.ip_const(lin[0]), Y.ip_const(lin[1])
    if s not in (1, -1) or b is None:
        return None
    v = Y.ip_c(Y._emod(-s * b, d[0]))
    return (
        Y.of_q(1),
        tuple(at_sub(x, v, t) for t in ats),
        tuple(Y.fac_sub(x, v, g) for g in (*pre, *post)),
        tuple(Y.fac_sub(x, v, g) for g in ps),
    )


def elim_pin_c(
    x: int, d: Y.DMon, ats: tuple[Atom, ...], ds: tuple[Y.Fac, ...], ps: tuple[Y.Fac, ...]
) -> AElim | None:
    for pre, f, post in Y._splits(ds):
        e = elim_pin_c1(x, d, ats, pre, f, post, ps)
        if e is not None:
            return e
    return None


def elim_pin_a(
    x: int, d: Y.DMon, ats: tuple[Atom, ...], ds: tuple[Y.Fac, ...], ps: tuple[Y.Fac, ...]
) -> AElim | None:
    a = tuple(b for b in ats if x not in at_vs(b))
    bt = tuple(b for b in ats if x in at_vs(b))
    i = ids(ats)
    if not (wf_a(ats) and len(i) == len(set(i)) and wf_a(a + bt) and x not in i):
        return None
    e = elim_pin(x, d, bt, ds, ps)
    if e is None:
        return None
    return e[0], a + e[1], e[2], e[3]


def a_elim_var(
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    x: int,
    d: Y.DMon,
    ats: tuple[Atom, ...],
    ds: tuple[Y.Fac, ...],
    ps: tuple[Y.Fac, ...],
) -> AElim | None:
    for fn in (elim_plain, elim_pin):
        e = fn(x, d, ats, ds, ps)
        if e is not None:
            return e
    e = elim_digit(pw, x, d, ats, ds, ps)
    if e is not None:
        return e
    e = elim_pin_c(x, d, ats, ds, ps)
    if e is not None:
        return e
    e = elim_pin_a(x, d, ats, ds, ps)
    if e is not None:
        return e
    e = elim_lin_c(pw, x, d, ats, ds, ps)
    if e is not None:
        return e
    return elim_pin_r(x, d, ats, ds, ps)


def pin_r_of(x: int, d: Y.DMon, a: Sequence[Atom], f: Y.Fac) -> int | None:
    if f[0] != d or not (Y.dm_const(d) and d[0] != 0):
        return None
    lin = Y.ip_lin(x, f[1])
    if lin is None:
        return None
    s = Y.ip_const(lin[0])
    b = lin[1]
    if s not in (1, -1) or len(b) != 1 or len(b[0][0]) != 1:
        return None
    (u,), c = b[0]
    bu = find_at(a, u)
    if bu is None or bu[1] != 2 or len(bu[4]) != 1 or bu[4][0][1] != d:
        return None
    return u if Y._emod(s + c, d[0]) == 0 else None


def elim_pin_r(
    x: int, d: Y.DMon, ats: tuple[Atom, ...], ds: tuple[Y.Fac, ...], ps: tuple[Y.Fac, ...]
) -> AElim | None:
    a = tuple(b for b in ats if x not in at_vs(b))
    bt = tuple(b for b in ats if x in at_vs(b))
    i = ids(ats)
    if x in i:
        return None
    for pre, f, post in Y._splits(ds):
        u = pin_r_of(x, d, a, f)
        if u is None:
            continue
        if not (wf_a(ats) and len(i) == len(set(i)) and wf_a(a + bt)):
            return None
        v = Y.ip_v(u)
        return (
            Y.of_q(1),
            a + tuple(at_sub(x, v, t) for t in bt),
            tuple(Y.fac_sub(x, v, g) for g in (*pre, *post)),
            tuple(Y.fac_sub(x, v, g) for g in ps),
        )
    return None


def elim_lin_c(
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    x: int,
    dd: Y.DMon,
    ats: tuple[Atom, ...],
    ds: tuple[Y.Fac, ...],
    ps: tuple[Y.Fac, ...],
) -> AElim | None:
    sel = [f for f in ps if Y.fac_has(x, f)]
    if not sel:
        return None
    d = sel[0][0]
    lin = Y.ip_lin(x, psum(sel))
    if lin is None:
        return None
    ap, r = lin
    a = Y.ip_const(ap)
    if a is None:
        return None
    if not (
        (d, dd) in pw
        and Y.dm_const(d)
        and d[0] != 0
        and all(f[0] == d for f in sel)
        and x not in arg_vs(ats) + ids(ats)
        and all(not Y.fac_has(x, f) for f in ds)
    ):
        return None
    rest = tuple(f for f in ps if not Y.fac_has(x, f))
    return Y.rt_d(dd, 2), ats, ds + ((dd, Y.ip_c(Y._emod(a, d[0]))),), rest + ((d, r),)


def a_elim_step(pw: Sequence[tuple[Y.DMon, Y.DMon]], t: ATm) -> ATm | None:
    for pre, (x, d), post in Y._splits(t[1]):
        if x in [y for y, _ in (*pre, *post)]:
            continue
        e = a_elim_var(pw, x, d, t[2], t[3], t[4])
        if e is not None:
            return (Y.cm_mul(t[0], e[0]), pre + post, e[1], e[2], e[3])
    return None


def a_elim_all(pw: Sequence[tuple[Y.DMon, Y.DMon]], n: int, t: ATm) -> ATm:
    for _ in range(n):
        t2 = a_elim_step(pw, a_rules(len(t[2]) + 1, t))
        if t2 is None:
            return t
        t = t2
    return t


# canonicalisation


def canon_f(fl: Sequence[int], ds: tuple[Y.Fac, ...], ps: tuple[Y.Fac, ...]) -> Any:
    ds0, ps0 = Y.piv_pass(len(ds), (), ds, ps)
    dn = Y.norm_dels(fl, ds0)
    if dn is None:
        return None
    k, pn = Y.norm_phs(Y.ph_merge(ps0))
    dsort: tuple[Y.Fac, ...] = ()
    for f in reversed(dn):
        dsort = Y.del_ins(f, dsort)
    psort: tuple[Y.Fac, ...] = ()
    for f in reversed(pn):
        psort = Y.fac_ins(f, psort)
    return k, dsort, psort


def dz_poly(pw: Sequence[tuple[Y.DMon, Y.DMon]], ats: Sequence[Atom], a: Atom) -> Any:
    if a[1] != 3 or len(a[3]) != 2:
        return None
    d, n = a[3]
    ks, args = a[2], a[4]
    if len(ks) == 1 and len(args) == 2:
        (aa, m1), (bp, m2) = args
        b = Y.ip_const(bp)
        if b is None:
            return None
        c = ks[0]
        const = Y.dm_const(d)
        r = (-c * b) % d[0] if const and d[0] != 0 else -c * b
        if (
            (d, n) in pw
            and m1 == n
            and m2 == d
            and c in (1, -1)
            and 0 <= r
            and (r <= 1 or const)
            and plain_p(ats, aa)
        ):
            return n, Y.ip_sub(aa, Y.ip_c(r))
        if (d, n) in pw and m1 == n and m2 == d and aa == () and b in (1, -1):
            return n, Y.ip_c(1)
        return None
    if len(ks) == 2 and len(args) == 3:
        (a1, m1), (a2, m2), (bp, m3) = args
        c, c2 = ks
        if (
            (d, n) in pw
            and m1 == n
            and m2 == n
            and m3 == d
            and c in (1, -1)
            and (c2 == -c or (Y.dm_const(d) and Y._emod(c + c2, d[0]) == 0))
            and Y.ip_const(bp) == 0
            and plain_p(ats, a1)
            and plain_p(ats, a2)
        ):
            return n, Y.ip_sub(a1, a2)
    return None


def dz_find(pw: Sequence[tuple[Y.DMon, Y.DMon]], ats: Sequence[Atom], f: Y.Fac) -> Y.Fac | None:
    p = f[1]
    if not (len(p) == 1 and len(p[0][0]) == 1 and p[0][1] == 1):
        return None
    z = p[0][0][0]
    a = next((b for b in ats if b[0] == z), None)
    if a is None:
        return None
    r = dz_poly(pw, ats, a)
    if r is None:
        return None
    n, pp = r
    if f[0] == n and plain_p(ats, pp):
        return n, pp
    return None


def dz_step(pw: Sequence[tuple[Y.DMon, Y.DMon]], t: ATm) -> ATm:
    i = ids(t[2])
    if len(i) != len(set(i)):
        return t
    ds = tuple(dz_find(pw, t[2], f) or f for f in t[3])
    return (t[0], t[1], t[2], ds, t[4])


def is_zero_dig(a: Atom) -> bool:
    return a[1] == 0 and len(a[4]) == 2 and (a[4][0][0] == () or a[4][1][0] == ())


def zero_at(t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]) -> ATm | None:
    if is_zero_dig(a) and a[0] not in ids(post):
        z = a[0]
        return (
            t[0],
            t[1],
            pre + tuple(at_sub(z, (), b) for b in post),
            tuple(Y.fac_sub(z, (), f) for f in t[3]),
            tuple(Y.fac_sub(z, (), f) for f in t[4]),
        )
    return None


def drop_at(t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]) -> ATm | None:
    z = a[0]
    if z not in fvs(t) and z not in arg_vs(post) and z not in ids(post):
        return (t[0], t[1], pre + post, t[3], t[4])
    return None


def dedup_at(t: ATm, pre: tuple[Atom, ...], b: Atom, post: tuple[Atom, ...]) -> ATm | None:
    a = next((x for x in pre if x[0] != b[0] and x[1:] == b[1:]), None)
    if a is None:
        return None
    i = ids(t[2])
    if (
        len(i) == len(set(i))
        and all(plain_p(t[2], p) for p, _ in b[4])
        and b[0] not in arg_vs(t[2])
    ):
        v = Y.ip_v(a[0])
        return (
            t[0],
            t[1],
            t[2],
            tuple(Y.fac_sub(b[0], v, f) for f in t[3]),
            tuple(Y.fac_sub(b[0], v, f) for f in t[4]),
        )
    return None


def dz_drop_at(t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]) -> ATm | None:
    ks, args = a[2], a[4]
    if a[1] != 3 or len(args) != len(ks) + 1:
        return None
    pairs = list(zip(ks, args))
    if not any(p[1][0] == () for p in pairs):
        return None
    kept = [p for p in pairs if p[1][0] != ()]
    if not kept:
        return None
    a2: Atom = (
        a[0],
        3,
        tuple(k for k, _ in kept),
        a[3],
        tuple(x for _, x in kept) + tuple(args[len(ks) :]),
    )
    return (t[0], t[1], pre + (a2,) + post, t[3], t[4])


def a_rule1(t: ATm) -> ATm | None:
    for fn in (zero_at, drop_at, dedup_at, dz_drop_at):
        for pre, a, post in Y._splits(t[2]):
            r = fn(t, pre, a, post)
            if r is not None:
                return r
    return None


def a_rules(n: int, t: ATm) -> ATm:
    for _ in range(n):
        t2 = a_rule1(t)
        if t2 is None:
            return t
        t = t2
    return t


def wf_a(l: Sequence[Atom]) -> bool:
    for k, a in enumerate(l):
        later = set(ids(l[k:]))
        if any(v in later for v in at_vs(a)):
            return False
    return True


def uniq(l: Sequence[int]) -> list[int]:
    out: list[int] = []
    for x in l:
        if x not in out:
            out.append(x)
    return out


def canon_ren(t: ATm) -> ATm:
    occ = uniq(fvs(t) + ids(t[2]) + arg_vs(t[2]) + abvs(t))
    b = set(abvs(t))
    i = set(ids(t[2]))
    bl = [v for v in occ if v in b]
    al = [v for v in occ if v in i and v not in b]

    def m(v: int) -> int:
        if v in bl:
            return RBASE + bl.index(v)
        if v in al:
            return ABASE + al.index(v)
        return v

    if inj_on(m, all_v(t)) and wf_a(t[2]):
        return t_ren(m, t)
    return t


def dm_key(m: Y.DMon) -> list[int]:
    return [m[0], len(m[1]), *m[1]]


def ip_key(p: Y.IPoly) -> list[int]:
    out = [len(p)]
    for mon, c in p:
        out += [len(mon), *mon, c]
    return out


def at_key(a: Atom) -> list[int]:
    out = [-a[1], len(a[2]), *a[2], len(a[3])]
    for m in a[3]:
        out += dm_key(m)
    out.append(len(a[4]))
    for p, m in a[4]:
        out += ip_key(p) + dm_key(m)
    return out


def z_lt(a: Sequence[int], b: Sequence[int]) -> bool:
    for x, y in zip(a, b):
        if x != y:
            return x < y
    return len(a) < len(b)


def pick_min(rest: Sequence[Atom]) -> Atom | None:
    i = set(ids(rest))
    best: Atom | None = None
    for a in rest:
        if all(v not in i for v in at_vs(a)) and (best is None or z_lt(at_key(a), at_key(best))):
            best = a
    return best


def topo(n: int, rest: Sequence[Atom]) -> tuple[Atom, ...] | None:
    acc: list[Atom] = []
    rest = list(rest)
    for _ in range(n):
        if not rest:
            return tuple(acc)
        a = pick_min(rest)
        if a is None:
            return None
        acc.append(a)
        rest.remove(a)
    return tuple(acc) if not rest else None


def sort_tab(t: ATm) -> ATm:
    lst = topo(len(t[2]) + 1, t[2])
    i = ids(t[2])
    if (
        lst is None
        or not wf_a(t[2])
        or len(i) != len(set(i))
        or not wf_a(lst)
        or sorted(lst) != sorted(t[2])
    ):
        return t
    return (t[0], t[1], lst, t[3], t[4])


def sort_sums(t: ATm) -> ATm:
    b = abvs(t)
    if len(b) != len(set(b)):
        return t
    out: list[tuple[int, Y.DMon]] = []
    for p in reversed(t[1]):
        k = 0
        while k < len(out) and not p[0] <= out[k][0]:
            k += 1
        out.insert(k, p)
    return (t[0], tuple(out), t[2], t[3], t[4])


def dvd_p(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], k: Y.DMon, m: Y.DMon) -> bool:
    return Y.dm_dvd(k, m) or ((k, m) in pw and Y.dm_den(m, lambda i: Y.flv(fl, i)) >= 2)


def mod_drop_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    if a[1] != 2 or len(a[4]) != 1:
        return None
    q, m = a[4][0]
    z = a[0]
    if (
        all(y != z and y not in ids(post) for y in ip_vs(q))
        and z not in arg_vs(t[2])
        and z not in ids(post)
        and all(
            not Y.fac_has(z, g) or (g[0][0] != 0 and dvd_p(fl, pw, g[0], m)) for g in (*t[3], *t[4])
        )
    ):
        return (
            t[0],
            t[1],
            t[2],
            tuple(Y.fac_sub(z, q, g) for g in t[3]),
            tuple(Y.fac_sub(z, q, g) for g in t[4]),
        )
    return None


def mod_rules(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], n: int, t: ATm) -> ATm:
    for _ in range(n):
        t2 = None
        for pre, a, post in Y._splits(t[2]):
            t2 = mod_drop_at(fl, pw, t, pre, a, post)
            if t2 is not None:
                break
        if t2 is None:
            return t
        t = t2
    return t


ZM: Y.DMon = (0, ())
TWO: Y.DMon = (2, ())


def cst_val(a: Atom) -> int | None:
    if a[1] == 7 and len(a[4]) == 1 and a[4][0][0] == ():
        return 1
    if a[1] == 10 and len(a[4]) == 2 and a[4][1][0] == ():
        return 0
    if a[1] == 2 and len(a[4]) == 1:
        c = Y.ip_const(a[4][0][0])
        if c is not None and Y.dm_const(a[4][0][1]):
            return Y._emod(c, a[4][0][1][0])
        if c == 0:
            return 0
    if a[1] == 13 and len(a[4]) == 1 and a[4][0][0] == ():
        return 0
    return None


def cst_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    c = cst_val(a)
    if c is None or a[0] in ids(post):
        return None
    v = Y.ip_c(c)
    z = a[0]
    return (
        t[0],
        t[1],
        pre + tuple(at_sub(z, v, b) for b in post),
        tuple(Y.fac_sub(z, v, f) for f in t[3]),
        tuple(Y.fac_sub(z, v, f) for f in t[4]),
    )


def xor_z(a: Atom) -> Atom | None:
    if a[1] != 1 or len(a[4]) != 2:
        return None
    (p, m), (q, m2) = a[4]
    if q == () and m[0] != 0:
        return (a[0], 2, a[2], a[3], ((p, m),))
    if p == () and m2[0] != 0:
        return (a[0], 2, a[2], a[3], ((q, m2),))
    return None


def xor_z_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    a2 = xor_z(a)
    if a2 is None:
        return None
    return (t[0], t[1], pre + (a2,) + post, t[3], t[4])


def find_at(l: Sequence[Atom], z: int) -> Atom | None:
    return next((b for b in l if b[0] == z), None)


def is_bit(a: Atom | None) -> bool:
    return a is not None and a[1] == 2 and len(a[4]) == 1 and a[4][0][1] == TWO


def is_pw2(a: Atom | None) -> bool:
    return a is not None and a[1] == 7 and len(a[4]) == 1 and a[3] in ((), (TWO,))


def xor_x(pw: Sequence[tuple[Y.DMon, Y.DMon]], pre: Sequence[Atom], o: Atom) -> Atom | None:
    if o[1] != 1 or len(o[4]) != 2:
        return None
    (aa, m1), (bq, m2) = o[4]
    if not (len(aa) == 1 and aa[0][1] == 1 and len(aa[0][0]) == 1):
        return None
    if not (len(bq) == 1 and bq[0][1] == 1 and len(bq[0][0]) == 2):
        return None
    w = find_at(pre, aa[0][0][0])
    if w is None or w[1] != 1 or len(w[4]) != 2:
        return None
    (a, ma), (c1, mb) = w[4]
    if not (ma == m1 and mb == m1 and m2 == m1 and (TWO, m1) in pw):
        return None
    u, v = bq[0][0]
    for c, z in ((u, v), (v, u)):
        if (
            is_bit(find_at(pre, c))
            and is_pw2(find_at(pre, z))
            and c1 == Y.ip_sub(Y.ip_mul(Y.ip_v(c), Y.ip_v(z)), Y.ip_v(c))
        ):
            arg = Y.ip_sub(Y.ip_smul(2, Y.ip_mul(Y.ip_v(c), Y.ip_v(z))), Y.ip_v(c))
            return (o[0], o[1], o[2], o[3], ((a, m1), (arg, m1)))
    return None


def xor_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    i = ids(t[2])
    if not (wf_a(t[2]) and len(i) == len(set(i))):
        return None
    a2 = xor_x(pw, pre, a)
    if a2 is None:
        a2 = xor_p(pw, pre, a)
    if a2 is None:
        return None
    return (t[0], t[1], pre + (a2,) + post, t[3], t[4])


def xor_p(pw: Sequence[tuple[Y.DMon, Y.DMon]], pre: Sequence[Atom], o: Atom) -> Atom | None:
    if o[1] != 1 or len(o[4]) != 2:
        return None
    (aa, m1), (bq, m2) = o[4]
    if not (len(bq) == 1 and bq[0][1] == 1 and len(bq[0][0]) == 1):
        return None
    z = bq[0][0][0]
    if (
        m2 == m1
        and (TWO, m1) in pw
        and is_pw2(find_at(pre, z))
        and aa == Y.ip_sub(Y.ip_v(z), Y.ip_c(1))
    ):
        return (o[0], 2, o[2], o[3], ((Y.ip_sub(Y.ip_smul(2, Y.ip_v(z)), Y.ip_c(1)), m1),))
    return None


def dedup_a(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    b: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    a = next((x for x in pre if x[0] != b[0] and x[1:] == b[1:]), None)
    if a is None:
        return None
    i = ids(t[2])
    if not (
        len(i) == len(set(i)) and all(plain_p(t[2], p) for p, _ in b[4]) and b[0] in arg_vs(post)
    ):
        return None
    v = Y.ip_v(a[0])
    z = b[0]
    return (
        t[0],
        t[1],
        pre + tuple(at_sub(z, v, c) for c in post),
        tuple(Y.fac_sub(z, v, f) for f in t[3]),
        tuple(Y.fac_sub(z, v, f) for f in t[4]),
    )


def mod_c(a: Atom) -> Atom | None:
    if a[1] != 2 or len(a[4]) != 1:
        return None
    p, m = a[4][0]
    if not (Y.dm_const(m) and m[0] != 0):
        return None
    q = Y.ip_modc(m[0], p)
    if q == p:
        return None
    return (a[0], a[1], a[2], a[3], ((q, m),))


def mod_c_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    a2 = mod_c(a)
    if a2 is None:
        return None
    return (t[0], t[1], pre + (a2,) + post, t[3], t[4])


def dedup_w(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    b: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    a = next((x for x in pre if x[0] != b[0] and x[1:] == b[1:]), None)
    if a is None:
        return None
    i = ids(t[2])
    if not (wf_a(t[2]) and len(i) == len(set(i)) and b[0] in fvs(t)):
        return None
    v = Y.ip_v(a[0])
    return (
        t[0],
        t[1],
        t[2],
        tuple(Y.fac_sub(b[0], v, f) for f in t[3]),
        tuple(Y.fac_sub(b[0], v, f) for f in t[4]),
    )


def dsub_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    i = ids(t[2])
    if not (wf_a(t[2]) and len(i) == len(set(i))):
        return None
    later = set(ids((a, *post)))
    for o in at_vs(a):
        for f in t[3]:
            lin = Y.ip_lin(o, f[1])
            if lin is None:
                continue
            aa, b = lin
            s = Y.ip_const(aa)
            if (
                s in (1, -1)
                and f[0][0] != 0
                and o not in i
                and all(y not in later for y in ip_vs(b))
                and all(not Y.ip_has(o, p) or Y.dm_dvd(m, f[0]) for p, m in a[4])
            ):
                a2 = at_sub(o, Y.pin_val(s, b), a)
                return (t[0], t[1], (*pre, a2, *post), t[3], t[4])
    return None


def xor_of(pre: Sequence[Atom], x: Y.IPoly, n: Y.DMon) -> tuple[Y.IPoly, Y.IPoly] | None:
    if not (len(x) == 1 and x[0][1] == 1 and len(x[0][0]) == 1):
        return None
    w = find_at(pre, x[0][0][0])
    if w is None or w[1] != 1 or len(w[4]) != 2:
        return None
    (u, mu), (v, mv) = w[4]
    return (u, v) if mu == n and mv == n else None


def dot_xor(
    pw: Sequence[tuple[Y.DMon, Y.DMon]], pre: Sequence[Atom], a: Atom, b: int
) -> tuple[Atom, Atom] | None:
    if a[1] != 0 or len(a[3]) != 2 or len(a[4]) != 2:
        return None
    d, n = a[3]
    (x, m1), (c, m2) = a[4]
    if not (d == TWO and m1 == n and m2 == n and (TWO, n) in pw):
        return None
    uv = xor_of(pre, x, n)
    if uv is not None:
        u, v = uv
        return (b, 0, a[2], (d, n), ((u, n), (c, n))), (b + 1, 0, a[2], (d, n), ((v, n), (c, n)))
    uv = xor_of(pre, c, n)
    if uv is not None:
        u, v = uv
        return (b, 0, a[2], (d, n), ((x, n), (u, n))), (b + 1, 0, a[2], (d, n), ((x, n), (v, n)))
    return None


def dot_xor_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    b = max_v(t) + 1
    r = dot_xor(pw, pre, a, b)
    if r is None:
        return None
    i = ids(t[2])
    z = a[0]
    if not (
        wf_a(t[2])
        and len(i) == len(set(i))
        and z not in arg_vs(t[2])
        and all(not Y.fac_has(z, g) for g in t[3])
        and all(not Y.fac_has(z, g) or g[0] == TWO for g in t[4])
        and z in fvs(t)
    ):
        return None
    p = Y.ip_add(Y.ip_v(b), Y.ip_v(b + 1))
    return (
        t[0],
        t[1],
        (*pre, r[0], r[1], a, *post),
        tuple(Y.fac_sub(z, p, g) for g in t[3]),
        tuple(Y.fac_sub(z, p, g) for g in t[4]),
    )


def ddot_swap(a: Atom) -> Atom | None:
    if a[1] != 0 or len(a[4]) != 2:
        return None
    (p, m1), (q, m2) = a[4]
    if z_lt(ip_key(q) + dm_key(m2), ip_key(p) + dm_key(m1)):
        return (a[0], a[1], a[2], a[3], ((q, m2), (p, m1)))
    return None


def ddot_swap_at(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    t: ATm,
    pre: tuple[Atom, ...],
    a: Atom,
    post: tuple[Atom, ...],
) -> ATm | None:
    a2 = ddot_swap(a)
    if a2 is None:
        return None
    return (t[0], t[1], (*pre, a2, *post), t[3], t[4])


def is_m1(l: Sequence[Atom], z: int, n: Y.DMon) -> bool:
    b = find_at(l, z)
    return b is not None and b[1] == 13 and b[3] == (n,) and len(b[4]) == 1


def is_dim(l: Sequence[Atom], w: int, n: Y.DMon) -> bool:
    b = find_at(l, w)
    return b is not None and b[1] == 8 and b[3] == (n,) and b[4] == ()


def is_neg1(l: Sequence[Atom], z: int, n: Y.DMon) -> bool:
    b = find_at(l, z)
    return b is not None and b[1] == 2 and b[4] == ((Y.ip_c(-1), n),)


def m1_arg(pre: Sequence[Atom], a: Atom) -> Atom | None:
    if a[1] != 13 or len(a[3]) != 1 or len(a[4]) != 1:
        return None
    n = a[3][0]
    p, z0 = a[4][0]
    if z0 != ZM:
        return None
    z = next((z for z in ip_vs(p) if is_m1(pre, z, n)), None)
    if z is not None:
        b = find_at(pre, z)
        if b is None or len(b[4]) != 1:
            return None
        q, zb = b[4][0]
        if zb != ZM:
            return None
        return (a[0], a[1], a[2], a[3], ((Y.ip_subst(z, q, p), ZM),))
    w = next((w for w in ip_vs(p) if is_dim(pre, w, n)), None)
    if w is not None:
        return (a[0], a[1], a[2], a[3], ((Y.ip_subst(w, Y.ip_c(1), p), ZM),))
    u = next((u for u in ip_vs(p) if is_neg1(pre, u, n)), None)
    if u is None:
        return None
    return (a[0], a[1], a[2], a[3], ((Y.ip_subst(u, Y.ip_c(0), p), ZM),))


def m1_at(
    fl: Any, pw: Any, t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]
) -> ATm | None:
    a2 = m1_arg(pre, a)
    if a2 is None:
        return None
    i = ids(t[2])
    if not (wf_a(t[2]) and len(i) == len(set(i))):
        return None
    return (t[0], t[1], (*pre, a2, *post), t[3], t[4])


def alias_at(
    fl: Any, pw: Any, t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]
) -> ATm | None:
    if a[1] != 2 or len(a[4]) != 1:
        return None
    p, n = a[4][0]
    if not (len(p) == 1 and p[0][1] == 1 and len(p[0][0]) == 1):
        return None
    z = p[0][0][0]
    i = ids(t[2])
    if not (
        is_m1(pre, z, n)
        and Y.dm_den(n, lambda k: Y.flv(fl, k)) >= 2
        and wf_a(t[2])
        and len(i) == len(set(i))
    ):
        return None
    v = Y.ip_v(z)
    x = a[0]
    return (
        t[0],
        t[1],
        pre + tuple(at_sub(x, v, b) for b in post),
        tuple(Y.fac_sub(x, v, f) for f in t[3]),
        tuple(Y.fac_sub(x, v, f) for f in t[4]),
    )


def false_del(fl: Sequence[int], ats: Sequence[Atom], f: Y.Fac) -> Y.Fac | None:
    p = f[1]
    if len(p) == 2 and p[0][0] == () and len(p[1][0]) == 1:
        c, (z,), cz = p[0][1], p[1][0], p[1][1]
        if (
            ((c, cz) == (1, 1) or (c, cz) == (-1, -1))
            and is_m1(ats, z, f[0])
            and Y.dm_den(f[0], lambda k: Y.flv(fl, k)) >= 2
        ):
            return (f[0], Y.ip_c(1))
        return None
    if len(p) != 3 or p[0][0] != () or len(p[1][0]) != 1 or len(p[2][0]) != 1:
        return None
    c, (z,), cz, (w,), cw = p[0][1], p[1][0], p[1][1], p[2][0], p[2][1]
    if (
        ((c, cz, cw) == (1, 1, -1) or (c, cz, cw) == (-1, -1, 1))
        and is_m1(ats, z, f[0])
        and is_dim(ats, w, f[0])
        and Y.dm_den(f[0], lambda k: Y.flv(fl, k)) >= 2
    ):
        return (f[0], Y.ip_c(1))
    return None


def false_at(fl: Sequence[int], t: ATm) -> ATm | None:
    for pre, f, post in Y._splits(t[3]):
        f2 = false_del(fl, t[2], f)
        if f2 is None:
            continue
        i = ids(t[2])
        if wf_a(t[2]) and len(i) == len(set(i)):
            return (t[0], t[1], t[2], (*pre, f2, *post), t[4])
        return None
    return None


def red_arg(t: ATm, pre: Sequence[Atom], a: Atom) -> Atom | None:
    if a[1] != 13 or len(a[3]) != 1 or len(a[4]) != 1:
        return None
    n = a[3][0]
    p, z0 = a[4][0]
    if z0 != ZM:
        return None
    u = next(
        (u for u in ip_vs(p) if is_red(pre, u, n) and (n, ((((), 1), ((u,), 1)))) in t[3]), None
    )
    if u is None:
        return None
    return (a[0], a[1], a[2], a[3], ((Y.ip_subst(u, Y.ip_c(0), p), ZM),))


def red_at(
    fl: Any, pw: Any, t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]
) -> ATm | None:
    a2 = red_arg(t, pre, a)
    if a2 is None:
        return None
    i = ids(t[2])
    if not (wf_a(t[2]) and len(i) == len(set(i))):
        return None
    return (t[0], t[1], (*pre, a2, *post), t[3], t[4])


def eq_del_of(ats: Sequence[Atom], f: Y.Fac) -> tuple[int, int] | None:
    p = f[1]
    if len(p) != 2 or len(p[0][0]) != 1 or len(p[1][0]) != 1:
        return None
    (a,), ca = p[0]
    (b,), cb = p[1]
    d = f[0]
    if not (
        Y.dm_const(d)
        and d[0] != 0
        and ca in (1, -1)
        and Y._emod(ca + cb, d[0]) == 0
        and is_red(ats, a, d)
        and is_red(ats, b, d)
        and a != b
    ):
        return None
    fa, fb = find_at(ats, a), find_at(ats, b)
    assert fa is not None and fb is not None
    return (b, a) if z_lt(at_key(fb), at_key(fa)) else (a, b)


def eq_at(fl: Sequence[int], t: ATm) -> ATm | None:
    for pre, f, post in Y._splits(t[3]):
        o = eq_del_of(t[2], f)
        if o is None:
            continue
        u, w = o
        v = Y.ip_v(u)
        rest = (*pre, *post)
        i = ids(t[2])
        if (
            wf_a(t[2])
            and len(i) == len(set(i))
            and (any(w in Y.fac_vars(g) for g in rest) or any(w in Y.fac_vars(g) for g in t[4]))
        ):
            return (
                t[0],
                t[1],
                t[2],
                (*(Y.fac_sub(w, v, g) for g in pre), f, *(Y.fac_sub(w, v, g) for g in post)),
                tuple(Y.fac_sub(w, v, g) for g in t[4]),
            )
    return None


def p_rule1(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], t: ATm) -> ATm | None:
    for fn in (
        cst_at,
        xor_z_at,
        mod_c_at,
        ddot_swap_at,
        xor_at,
        dedup_a,
        dedup_w,
        dsub_at,
        dot_xor_at,
        m1_at,
        alias_at,
        red_at,
    ):
        for pre, a, post in Y._splits(t[2]):
            r = fn(fl, pw, t, pre, a, post)
            if r is not None:
                return r
    r = eq_at(fl, t)
    if r is not None:
        return r
    return false_at(fl, t)


def p_rules(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], n: int, t: ATm) -> ATm:
    for _ in range(n):
        t2 = p_rule1(fl, pw, t)
        if t2 is None:
            return t
        t = t2
    return t


def pre_a(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], t: ATm) -> ATm:
    t1 = p_rules(fl, pw, len(t[2]) + 1, a_rules(len(t[2]) + 1, t))
    t2 = dz_step(pw, mod_rules(fl, pw, len(t[2]) + 1, t1))
    return a_rules(len(t2[2]) + 1, t2)


def canon_a(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], t: ATm) -> ATm | None:
    t3 = pre_a(fl, pw, t)
    r = canon_f(fl, t3[3], t3[4])
    if r is None:
        return None
    k, ds, ps = r
    return sort_sums(sort_tab(canon_ren((Y.cm_mul(t3[0], k), t3[1], t3[2], ds, ps))))


def norm_a(fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], r: int, t: ATm) -> ATm | None:
    for _ in range(r):
        t2 = canon_a(fl, pw, a_elim_all(pw, len(t[1]) + 1, t))
        if t2 is None:
            return None
        t = t2
    return t


def a_shape(t: ATm) -> ATm:
    c = t[0]
    return ((Fraction(0), *c[1:]), *t[1:])


def a_with_q(t: ATm, q: Fraction) -> ATm:
    c = t[0]
    return ((q, *c[1:]), *t[1:])


def ta_add(t: ATm, lst: tuple[ATm, ...]) -> tuple[ATm, ...]:
    out = list(lst)
    st = a_shape(t)
    for i, u in enumerate(out):
        if a_shape(u) == st:
            q = u[0][0] + t[0][0]
            if q == 0:
                return tuple(out[:i] + out[i + 1 :])
            out[i] = a_with_q(u, q)
            return tuple(out)
    return tuple(out + ([t] if t[0][0] != 0 else []))


def nf_a(
    fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], e: Sequence[ATm]
) -> tuple[ATm, ...]:
    acc: tuple[ATm, ...] = ()
    for t in e:
        n = norm_a(fl, pw, AROUNDS, t)
        if n is not None:
            acc = ta_add(n, acc)
    return acc


def ax_neg(e: Sequence[ATm]) -> list[ATm]:
    return [a_with_q(t, -t[0][0]) for t in e]


# the passes under facts about free variables (``LPass``)

Ctx = tuple[
    tuple[int, ...], tuple[tuple[int, Y.DMon, Y.DMon], ...], tuple[tuple[Y.DMon, Y.DMon], ...]
]


def ctx_vs(c: Ctx) -> list[int]:
    return list(c[0]) + [w[0] for w in c[1]]


def x_one(c: Ctx, b: int, a: Atom) -> tuple[tuple[Atom, ...], Y.IPoly] | None:
    nn, wl = c[0], c[1]
    f, args = a[1], a[4]
    if f == 10 and len(args) == 2 and len(a[3]) == 1 and args[1][1] == ZM:
        (x, m), (p, _) = args
        d = a[3][0]
        for j in nn:
            if p == Y.ip_add(Y.ip_v(j), Y.ip_c(1)) and m[0] != 0 and d[0] != 0:
                jv = (Y.ip_v(j), ZM)
                new = (
                    (b + 1, 7, (), a[3], (jv,)),
                    (b + 2, 9, (), a[3], ((x, m), jv)),
                    (b, 10, (), a[3], ((x, m), jv)),
                )
                return new, Y.ip_add(Y.ip_v(b), Y.ip_mul(Y.ip_v(b + 1), Y.ip_v(b + 2)))
        for v, dd, n in wl:
            if p == Y.ip_v(v) and d == dd and m == n:
                return ((b, 2, (), (), ((x, n),)),), Y.ip_v(b)
    if f == 7 and len(args) == 1 and args[0][1] == ZM:
        p = args[0][0]
        d = a[3][0] if a[3] else TWO
        for j in nn:
            if p == Y.ip_add(Y.ip_v(j), Y.ip_c(1)):
                new0: Atom = (b, 7, (), a[3], ((Y.ip_v(j), ZM),))
                if Y.dm_const(d):
                    return (new0,), Y.ip_smul(d[0], Y.ip_v(b))
                return (new0, (b + 1, 8, (), (d,), ())), Y.ip_mul(Y.ip_v(b + 1), Y.ip_v(b))
        for v, dd, n in wl:
            if p == Y.ip_v(v) and d == dd:
                return ((b, 8, (), (n,), ()),), Y.ip_v(b)
    return None


def max_v(t: ATm) -> int:
    return max(all_v(t), default=0)


def x_at(c: Ctx, t: ATm, pre: tuple[Atom, ...], a: Atom, post: tuple[Atom, ...]) -> ATm | None:
    b = max_v(t) + 1
    r = x_one(c, b, a)
    if r is None:
        return None
    new, p = r
    z = a[0]
    bv, iv = set(abvs(t)), set(ids(t[2]))
    if not (
        all(v not in bv and v not in iv for v in ctx_vs(c))
        and z not in ids(post)
        and wf_a(t[2])
        and plain_p(post, p)
        and not Y.ip_has(z, p)
    ):
        return None
    return (
        t[0],
        t[1],
        pre + new + tuple(at_sub(z, p, x) for x in post),
        tuple(Y.fac_sub(z, p, f) for f in t[3]),
        tuple(Y.fac_sub(z, p, f) for f in t[4]),
    )


def x_ph(c: Ctx, t: ATm) -> ATm | None:
    b = max_v(t) + 1
    for pre, f, post in Y._splits(t[4]):
        w = next((w for w in c[2] if f[0] == w[0] and w[0] != w[1]), None)
        if w is not None:
            z: Atom = (b, 12, (), (w[1], w[0]), ())
            g = (w[1], Y.ip_mul(Y.ip_v(b), f[1]))
            return (t[0], t[1], (z, *t[2]), t[3], (*pre, g, *post))
    return None


def x_del(c: Ctx, t: ATm) -> ATm | None:
    i = ids(t[2])
    if len(i) != len(set(i)):
        return None
    for pre, f, post in Y._splits(t[3]):
        for w in c[2]:
            z = next((b for b in t[2] if b[1] == 12 and b[3] == (w[1], w[0]) and b[4] == ()), None)
            if z is None or f[0] != w[1]:
                continue
            lin = Y.ip_lin(z[0], f[1])
            if lin is None:
                continue
            p2, r = lin
            if r == () and not Y.ip_has(z[0], p2):
                return (t[0], t[1], t[2], (*pre, (w[0], p2), *post), t[4])
    return None


def x_rules(c: Ctx, n: int, t: ATm) -> ATm:
    for _ in range(n):
        t2 = None
        for pre, a, post in Y._splits(t[2]):
            t2 = x_at(c, t, pre, a, post)
            if t2 is not None:
                break
        if t2 is None:
            t2 = x_ph(c, t)
        if t2 is None:
            t2 = x_del(c, t)
        if t2 is None:
            return t
        t = t2
    return t


def is_red(l: Sequence[Atom], u: int, n: Y.DMon) -> bool:
    c = find_at(l, u)
    return c is not None and c[1] == 2 and len(c[4]) == 1 and c[4][0][1] == n


def split_of(t: ATm, pre: tuple[Y.Fac, ...], f: Y.Fac, post: tuple[Y.Fac, ...]) -> list[ATm] | None:
    for z in Y.fac_vars(f):
        b = find_at(t[2], z)
        if b is None or b[1] != 13 or len(b[3]) != 1 or len(b[4]) != 1:
            continue
        n = b[3][0]
        p, zz = b[4][0]
        if not (len(p) == 1 and p[0][1] == 1 and len(p[0][0]) == 1):
            continue
        u = p[0][0][0]
        if not (zz == ZM and is_red(t[2], u, n) and n[0] != 0):
            continue
        lin = Y.ip_lin(z, f[1])
        if lin is None:
            continue
        a, r = lin
        s = Y.ip_const(a)
        if s is None:
            continue
        i = ids(t[2])
        if not (s in (1, -1) and wf_a(t[2]) and len(i) == len(set(i))):
            continue
        du = (f[0], Y.ip_add(Y.ip_smul(s, Y.ip_v(u)), r))
        dc = (n, Y.ip_add(Y.ip_v(u), Y.ip_c(1)))
        c = t[0]
        neg = (-c[0], *c[1:])
        return [
            (c, t[1], t[2], (*pre, du, *post), t[4]),
            (neg, t[1], t[2], (*pre, du, dc, *post), t[4]),
            (c, t[1], t[2], (*pre, (f[0], r), dc, *post), t[4]),
        ]
    return None


def x_pass(c: Ctx, e: Sequence[ATm]) -> list[ATm]:
    out: list[ATm] = []
    for t in (x_rules(c, len(t[2]) + len(t[4]) + len(t[3]) + 1, t) for t in e):
        ts = None
        for pre, f, post in Y._splits(t[3]):
            ts = split_of(t, pre, f, post)
            if ts is not None:
                break
        out += ts if ts is not None else [t]
    return out


def close2(
    fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], c: Ctx, e: Sequence[ATm]
) -> bool:
    r = nf_a(fl, pw, x_pass(c, e))
    return not r or not nf_a(fl, pw, x_pass(c, list(r)))


# real coefficient atoms


def real_c(j: int, m: Y.CMon) -> Y.CMon:
    am = list(m[4])
    c = am[2 * j + 1] if 2 * j + 1 < len(am) else 0
    if 2 * j + 1 < len(am):
        am[2 * j + 1] = 0
    return Y.cm_mul((m[0], m[1], m[2], m[3], tuple(am), m[5]), Y.atom_p(2 * j, c))


def real_t(rs: Sequence[int], t: ATm) -> ATm:
    c = t[0]
    for j in rs:
        c = real_c(j, c)
    return (c, t[1], t[2], t[3], t[4])


# free variables in range


def rg_one(v: int, d: Y.DMon, t: ATm) -> ATm:
    if v not in fvs(t) + arg_vs(t[2]) or v in abvs(t) or v in ids(t[2]):
        return t
    u = max_v(t) + 1
    w = Y.ip_v(u)
    a = (u, 2, (), (), ((Y.ip_v(v), d),))
    return (
        t[0],
        t[1],
        (a, *(at_sub(v, w, b) for b in t[2])),
        tuple(Y.fac_sub(v, w, f) for f in t[3]),
        tuple(Y.fac_sub(v, w, f) for f in t[4]),
    )


def rg_t(rg: Sequence[tuple[int, Y.DMon]], t: ATm) -> ATm:
    for v, d in rg:
        t = rg_one(v, d, t)
    return t
