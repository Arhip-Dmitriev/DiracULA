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

"""The mirror of the normaliser of symbolic sums in ``DiracULA.Sym``, ``SymNorm`` and
``SymCanon``: the functions follow their Lean namesakes on tuples. ``DMon`` is ``(c, e)``,
``IPoly`` a tuple of ``(monomial, coefficient)``, ``CMon`` ``(q, r, sq, rc, am, gc)``, a
factor ``(DMon, IPoly)`` and a term ``(CMon, sums, dels, phs)``.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence
from fractions import Fraction
from typing import Any

import sympy as sp  # type: ignore[import-untyped]  # sympy ships no py.typed marker


class SymUnsupported(Exception):
    """An expression outside the symbolic-sum grammar."""


DMon = tuple[int, tuple[int, ...]]
IPoly = tuple[tuple[tuple[int, ...], int], ...]
Fac = tuple[DMon, IPoly]
CMon = tuple[
    Fraction,
    Fraction,
    tuple[int, ...],
    tuple[int, ...],
    tuple[int, ...],
    tuple[tuple[int, DMon], ...],
]
STm = tuple[CMon, tuple[tuple[int, DMon], ...], tuple[Fac, ...], tuple[Fac, ...]]

OFF = 1000000
ROUNDS = 3


def _emod(a: int, b: int) -> int:
    """Lean's ``Int`` remainder: nonnegative, ``a`` itself for ``b = 0``."""
    return a if b == 0 else a % abs(b)


def _ediv(a: int, b: int) -> int:
    """Lean's ``Int`` division, ``a = b q + r`` with ``0 ≤ r < |b|``."""
    return 0 if b == 0 else (a - _emod(a, b)) // b


# dense vectors


def nadd(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    n = max(len(a), len(b))
    return tuple((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n))


def nsub(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    return tuple(max(0, a[i] - (b[i] if i < len(b) else 0)) for i in range(len(a)))


def nle(a: Sequence[int], b: Sequence[int]) -> bool:
    return all(x <= (b[i] if i < len(b) else 0) for i, x in enumerate(a))


def trim(a: Sequence[int]) -> tuple[int, ...]:
    out = list(a)
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


# dimension monomials


def dm_mul(a: DMon, b: DMon) -> DMon:
    return (a[0] * b[0], trim(nadd(a[1], b[1])))


def dm_dvd(a: DMon, b: DMon) -> bool:
    return a[0] != 0 and b[0] % a[0] == 0 and nle(a[1], b[1])


def dm_div(b: DMon, a: DMon) -> DMon:
    return (b[0] // a[0] if a[0] else 0, trim(nsub(b[1], a[1])))


def dm_const(m: DMon) -> bool:
    return all(x == 0 for x in m[1])


def dm_den(m: DMon, dv: Callable[[int], int]) -> int:
    out = m[0]
    for i, e in enumerate(m[1]):
        out *= dv(i) ** e
    return out


# polynomials


def im_ins(x: int, m: Sequence[int]) -> tuple[int, ...]:
    out = list(m)
    for i, y in enumerate(out):
        if x <= y:
            return tuple(out[:i] + [x] + out[i:])
    return tuple(out + [x])


def im_mul(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    out = tuple(a)
    for x in reversed(b):
        out = im_ins(x, out)
    return out


def ip_ins(m: tuple[int, ...], c: int, p: IPoly) -> IPoly:
    out = list(p)
    for i, (m2, c2) in enumerate(out):
        if m == m2:
            if c + c2 == 0:
                return tuple(out[:i] + out[i + 1 :])
            return tuple(out[:i] + [(m, c + c2)] + out[i + 1 :])
        if m < m2:
            if c == 0:
                return tuple(out)
            return tuple(out[:i] + [(m, c)] + out[i:])
    return tuple(out + ([(m, c)] if c != 0 else []))


def ip_add(p: IPoly, q: IPoly) -> IPoly:
    out = p
    for m, c in reversed(q):
        out = ip_ins(m, c, out)
    return out


def ip_smul(k: int, p: IPoly) -> IPoly:
    return () if k == 0 else tuple((m, k * c) for m, c in p)


def ip_mul(p: IPoly, q: IPoly) -> IPoly:
    acc: IPoly = ()
    for m, c in reversed(p):
        for m2, c2 in reversed(q):
            acc = ip_ins(im_mul(m, m2), c * c2, acc)
    return acc


def ip_c(c: int) -> IPoly:
    return ip_ins((), c, ())


def ip_v(x: int) -> IPoly:
    return (((x,), 1),)


def ip_sub(p: IPoly, q: IPoly) -> IPoly:
    return ip_add(p, ip_smul(-1, q))


def ip_pow(r: IPoly, k: int) -> IPoly:
    out = ip_c(1)
    for _ in range(k):
        out = ip_mul(r, out)
    return out


def ip_subst(x: int, r: IPoly, p: IPoly) -> IPoly:
    if not any(x in m for m, _ in p):
        return p
    acc: IPoly = ()
    for m, c in reversed(p):
        rest = tuple(y for y in m if y != x)
        acc = ip_add(acc, ip_mul(ip_smul(c, ((rest, 1),)), ip_pow(r, m.count(x))))
    return acc


def ip_has(x: int, p: IPoly) -> bool:
    return any(x in m for m, _ in p)


def ip_lin(x: int, p: IPoly) -> tuple[IPoly, IPoly] | None:
    if not all(m.count(x) <= 1 for m, _ in p):
        return None
    a: IPoly = ()
    b: IPoly = ()
    for m, c in reversed(p):
        if x in m:
            mm = list(m)
            mm.remove(x)
            a = ip_ins(tuple(mm), c, a)
        else:
            b = ip_ins(m, c, b)
    return a, b


def ip_const(p: IPoly) -> int | None:
    if not p:
        return 0
    if len(p) == 1 and p[0][0] == ():
        return p[0][1]
    return None


def ip_modc(k: int, p: IPoly) -> IPoly:
    acc: IPoly = ()
    for m, c in reversed(p):
        acc = ip_ins(m, _emod(c, k), acc)
    return acc


def ip_divby(k: int, p: IPoly) -> bool:
    return all(_emod(c, k) == 0 for _, c in p)


def ip_divc(k: int, p: IPoly) -> IPoly:
    acc: IPoly = ()
    for m, c in reversed(p):
        acc = ip_ins(m, _ediv(c, k), acc)
    return acc


def ip_sign(p: IPoly) -> IPoly:
    if p and p[0][1] < 0:
        return ip_smul(-1, p)
    return p


def ip_vars(p: IPoly) -> list[int]:
    return [x for m, _ in p for x in m]


# coefficient monomials


def rnorm(q: Fraction, r: Fraction) -> tuple[Fraction, Fraction]:
    r2 = r - math.floor(r)
    if Fraction(1, 2) <= r2:
        return -q, r2 - Fraction(1, 2)
    return q, r2


def rc_ins(c: int, lst: tuple[int, ...]) -> tuple[int, tuple[int, ...]]:
    out = list(lst)
    for i, x in enumerate(out):
        if c == x:
            return c, tuple(out[:i] + out[i + 1 :])
        if c < x:
            return 1, tuple(out[:i] + [c] + out[i:])
    return 1, tuple(out + [c])


def rc_mul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, tuple[int, ...]]:
    f, lst = 1, a
    for c in reversed(b):
        g, lst = rc_ins(c, lst)
        f = g * f
    return f, lst


def gc_key(g: tuple[int, DMon]) -> tuple[int, int, tuple[int, ...]]:
    return (g[0], g[1][0], g[1][1])


def gc_ins(g: tuple[int, DMon], lst: tuple[tuple[int, DMon], ...]) -> tuple[tuple[int, DMon], ...]:
    out = list(lst)
    for i, h in enumerate(out):
        if not gc_key(h) < gc_key(g):
            return tuple(out[:i] + [g] + out[i:])
    return tuple(out + [g])


def cm_mul(a: CMon, b: CMon) -> CMon:
    q, r = rnorm(a[0] * b[0], a[1] + b[1])
    f, rc = rc_mul(a[3], b[3])
    gc = a[5]
    for g in reversed(b[5]):
        gc = gc_ins(g, gc)
    return (q * f, r, trim(nadd(a[2], b[2])), rc, trim(nadd(a[4], b[4])), gc)


def of_q(q: Fraction | int) -> CMon:
    return (Fraction(q), Fraction(0), (), (), (), ())


def _isqrt_exact(c: int) -> bool:
    s = math.isqrt(c)
    return s * s == c


def rt_c(c: int, k: int) -> CMon:
    half = _ediv(k, 2)
    if _emod(k, 2) == 0:
        return of_q(Fraction(c) ** half)
    if _isqrt_exact(c):
        return of_q(Fraction(c) ** half * math.isqrt(c))
    return (Fraction(c) ** half, Fraction(0), (), (c,), (), ())


def rt_d(d: DMon, k: int) -> CMon:
    m = rt_c(d[0], k)
    return (m[0], m[1], trim(tuple(k * x for x in d[1])), m[3], m[4], m[5])


def gcd_a(a: int, d: DMon) -> CMon:
    if dm_const(d) or abs(a) == 1:
        return of_q(math.gcd(abs(a), d[0]))
    return (Fraction(1), Fraction(0), (), (), (), ((abs(a), d),))


def ex_q(r: Fraction) -> CMon:
    q, r2 = rnorm(Fraction(1), r)
    return (q, r2, (), (), (), ())


def atom_p(j: int, k: int) -> CMon:
    return (Fraction(1), Fraction(0), (), (), trim((0,) * j + (k,)), ())


# terms


def fac_vars(f: Fac) -> list[int]:
    return ip_vars(f[1])


def tm_vars(t: STm) -> list[int]:
    return [x for f in (*t[2], *t[3]) for x in fac_vars(f)]


def bvs(t: STm) -> list[int]:
    return [x for x, _ in t[1]]


def tm_mul(s: STm, t: STm) -> STm:
    return (cm_mul(s[0], t[0]), s[1] + t[1], s[2] + t[2], s[3] + t[3])


def mul_ok(s: STm, t: STm) -> bool:
    vt, vs = set(tm_vars(t)), set(tm_vars(s))
    return all(x not in vt for x in bvs(s)) and all(x not in vs for x in bvs(t))


def fac_has(x: int, f: Fac) -> bool:
    return ip_has(x, f[1])


def fac_sub(x: int, v: IPoly, f: Fac) -> Fac:
    return (f[0], ip_subst(x, v, f[1]))


def pin_val(s: int, b: IPoly) -> IPoly:
    return ip_smul(-s, b)


def _splits(lst: Sequence[Any]) -> list[tuple[tuple[Any, ...], Any, tuple[Any, ...]]]:
    return [(tuple(lst[:i]), lst[i], tuple(lst[i + 1 :])) for i in range(len(lst))]


# eliminations


def elim_unused(
    x: int, d: DMon, ds: tuple[Fac, ...], ps: tuple[Fac, ...]
) -> tuple[CMon, tuple[Fac, ...], tuple[Fac, ...]] | None:
    if d[0] != 0 and all(not fac_has(x, f) for f in (*ds, *ps)):
        return rt_d(d, 2), ds, ps
    return None


def elim_delta1(
    x: int, d: DMon, pre: tuple[Fac, ...], f: Fac, post: tuple[Fac, ...], ps: tuple[Fac, ...]
) -> tuple[CMon, tuple[Fac, ...], tuple[Fac, ...]] | None:
    lin = ip_lin(x, f[1])
    if lin is None:
        return None
    a, b = lin
    s = ip_const(a)
    if s is None:
        return None
    if (
        (s in (1, -1))
        and d[0] != 0
        and dm_dvd(f[0], d)
        and all(not fac_has(x, g) or dm_dvd(g[0], f[0]) for g in (*pre, *post, *ps))
    ):
        v = pin_val(s, b)
        return (
            rt_d(dm_div(d, f[0]), 2),
            tuple(fac_sub(x, v, g) for g in (*pre, *post)),
            tuple(fac_sub(x, v, g) for g in ps),
        )
    return None


def elim_delta(x: int, d: DMon, ds: tuple[Fac, ...], ps: tuple[Fac, ...]) -> Any:
    for pre, f, post in _splits(ds):
        e = elim_delta1(x, d, pre, f, post, ps)
        if e is not None:
            return e
    return None


def char_data(x: int, d: DMon, lst: tuple[Fac, ...]) -> tuple[IPoly, IPoly] | None:
    if not lst:
        return (), ()
    rest = char_data(x, d, lst[1:])
    if rest is None:
        return None
    big_a, big_b = rest
    f = lst[0]
    if fac_has(x, f):
        if f[0] == d:
            lin = ip_lin(x, f[1])
            if lin is None:
                return None
            return ip_add(big_a, lin[0]), ip_add(big_b, lin[1])
        return None
    return big_a, big_b


def elim_char(x: int, d: DMon, ds: tuple[Fac, ...], ps: tuple[Fac, ...]) -> Any:
    if d[0] != 0 and all(not fac_has(x, f) for f in ds):
        cd = char_data(x, d, ps)
        if cd is not None:
            big_a, big_b = cd
            return (
                rt_d(d, 2),
                ds + ((d, big_a),),
                tuple(f for f in ps if not fac_has(x, f)) + ((d, big_b),),
            )
    return None


def elim_gcd1(
    x: int, d: DMon, pre: tuple[Fac, ...], f: Fac, post: tuple[Fac, ...], ps: tuple[Fac, ...]
) -> Any:
    if f[0] == d and d[0] != 0 and all(not fac_has(x, g) for g in (*pre, *post, *ps)):
        lin = ip_lin(x, f[1])
        if lin is None:
            return None
        a, b = lin
        alpha = ip_const(a)
        if alpha is None:
            return None
        if ip_divby(alpha, b):
            return gcd_a(alpha, d), pre + post, ps
    return None


def elim_gcd(x: int, d: DMon, ds: tuple[Fac, ...], ps: tuple[Fac, ...]) -> Any:
    for pre, f, post in _splits(ds):
        e = elim_gcd1(x, d, pre, f, post, ps)
        if e is not None:
            return e
    return None


def elim_var(x: int, d: DMon, ds: tuple[Fac, ...], ps: tuple[Fac, ...]) -> Any:
    for fn in (elim_unused, elim_delta, elim_char, elim_gcd):
        e = fn(x, d, ds, ps)
        if e is not None:
            return e
    return None


def elim_step(t: STm) -> STm | None:
    for pre, (x, d), post in _splits(t[1]):
        if x in [y for y, _ in (*pre, *post)]:
            continue
        e = elim_var(x, d, t[2], t[3])
        if e is not None:
            return (cm_mul(t[0], e[0]), pre + post, e[1], e[2])
    return None


def elim_all(n: int, t: STm) -> STm:
    for _ in range(n):
        t2 = elim_step(t)
        if t2 is None:
            return t
        t = t2
    return t


# canonical forms


def _pick(p: IPoly, ok: Callable[[int], bool]) -> tuple[int, int, IPoly] | None:
    acc: tuple[int, int, IPoly] | None = None
    for x in ip_vars(p):
        lin = ip_lin(x, p)
        if lin is None:
            continue
        c = ip_const(lin[0])
        if c is None or not ok(c):
            continue
        if acc is None or acc[0] < x:
            acc = (x, c, lin[1])
    return acc


def pivot_of(p: IPoly) -> tuple[int, int, IPoly] | None:
    return _pick(p, lambda c: c in (1, -1))


def div_of(p: IPoly) -> tuple[int, int, IPoly] | None:
    return _pick(p, lambda c: c != 0)


def piv_sub(m: DMon, x: int, v: IPoly, g: Fac) -> Fac:
    return fac_sub(x, v, g) if dm_dvd(g[0], m) else g


def div_sub(m: DMon, x: int, c: int, b: IPoly, g: Fac) -> Fac:
    if not dm_dvd(g[0], m):
        return g
    lin = ip_lin(x, g[1])
    if lin is None:
        return g
    ag, bg = lin
    if ip_divby(c, ag):
        return (g[0], ip_sub(bg, ip_mul(ip_divc(c, ag), b)))
    return g


def step_of(f: Fac) -> Callable[[Fac], Fac] | None:
    q = pivot_of(f[1])
    if q is not None:
        v = pin_val(q[1], q[2])
        return lambda g: piv_sub(f[0], q[0], v, g)
    q2 = div_of(f[1])
    if q2 is not None:
        return lambda g: div_sub(f[0], q2[0], q2[1], q2[2], g)
    return None


def piv_pass(
    n: int, a: tuple[Fac, ...], b: tuple[Fac, ...], ps: tuple[Fac, ...]
) -> tuple[tuple[Fac, ...], tuple[Fac, ...]]:
    while True:
        if n == 0:
            return a + b, ps
        if not b:
            return a, ps
        n -= 1
        f, b = b[0], b[1:]
        st = step_of(f)
        if st is None:
            a = a + (f,)
        else:
            a = tuple(st(g) for g in a) + (f,)
            b = tuple(st(g) for g in b)
            ps = tuple(st(g) for g in ps)


def flv(fl: Sequence[int], i: int) -> int:
    return fl[i] if i < len(fl) else 0


def sym_mod(c: int, k: int) -> int:
    r = _emod(c, k)
    return r - k if 2 * r > k else r


def ip_mods(k: int, p: IPoly) -> IPoly:
    acc: IPoly = ()
    for m, c in reversed(p):
        acc = ip_ins(m, sym_mod(c, k), acc)
    return acc


def del_poly(f: Fac) -> IPoly:
    return ip_sign(ip_mods(f[0][0], f[1])) if dm_const(f[0]) else ip_sign(f[1])


_ZERO = object()


def norm_del(fl: Sequence[int], f: Fac) -> Any:
    """``None`` when the delta vanishes, ``()`` when it is one, else the factor."""
    p = del_poly(f)
    c = ip_const(p)
    if c is not None:
        if c == 0:
            return ()
        if dm_const(f[0]):
            return () if _emod(c, f[0][0]) == 0 else None
        if abs(c) < dm_den(f[0], lambda i: flv(fl, i)):
            return None
        return (f[0], p)
    return (f[0], p)


def norm_dels(fl: Sequence[int], lst: tuple[Fac, ...]) -> tuple[Fac, ...] | None:
    out = []
    for f in lst:
        r = norm_del(fl, f)
        if r is None:
            return None
        if r != ():
            out.append(r)
    return tuple(out)


def norm_ph(f: Fac) -> tuple[CMon, Fac | None]:
    if dm_const(f[0]) and f[0][0] != 0:
        p = ip_modc(f[0][0], f[1])
        c = ip_const(p)
        if c is not None:
            return ex_q(Fraction(c, f[0][0])), None
        return of_q(1), (f[0], p)
    if not f[1]:
        return of_q(1), None
    return of_q(1), f


def norm_phs(lst: tuple[Fac, ...]) -> tuple[CMon, tuple[Fac, ...]]:
    if not lst:
        return of_q(1), ()
    k, rest = norm_phs(lst[1:])
    k1, g = norm_ph(lst[0])
    return cm_mul(k1, k), (rest if g is None else (g,) + rest)


def ph_ins(f: Fac, lst: tuple[Fac, ...]) -> tuple[Fac, ...]:
    out = list(lst)
    for i, g in enumerate(out):
        if g[0] == f[0]:
            out[i] = (g[0], ip_add(g[1], f[1]))
            return tuple(out)
    return tuple(out + [f])


def ph_merge(ps: tuple[Fac, ...]) -> tuple[Fac, ...]:
    acc: tuple[Fac, ...] = ()
    for f in ps:
        acc = ph_ins(f, acc)
    return acc


def _fkey(f: Fac) -> tuple[Any, ...]:
    return (f[0][0], f[0][1], f[1])


def fac_ins(f: Fac, lst: tuple[Fac, ...]) -> tuple[Fac, ...]:
    out = list(lst)
    for i, g in enumerate(out):
        if not _fkey(g) < _fkey(f):
            return tuple(out[:i] + [f] + out[i:])
    return tuple(out + [f])


def del_ins(f: Fac, lst: tuple[Fac, ...]) -> tuple[Fac, ...]:
    out = list(lst)
    for i, g in enumerate(out):
        if g == f:
            return tuple(out)
        if not _fkey(g) < _fkey(f):
            return tuple(out[:i] + [f] + out[i:])
    return tuple(out + [f])


RBASE = 2000000


def ren_one(t: STm, x: int, y: int) -> STm | None:
    b = bvs(t)
    if b.count(x) == 1 and y not in b and y not in tm_vars(t):
        v = ip_v(y)
        return (
            t[0],
            tuple((y, p[1]) if p[0] == x else p for p in t[1]),
            tuple(fac_sub(x, v, f) for f in t[2]),
            tuple(fac_sub(x, v, f) for f in t[3]),
        )
    return None


def ren_list(t: STm, k: int, xs: Sequence[int]) -> STm:
    for x in xs:
        r = ren_one(t, x, RBASE + k)
        t = t if r is None else r
        k += 1
    return t


def canon_tm(fl: Sequence[int], t: STm) -> STm | None:
    t = ren_list(t, 0, bvs(t))
    ds0, ps0 = piv_pass(len(t[2]), (), t[2], t[3])
    ds = norm_dels(fl, ds0)
    if ds is None:
        return None
    k, ps = norm_phs(ph_merge(ps0))
    dsort: tuple[Fac, ...] = ()
    for f in reversed(ds):
        dsort = del_ins(f, dsort)
    psort: tuple[Fac, ...] = ()
    for f in reversed(ps):
        psort = fac_ins(f, psort)
    return (cm_mul(t[0], k), t[1], dsort, psort)


def norm_tm(fl: Sequence[int], r: int, t: STm) -> STm | None:
    for _ in range(r):
        t2 = canon_tm(fl, elim_all(len(t[1]) + 1, t))
        if t2 is None:
            return None
        t = t2
    return t


def shape(t: STm) -> STm:
    c = t[0]
    return ((Fraction(0), c[1], c[2], c[3], c[4], c[5]), t[1], t[2], t[3])


def with_q(t: STm, q: Fraction) -> STm:
    c = t[0]
    return ((q, c[1], c[2], c[3], c[4], c[5]), t[1], t[2], t[3])


def tm_add(t: STm, lst: tuple[STm, ...]) -> tuple[STm, ...]:
    out = list(lst)
    st = shape(t)
    for i, u in enumerate(out):
        if shape(u) == st:
            q = u[0][0] + t[0][0]
            if q == 0:
                return tuple(out[:i] + out[i + 1 :])
            out[i] = with_q(u, q)
            return tuple(out)
    return tuple(out + ([t] if t[0][0] != 0 else []))


def nf_ex(fl: Sequence[int], e: Sequence[STm]) -> tuple[STm, ...]:
    acc: tuple[STm, ...] = ()
    for t in e:
        n = norm_tm(fl, ROUNDS, t)
        if n is not None:
            acc = tm_add(n, acc)
    return acc


# networks


def sum_l(ls: Sequence[int]) -> IPoly:
    acc: IPoly = ()
    for x in reversed(ls):
        acc = ip_add(acc, ip_v(x))
    return acc


def _dmon(e: sp.Expr, syms: Sequence[sp.Symbol]) -> DMon:
    """A dimension expression as ``c Π d_i^e_i``."""
    e = sp.expand(sp.sympify(e))
    if e.has(sp.pi):
        raise SymUnsupported("a phase that is not a rational number of turns (a real angle)")
    c, rest = e.as_coeff_Mul()
    if not c.is_Integer or int(c) <= 0:
        raise SymUnsupported(f"the dimension {e} is not a monomial")
    exps = [0] * len(syms)
    for f in sp.Mul.make_args(rest):
        if f == 1:
            continue
        if f in syms:
            exps[syms.index(f)] += 1
            continue
        base, k = f.as_base_exp()
        if base not in syms or not k.is_Integer or int(k) < 0:
            raise SymUnsupported(f"the dimension {e} is not a monomial")
        exps[syms.index(base)] += int(k)
    return (int(c), trim(exps))
