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

"""Lean 4 certificates for results of the .ula language, by translation validation over the
verified normaliser of symbolic sums with integer atoms (``DiracULA.LCanon``).

The left side of a certificate is the program's structure (``DiracULA.Lang.Prog``), built
from the syntax trees the interpreter keeps: every gate instance, literal state and identity
is a leaf expression; applications, tensor products, scalar products, sums, inner products,
conjugates and loops are ``Prog`` nodes whose meaning ``Prog.sem`` is a sum or product over
ℂ. The right side is the printed value, as an expression. ``certify_lit`` proves the two equal
when the kernel normalises their difference to nothing (``decide +kernel``), for every value
of the dimension symbols, parameters, functions and output registers.

Variables: output register ``i`` is ``i``, input register ``i`` of a gate is ``IN + i``,
parameter ``k`` is ``PAR + k``, summation indices start at ``BV`` and atoms at ``AID``.

The functions under "the mirror" follow their Lean namesakes in ``DiracULA.Lang`` on the
tuples of :mod:`diracula.lean_lsym`, so that :func:`cert_check` predicts
``certCheck``.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, cast

import sympy  # type: ignore[import-untyped]  # sympy ships no py.typed marker

from diracula import lean_lsym as Z
from diracula import lean_sym as Y
from diracula.lean_lsym import ATm, Atom
from diracula.pathsum import State

IN = 1000
PAR = 2000
BV = 10000


class CertifyError(Exception):
    """A result that cannot be certified; the message names what lies outside the fragment."""


# the mirror


def ax_ren(m: Callable[[int], int], e: Sequence[ATm]) -> list[ATm]:
    return [Z.t_ren(m, t) for t in e]


def ren_oka(m: Callable[[int], int], e: Sequence[ATm]) -> bool:
    return all(Z.inj_on(m, Z.all_v(t)) for t in e)


def ax_sums(s: Sequence[tuple[int, Y.DMon]], e: Sequence[ATm]) -> list[ATm]:
    return [(t[0], tuple(s) + t[1], t[2], t[3], t[4], t[5]) for t in e]


def max_var(e: Sequence[ATm]) -> int:
    return max([0, *(x for t in e for x in Z.all_v(t))])


def fresh(a: Sequence[ATm], b: Sequence[ATm]) -> int:
    return max(3 * IN, max(max_var(a), max_var(b)) + 1)


def t_apart(base: int, t: ATm) -> ATm:
    bl = Z.abvs(t)
    al = [v for v in Z.ids(t[2]) if v not in bl]

    def m(v: int) -> int:
        if v in bl:
            return base + bl.index(v)
        if v in al:
            return base + len(bl) + al.index(v)
        return v

    if Z.inj_on(m, Z.all_v(t)) and Z.wf_a(t[2]) and all(v not in Z.ids(t[2]) for v in Z.aps_vs(t)):
        return Z.t_ren(m, t)
    return t


def apart(base: int, e: Sequence[ATm]) -> list[ATm]:
    return [t_apart(base, t) for t in e]


def in_map(t0: int, k: int) -> Callable[[int], int]:
    return lambda v: t0 + (v - IN) if IN <= v < IN + k else v


def out_map(t0: int, k: int) -> Callable[[int], int]:
    return lambda v: t0 + v if v < k else v


def shift_n(k: int) -> Callable[[int], int]:
    return lambda v: v + k if v < 2 * IN else v


def to_in(k: int) -> Callable[[int], int]:
    return lambda v: IN + v if v < k else v


def avoids(t0: int, k: int, e: Sequence[ATm]) -> bool:
    return all(not (t0 <= v < t0 + k) for v in Z.ax_vs(e))


def blk(t0: int, levels: Sequence[Y.DMon]) -> list[tuple[int, Y.DMon]]:
    return [(t0 + i, d) for i, d in enumerate(levels)]


def app_sym(levels: Sequence[Y.DMon], a: Sequence[ATm], b: Sequence[ATm]) -> list[ATm] | None:
    t0, k = fresh(a, b), len(levels)
    a2, b2 = ax_ren(in_map(t0, k), a), ax_ren(out_map(t0, k), b)
    if (
        k < IN
        and 3 * IN <= t0
        and avoids(t0, k, a)
        and avoids(t0, k, b)
        and ren_oka(in_map(t0, k), a)
        and ren_oka(out_map(t0, k), b)
        and Z.ax_mul_ok(a2, b2)
    ):
        return ax_sums(blk(t0, levels), Z.ax_mul(a2, b2))
    return None


def ten_sym(k: int, a: Sequence[ATm], b: Sequence[ATm]) -> list[ATm] | None:
    b2 = ax_ren(shift_n(k), b)
    if ren_oka(shift_n(k), b) and Z.ax_mul_ok(a, b2):
        return Z.ax_mul(a, b2)
    return None


def pswap(l: Sequence[int]) -> tuple[int, ...]:
    """``pswap``."""
    out: list[int] = []
    for k in range(0, len(l), 2):
        out += [l[k + 1], l[k]] if k + 1 < len(l) else [0, l[k]]
    return tuple(out)


def c_conj(c: Y.CMon) -> Y.CMon:
    q, r = Y.rnorm(c[0], -c[1])
    return (q, r, c[2], c[3], pswap(c[4]), c[5])


def a_swap(k: int) -> int:
    return k + 1 if k % 2 == 0 else k - 1


def t_conj(t: ATm) -> ATm:
    return (
        c_conj(t[0]),
        t[1],
        t[2],
        t[3],
        tuple((f[0], Y.ip_smul(-1, f[1])) for f in t[4]),
        tuple((a_swap(a[0]), a[1], a[2]) for a in t[5]),
    )


def inn_sym(levels: Sequence[Y.DMon], a: Sequence[ATm], b: Sequence[ATm]) -> list[ATm] | None:
    k = len(levels)
    ca = [t_conj(t) for t in a]
    if ren_oka(to_in(k), ca) and avoids(IN, k, a):
        return app_sym(levels, ax_ren(to_in(k), ca), b)
    return None


def t_sub(x: int, v: Y.IPoly, t: ATm) -> ATm:
    return (
        t[0],
        t[1],
        tuple(Z.at_sub(x, v, a) for a in t[2]),
        tuple(Y.fac_sub(x, v, f) for f in t[3]),
        tuple(Y.fac_sub(x, v, f) for f in t[4]),
        tuple(
            a
            for a in ((b[0], Y.ip_subst(x, v, b[1]), ()) if not b[2] else b for b in t[5])
            if a[2] or a[1] or not Z.ap_merge(a[0])
        ),
    )


def tab_vs(l: Sequence[Z.APw]) -> list[int]:
    """``tabVs``."""
    return [x for a in l if a[2] for x in Z.ap_vs(a)]


def sub_ok(x: int, v: Y.IPoly, t: ATm) -> bool:
    b = Z.abvs(t)
    return (
        x not in b
        and x not in Z.ids(t[2])
        and Z.plain_p(t[2], v)
        and all(y not in b for y in Z.ip_vs(v))
        and x not in tab_vs(t[5])
    )


def loop_chk(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    levels: Sequence[Y.DMon],
    j: int,
    lo: int,
    s: Sequence[ATm],
    i0: Sequence[ATm],
    inv: Sequence[ATm],
    k0: Sequence[tuple[ATm, int, int]] = (),
    k1: Sequence[tuple[ATm, int, int]] = (),
) -> bool:
    v0 = Y.ip_c(lo)
    v1 = Y.ip_add(Y.ip_v(j), Y.ip_c(1))
    if not (
        2 * IN <= j and all(sub_ok(j, v0, t) for t in inv) and all(sub_ok(j, v1, t) for t in inv)
    ):
        return False
    c0: Z.Ctx = ((), (), ())
    if not (Z.rel_ok(fl, k0) and Z.rel_ok(fl, k1)):
        return False
    if not Z.close2(fl, pw, c0, list(i0) + Z.ax_neg([t_sub(j, v0, t) for t in inv]) + Z.rel_x(k0)):
        return False
    e1 = app_sym(levels, apart(fresh(s, inv), s), inv)
    return e1 is not None and Z.close2(
        fl, pw, c0, e1 + Z.ax_neg(j_pass(lo, j, [t_sub(j, v1, t) for t in inv])) + Z.rel_x(k1)
    )


def j_pass(lo: int, j: int, e: Sequence[ATm]) -> list[ATm]:
    """``jPass``."""
    return Z.x_pass(((j,), (), ()), e) if 0 <= lo else list(e)


def _laurent(t: ATm) -> tuple[Any, dict[tuple[str, int], int], sympy.Expr] | None:
    """A term as ``(shape, monomial exponents, coefficient)``: the shape without its coefficient
    and the constant parts of its built-in powers; ``None`` for a coefficient other than rational,
    ``i`` and powers of square roots of dimensions, atoms and built-in powers."""
    q, r, sq, rc, am, gc = t[0]
    if rc or gc or r not in (0, Fraction(1, 4)):
        return None
    ex: dict[tuple[str, int], int] = {}
    for i, k in enumerate(sq):
        if k:
            ex[("w", i)] = k
    for j, k in enumerate(am):
        if k:
            ex[("a", j)] = k
    rest: list[Any] = []
    for a in t[5]:
        if a[0] >= GB and not a[2]:
            c = Y.ip_const(tuple(m for m in a[1] if not m[0])) or 0
            if c:
                ex[("g", a[0])] = c
            var = tuple(m for m in a[1] if m[0])
            if var:
                rest.append((a[0], var))
        else:
            rest.append(a)
    coef = sympy.Rational(q.numerator, q.denominator) * (sympy.I if r else 1)
    return (t[1], t[2], t[3], t[4], tuple(rest)), ex, coef


def rel_cofactors(
    fl: Sequence[int], pw: Sequence[tuple[Y.DMon, Y.DMon]], e: Sequence[ATm]
) -> list[tuple[ATm, int, int]] | None:
    """Cofactors ``(p, r, i)`` with ``e + relX`` normalising to zero: the residue of ``e``,
    grouped by shape, solved as a combination of the relations ``r`` of dimension ``i`` by
    linear algebra over cofactor monomials in a growing box."""
    import itertools

    from sympy.polys.domains import QQ_I  # type: ignore[import-untyped]
    from sympy.polys.matrices import DomainMatrix  # type: ignore[import-untyped]

    res = Z.nf_a(fl, pw, Z.x_pass(((), (), ()), e))
    if not res:
        return []
    groups: dict[Any, list[tuple[dict[tuple[str, int], int], sympy.Expr]]] = {}
    for t in res:
        lt = _laurent(t)
        if lt is None:
            return None
        groups.setdefault(lt[0], []).append((lt[1], lt[2]))
    dims = sorted(
        {(a[0] - GB) // 4 for sh in groups for a in sh[4] if len(a) == 2}
        | {(k[1] - GB) // 4 for g in groups.values() for ex, _ in g for k in ex if k[0] == "g"}
    )
    rels: list[tuple[int, int, list[tuple[dict[tuple[str, int], int], sympy.Expr]]]] = []
    for i in dims:
        u, w, qv = ("g", GB + 4 * i), ("w", i), ("g", GB + 4 * i + 2)
        rels.append(
            (
                0,
                i,
                [
                    ({w: 1, u: 1}, sympy.Integer(1)),
                    ({w: 1, u: -1}, sympy.Integer(-1)),
                    ({}, -2 * sympy.I),
                ],
            )
        )
        rels.append(
            (
                1,
                i,
                [
                    ({qv: 1, u: 1}, sympy.Integer(1)),
                    ({qv: 1, u: -1}, sympy.Integer(1)),
                    ({}, sympy.Integer(-1)),
                ],
            )
        )
    out: list[tuple[ATm, int, int]] = []
    for shape, mons in groups.items():
        keys = sorted(
            {k for ex, _ in mons for k in ex} | {k for _, _, rm in rels for ex, _ in rm for k in ex}
        )
        lo = {k: min([ex.get(k, 0) for ex, _ in mons] + [0]) for k in keys}
        hi = {k: max([ex.get(k, 0) for ex, _ in mons] + [0]) for k in keys}
        sol = None
        for pad in range(1, 4):
            box = [
                dict(zip(keys, v, strict=True))
                for v in itertools.product(*[range(lo[k] - pad, hi[k] + pad + 1) for k in keys])
            ]
            unknowns = [(ri, m) for ri in range(len(rels)) for m in box]

            def key(
                ex: dict[tuple[str, int], int], keys: list[tuple[str, int]] = keys
            ) -> tuple[int, ...]:
                return tuple(ex.get(k, 0) for k in keys)

            rows: dict[tuple[int, ...], int] = {}
            entries: dict[tuple[int, int], Any] = {}
            for col, (ri, m) in enumerate(unknowns):
                for ex, c in rels[ri][2]:
                    prod = {k: m.get(k, 0) + ex.get(k, 0) for k in keys}
                    row = rows.setdefault(key(prod), len(rows))
                    entries[(row, col)] = entries.get((row, col), 0) + c
            rhs: dict[int, Any] = {}
            for ex, c in mons:
                full = {k: ex.get(k, 0) for k in keys}
                row = rows.setdefault(key(full), len(rows))
                rhs[row] = rhs.get(row, 0) - c
            nr, nc = len(rows), len(unknowns)
            mat = [
                [QQ_I.from_sympy(sympy.sympify(entries.get((r_, c_), 0))) for c_ in range(nc)]
                + [QQ_I.from_sympy(sympy.sympify(rhs.get(r_, 0)))]
                for r_ in range(nr)
            ]
            dm = DomainMatrix(mat, (nr, nc + 1), QQ_I)
            red, piv = dm.rref()
            if nc in piv:
                continue
            rr = red.to_Matrix()
            vals = [sympy.Integer(0)] * nc
            for row_i, col in enumerate(piv):
                vals[col] = rr[row_i, nc]
            sol = [(unknowns[c_], vals[c_]) for c_ in range(nc) if vals[c_] != 0]
            break
        if sol is None:
            return None
        sums, ats, dels, phs, rest = shape
        for (ri, m), v in sol:
            r_, i_, _ = rels[ri]
            for part, ph in ((sympy.re(v), Fraction(0)), (sympy.im(v), Fraction(1, 4))):
                if part == 0:
                    continue
                qf = Fraction(int(sympy.fraction(part)[0]), int(sympy.fraction(part)[1]))
                sq = Y.trim(
                    tuple(
                        m.get(("w", i), 0)
                        for i in range(1 + max([k[1] for k in keys if k[0] == "w"] + [-1]))
                    )
                )
                am = Y.trim(
                    tuple(
                        m.get(("a", j), 0)
                        for j in range(1 + max([k[1] for k in keys if k[0] == "a"] + [-1]))
                    )
                )
                cm: Y.CMon = (qf, ph, sq, (), am, ())
                aps: tuple[Z.APw, ...] = tuple(a for a in rest if len(a) == 3)
                gs = {a[0]: a[1] for a in rest if len(a) == 2}
                for k in keys:
                    if k[0] == "g" and m.get(k, 0):
                        gs[k[1]] = Y.ip_add(gs.get(k[1], ()), Y.ip_c(m[k]))
                for k2 in sorted(gs):
                    poly = Y.ip_add((), gs[k2])
                    if poly:
                        aps = (*aps, (k2, poly, ()))
                out.append(((cm, sums, ats, dels, phs, aps), r_, i_))
    return out


@dataclass(frozen=True, eq=False)
class Prog:
    """``Prog``: ``kind`` is leaf, app, ten, mul, add, inn, cnj, loop, sum, ren or sub;
    ``name`` is the Lean definition a named node is written as."""

    kind: str
    args: tuple[Any, ...]
    name: str | None = None


def rmap(pairs: Sequence[tuple[int, int]]) -> Callable[[int], int]:
    """``rmap``: the first ``w`` with ``(v, w)`` in ``pairs``, else ``v``."""

    def m(v: int) -> int:
        return next((w for u, w in pairs if u == v), v)

    return m


LOW = 2800
ANALYTIC = ("exp", "sqrt", "cos", "sin", "tan", "log")
"""The scalar functions applied to operators."""


def p_tidy(e: sympy.Expr) -> sympy.Expr:
    """``e`` simplified and tidied by the engine."""
    from diracula import pathsum as P

    return P.tidy(sympy.simplify(sympy.sympify(e)))


"""The first variable of a trace's summed register values."""


def cm_inverse(c: Y.CMon) -> Y.CMon | None:
    """``1/c`` of a coefficient without gcd factors: ``1/sqrt(x) = sqrt(x)/x``."""
    q, r, sq, rc, am, gc = c
    if gc or q == 0:
        return None
    den = Fraction(1)
    for x in rc:
        den *= x
    return (1 / (q * den), (-r) % 1, tuple(-x for x in sq), tuple(rc), tuple(-a for a in am), ())


def _op_label(node: object) -> str:
    """The name of an operator tree, or A."""
    return getattr(node, "id", "A")


def swap_io(k: int) -> tuple[tuple[int, int], ...]:
    """Output register ``i`` and input register ``i`` exchanged, for ``i < k``."""
    return tuple((i, IN + i) for i in range(k)) + tuple((IN + i, i) for i in range(k))


def counts(p: Prog) -> list[Y.IPoly]:
    """``Prog.counts``."""
    if p.kind == "leaf":
        return []
    if p.kind == "loop":
        return [p.args[3], *counts(p.args[4]), *counts(p.args[5])]
    return [c for q in p.args if isinstance(q, Prog) for c in counts(q)]


def prog_sym(
    p: Prog, fl: Sequence[int] = (), pw: Sequence[tuple[Y.DMon, Y.DMon]] = ()
) -> list[ATm] | None:
    """``Prog.sym``."""
    if p.kind == "leaf":
        return list(p.args[0])
    if p.kind == "loop":
        levels, j, lo, cnt, step, init, inv, k0, k1 = p.args
        x0, y0 = prog_sym(step, fl, pw), prog_sym(init, fl, pw)
        if x0 is None or y0 is None:
            return None
        v = Y.ip_add(Y.ip_c(lo), cnt)
        if (
            not counts(step)
            and not counts(init)
            and len(levels) < IN
            and all(2 * IN <= y for y in Z.ip_vs(cnt))
            and all(sub_ok(j, v, t) for t in inv)
            and loop_chk(fl, pw, levels, j, lo, x0, y0, inv, k0, k1)
        ):
            return [t_sub(j, v, t) for t in inv]
        return None
    if p.kind == "sum":
        d, x, body = p.args
        e = prog_sym(body, fl, pw)
        if e is None or counts(body):
            return None
        return ax_sums(((x, d),), e)
    if p.kind == "cnj":
        x0 = prog_sym(p.args[0], fl, pw)
        if x0 is None:
            return None
        return [t_conj(t) for t in x0]
    if p.kind == "sub":
        x, v, a = p.args
        x0 = prog_sym(a, fl, pw)
        if x0 is None or counts(a) or not all(sub_ok(x, v, t) for t in x0):
            return None
        return [t_sub(x, v, t) for t in x0]
    if p.kind == "ren":
        pairs, a = p.args
        x0 = prog_sym(a, fl, pw)
        m = rmap(pairs)
        if x0 is None or counts(a) or not ren_oka(m, x0):
            return None
        return ax_ren(m, x0)
    xs = [prog_sym(q, fl, pw) for q in p.args if isinstance(q, Prog)]
    if any(x is None for x in xs):
        return None
    x, y = xs[0], xs[1]
    assert x is not None and y is not None
    if p.kind == "app":
        return app_sym(p.args[0], apart(fresh(x, y), x), y)
    if p.kind == "ten":
        return ten_sym(p.args[0], x, apart(fresh(x, y), y))
    if p.kind == "mul":
        y2 = apart(fresh(x, y), y)
        return Z.ax_mul(x, y2) if Z.ax_mul_ok(x, y2) else None
    if p.kind == "inn":
        return inn_sym(p.args[0], apart(fresh(x, y), x), y)
    return x + y


def cert_check(
    fl: Sequence[int],
    pw: Sequence[tuple[Y.DMon, Y.DMon]],
    p: Prog,
    r: Sequence[ATm],
    ctx: Z.Ctx | None = None,
    rounds: int = 1,
) -> bool:
    """``certCheck``; with a context, the program's expression passed under it, and with two
    rounds the normal form passed and normalised again."""
    e = prog_sym(p, fl, pw)
    if e is None:
        return False
    if ctx is not None:
        e = Z.x_pass(ctx, e)
    nf = Z.nf_a(fl, pw, e + Z.ax_neg(r))
    if nf and ctx is not None and rounds == 2:
        nf = Z.nf_a(fl, pw, Z.x_pass(ctx, nf))
    return not nf


# Lean text


def lean_q(q: Fraction) -> str:
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"(({q.numerator} : ℚ) / {q.denominator})"


def lean_ints(xs: Sequence[int]) -> str:
    return "[" + ", ".join(f"({x} : ℤ)" if x < 0 else str(x) for x in xs) + "]"


def lean_nats(xs: Sequence[int]) -> str:
    return "[" + ", ".join(map(str, xs)) + "]"


@dataclass
class Text:
    """Lean text of expressions, dimension monomials by their names in ``dms``."""

    dms: dict[Y.DMon, str] = field(default_factory=dict)

    def dm(self, m: Y.DMon) -> str:
        return self.dms.get(m, f"⟨{m[0]}, {lean_nats(m[1])}⟩")

    def cm(self, c: Y.CMon) -> str:
        if c[1:] == (Fraction(0), (), (), (), ()):
            return f"CMon.ofQ {lean_q(c[0])}"
        gc = "[" + ", ".join(f"({a}, {self.dm(m)})" for a, m in c[5]) + "]"
        return (
            f"⟨{lean_q(c[0])}, {lean_q(c[1])}, {lean_ints(c[2])}, {lean_nats(c[3])}, "
            f"{lean_ints(c[4])}, {gc}⟩"
        )

    @staticmethod
    def ip(p: Y.IPoly) -> str:
        return "[" + ", ".join(f"({lean_nats(m)}, {c})" for m, c in p) + "]"

    def fac(self, f: Y.Fac) -> str:
        return f"({self.dm(f[0])}, {self.ip(f[1])})"

    def atom(self, a: Atom) -> str:
        dp = "[" + ", ".join(self.dm(m) for m in a[3]) + "]"
        args = "[" + ", ".join(f"({self.ip(p)}, {self.dm(m)})" for p, m in a[4]) + "]"
        return f"⟨{a[0]}, {a[1]}, {lean_ints(a[2])}, {dp}, {args}⟩"

    def tm(self, t: ATm) -> str:
        sums = "[" + ", ".join(f"({x}, {self.dm(m)})" for x, m in t[1]) + "]"
        ats = "[" + ", ".join(self.atom(a) for a in t[2]) + "]"
        dels = "[" + ", ".join(self.fac(f) for f in t[3]) + "]"
        phs = "[" + ", ".join(self.fac(f) for f in t[4]) + "]"
        aps = (
            "["
            + ", ".join(
                f"({a[0]}, {self.ip(a[1])}, [" + ", ".join(self.atom(b) for b in a[2]) + "])"
                for a in t[5]
            )
            + "]"
        )
        return f"⟨{self.cm(t[0])}, {sums}, {ats}, {dels}, {phs}, {aps}⟩"

    def ex(self, e: Sequence[ATm], indent: str = "  ") -> str:
        if not e:
            return "[]"
        return "[" + f",\n{indent} ".join(self.tm(t) for t in e) + "]"

    def rels(self, ks: Sequence[tuple[ATm, int, int]]) -> str:
        if not ks:
            return "[]"
        return "[" + ",\n     ".join(f"({self.tm(t)}, {r}, {i})" for t, r, i in ks) + "]"

    def prog(self, p: Prog, top: bool = True) -> str:
        if p.name is not None and not top:
            return p.name
        if p.kind == "leaf":
            text = f".leaf {self.ex(p.args[0], '    ')}"
        elif p.kind in ("app", "inn"):
            levels = "[" + ", ".join(self.dm(m) for m in p.args[0]) + "]"
            text = f".{p.kind} {levels} {self.prog(p.args[1], False)} {self.prog(p.args[2], False)}"
        elif p.kind == "cnj":
            text = f".cnj {self.prog(p.args[0], False)}"
        elif p.kind == "ren":
            pairs = "[" + ", ".join(f"({u}, {w})" for u, w in p.args[0]) + "]"
            text = f".ren {pairs} {self.prog(p.args[1], False)}"
        elif p.kind == "sub":
            text = f".sub {p.args[0]} {self.ip(p.args[1])} {self.prog(p.args[2], False)}"
        elif p.kind == "loop":
            levels, j, lo, cnt, step, init, inv, k0, k1 = p.args
            ls = "[" + ", ".join(self.dm(m) for m in levels) + "]"
            text = (
                f".loop {ls} {j} ({lo}) {self.ip(cnt)} {self.prog(step, False)} "
                f"{self.prog(init, False)}\n    {self.ex(inv, '    ')}\n    {self.rels(k0)}"
                f"\n    {self.rels(k1)}"
            )
        elif p.kind == "ten":
            text = f".ten {p.args[0]} {self.prog(p.args[1], False)} {self.prog(p.args[2], False)}"
        elif p.kind == "sum":
            text = f".sum {self.dm(p.args[0])} {p.args[1]} {self.prog(p.args[2], False)}"
        else:
            text = f".{p.kind} {self.prog(p.args[0], False)} {self.prog(p.args[1], False)}"
        return text if top else f"({text})"


# sympy expressions as expressions

AID = 5000000
PID = 9000000
FB = 1000000
GB = 2000000
"""The first atom variable of a leaf."""


@dataclass
class Vars:
    """The variable of every symbol: dimension symbols (and powers ``d^n`` as their own
    symbols) by index, parameters from ``PAR``, pattern variables from ``IN``, summation
    indices from ``BV``, atoms from ``AID``; the range of every index variable that has one."""

    dsyms: list[sympy.Symbol] = field(default_factory=list)
    params: list[str] = field(default_factory=list)
    ids: dict[sympy.Symbol, int] = field(default_factory=dict)
    ranges: dict[int, sympy.Expr] = field(default_factory=dict)
    pw: list[tuple[Y.DMon, Y.DMon]] = field(default_factory=list)
    powers: dict[sympy.Symbol, tuple[sympy.Expr, sympy.Symbol]] = field(default_factory=dict)
    widths: list[sympy.Symbol] = field(default_factory=list)
    loops: list[sympy.Symbol] = field(default_factory=list)
    divs: list[tuple[sympy.Expr, sympy.Expr]] = field(default_factory=list)
    default: sympy.Expr | None = None
    catoms: list[sympy.Symbol] = field(default_factory=list)
    cfuncs: list[tuple[sympy.Symbol, sympy.Expr]] = field(default_factory=list)
    angle_atoms: dict[sympy.Symbol, sympy.Symbol] = field(default_factory=dict)
    """The atom ``e^(i t)`` of each real angle symbol ``t``."""
    gsyms: dict[sympy.Symbol, int] = field(default_factory=dict)
    """The built-in power index of ``u_N = e^(i asin(N^(-1/2)))`` and ``q_N = 1/(u_N + 1/u_N)``."""
    unit_params: set[sympy.Symbol] = field(default_factory=set)
    """The real parameters assumed in ``0..1``, each read as ``sin^2`` of an angle."""
    anchors: dict[tuple[sympy.Expr, sympy.Symbol], int] = field(default_factory=dict)
    funcs: list[str] = field(default_factory=list)
    needs_width: bool = False
    next_bound: int = BV
    next_atom: int = AID
    atoms: list[Atom] = field(default_factory=list)

    def dim(self, s: sympy.Symbol) -> None:
        if s not in self.dsyms:
            self.dsyms.append(s)

    def bound(self, s: sympy.Symbol, size: sympy.Expr | None = None) -> int:
        if s not in self.ids:
            self.ids[s] = self.next_bound
            self.next_bound += 1
        if size is not None:
            self.ranges[self.ids[s]] = size
        return self.ids[s]

    def var(self, s: sympy.Basic) -> int:
        if s in self.ids:
            return self.ids[s]
        if not isinstance(s, sympy.Symbol) or isinstance(s, sympy.Dummy):
            raise CertifyError(f"{s} is not an index variable")
        if s in self.dsyms or s in self.widths:
            raise CertifyError(f"the size {s} appears in an index expression")
        if s.name not in self.params:
            self.params.append(s.name)
        return PAR + self.params.index(s.name)

    def count(self, e: sympy.Expr) -> Y.IPoly:
        """A loop count as a polynomial in parameters; a width symbol is read as one."""
        saved = self.widths
        self.widths = []
        try:
            return self.ipoly(e)
        finally:
            self.widths = saved

    def power(self, base: sympy.Expr, n: sympy.Symbol) -> sympy.Symbol:
        """The dimension symbol standing for ``base^n``."""
        for a, (b, m) in self.powers.items():
            if b == base and m == n:
                return a
        a = sympy.Symbol(
            f"{base}^{n}" if isinstance(n, sympy.Symbol) else f"{base}^({n})", positive=True
        )
        self.powers[a] = (base, n)
        for w in sorted(sympy.sympify(n).free_symbols, key=str):
            if w not in self.widths:
                self.widths.append(w)
        self.dim(a)
        self.pw.append((self.dmon(base), self.dmon(a)))
        return a

    def dmon(self, e: sympy.Expr) -> Y.DMon:
        e = sympy.expand(sympy.sympify(e))
        if e == 0:
            return (0, ())
        c, rest = e.as_coeff_Mul()
        out = sympy.Integer(1)
        for f in sympy.Mul.make_args(rest):
            if f == 1:
                continue
            base, k = f.as_base_exp()
            if k.free_symbols:
                widths = [s for s in k.free_symbols]
                if len(widths) != 1:
                    raise CertifyError(f"the size {e}")
                n = widths[0]
                p = sympy.Poly(k, n)
                if p.degree() != 1 or not all(x.is_Integer for x in p.all_coeffs()):
                    raise CertifyError(f"the size {e}")
                a, b = (int(x) for x in p.all_coeffs())
                if a < 1:
                    raise CertifyError(f"the size {e}")
                c0 = self.anchors.get((base, n), 0)
                if b - a * c0 < 0:
                    out *= self.power(base, a * n + b)
                else:
                    out *= self.power(base, n + c0) ** a * base ** (b - a * c0)
            else:
                out *= f
        if isinstance(c, sympy.Integer) and int(c) > 1:
            pass
        e2 = sympy.expand(c * out)
        for s in e2.free_symbols:
            if s not in self.dsyms:
                raise CertifyError(f"the size {e} depends on {s}, which is not a dimension")
        try:
            return Y._dmon(e2, self.dsyms)
        except Y.SymUnsupported as exc:
            raise CertifyError(str(exc)) from exc

    def range_of(self, e: sympy.Expr, ctx: sympy.Expr | None) -> sympy.Expr:
        """The modulus an atom's argument is reduced by."""
        if isinstance(e, sympy.Symbol) and e in self.ids and self.ids[e] in self.ranges:
            return self.ranges[self.ids[e]]
        if ctx is not None:
            return ctx
        if self.default is not None:
            return self.default
        raise CertifyError(f"no range is known for the atom argument {e}")

    def known_range(self, e: sympy.Expr) -> sympy.Expr | None:
        """The range of an index variable that has one."""
        if isinstance(e, sympy.Symbol) and e in self.ids and self.ids[e] in self.ranges:
            return self.ranges[self.ids[e]]
        return None

    def atom(
        self,
        f: int,
        ks: Sequence[int],
        dp: Sequence[sympy.Expr],
        args: Sequence[tuple[sympy.Expr, sympy.Expr]],
    ) -> int:
        a: Atom = (
            0,
            f,
            tuple(ks),
            tuple(self.dmon(x) for x in dp),
            tuple((self.ipoly(x), self.dmon(m)) for x, m in args),
        )
        for b in self.atoms:
            if b[1:] == a[1:]:
                return b[0]
        a = (self.next_atom, *a[1:])
        self.next_atom += 1
        self.atoms.append(a)
        return a[0]

    def quotients(self, e: sympy.Expr) -> sympy.Expr:
        """``e`` with each ``D2 / D1`` of an assumed divisibility written as a quotient atom's
        variable."""
        for d2, d1 in self.divs:
            q = sympy.expand(d2 / d1)
            if not e.has(d1):
                continue
            z = sympy.Dummy("quo", integer=True)
            e2 = sympy.expand(e).subs(q, z)
            if e2.has(z) and not sympy.fraction(sympy.together(e2))[1].has(d1):
                self.ids[z] = self.atom(12, [], [d2, d1], [])
                e = e2
        return e

    def repunits(self, e: sympy.Expr) -> sympy.Expr:
        """``e`` with each ``(d^k - 1)/(d - 1)`` written as a repunit atom's variable."""
        e = sympy.sympify(e)
        mods = {m: sympy.Dummy("mod") for m in e.atoms(sympy.Mod)}
        e = e.xreplace(mods)
        for p in sorted(e.atoms(sympy.Pow), key=str):
            b, k = p.base, p.exp
            if not (k.free_symbols and b in self.dsyms) or k.free_symbols & set(self.loops):
                continue
            r = sympy.Dummy("rep", integer=True)
            e2 = sympy.cancel(sympy.together(e.subs(p, r * (b - 1) + 1)))
            if sympy.fraction(e2)[1].free_symbols:
                continue
            self.ids[r] = self.atom(4, [], [b, p], [])
            e = e2
        return e.xreplace({v: k for k, v in mods.items()})

    def ipoly(self, e: sympy.Expr, ctx: sympy.Expr | None = None) -> Y.IPoly:
        """An integer polynomial in index variables and atoms; ``ctx`` the modulus it is read
        under (a register's levels or a root of unity's order)."""
        p: Y.IPoly = ()
        e = self.quotients(sympy.sympify(e))
        for term in sympy.Add.make_args(sympy.expand(self.repunits(e))):
            c, rest = term.as_coeff_Mul()
            if not c.is_Integer:
                raise CertifyError(f"the index expression {e} has a non-integer coefficient")
            mon: list[int] = []
            for f in sympy.Mul.make_args(rest):
                if f == 1:
                    continue
                base, k = f.as_base_exp()
                if k.free_symbols and (base.is_Integer or base in self.dsyms):
                    if k.free_symbols <= set(self.widths) or (
                        base.is_Integer and k.free_symbols & set(self.widths)
                    ):
                        mon.append(self.atom(8, [], [f], []))
                        continue
                    if base == 2 and isinstance(k, sympy.Symbol):
                        mon.append(self.atom(7, [], [], [(k, sympy.Integer(0))]))
                        continue
                    if k in self.loops:
                        mon.append(self.atom(7, [], [base], [(k, sympy.Integer(0))]))
                        continue
                if not (k.is_Integer and int(k) > 0):
                    raise CertifyError(f"the index expression {e} is not a polynomial")
                if isinstance(base, sympy.Symbol) and base in self.dsyms:
                    mon += [self.atom(8, [], [base], [])] * int(k)
                    continue
                if isinstance(base, sympy.Symbol):
                    mon += [self.var(base)] * int(k)
                    continue
                inner = self.atom_poly(base, ctx)
                if len(inner) == 1 and inner[0][1] == 1 and len(inner[0][0]) <= 1:
                    mon += list(inner[0][0]) * int(k)
                else:
                    for _ in range(int(k) - 1):
                        inner = Y.ip_mul(inner, self.atom_poly(base, ctx))
                    rest_mon = tuple(sorted(mon))
                    for m2, c2 in Y.ip_mul(inner, ((rest_mon, 1),)):
                        p = Y.ip_ins(m2, int(c) * c2, p)
                    mon = []
                    c = sympy.Integer(0)
                    break
            if c != 0:
                p = Y.ip_ins(tuple(sorted(mon)), int(c), p)
        return p

    def atom_poly(self, f: sympy.Expr, ctx: sympy.Expr | None) -> Y.IPoly:
        """A function application as a polynomial: an atom, or a polynomial it equals under
        ``ctx``."""
        from diracula import pathsum as P

        two = ctx is not None and sympy.expand(ctx - 2) == 0
        digit = self.digit_atom(f, ctx)
        if digit is not None:
            return digit
        if isinstance(f, sympy.Mod):
            v, m = f.args
            if ctx is not None and sympy.expand(m - ctx) == 0:
                return self.ipoly(v, ctx)
            big = self.less_one(m)
            if big is not None:
                return Y.ip_v(
                    self.atom(13, [], [big], [(self.wrap_range(v, big), sympy.Integer(0))])
                )
            return Y.ip_v(self.atom(2, [], [], [(v, m)]))
        if isinstance(f, P.xor):
            a, b = f.args
            if two:
                return self.ipoly(a + b, ctx)
            ma = self.range_of(a, ctx)
            a, b = self.bit_wrap(a), self.bit_wrap(b)
            return Y.ip_v(self.atom(1, [], [], [(a, ma), (b, self.range_of(b, ma))]))
        if isinstance(f, P.bit):
            x, j = f.args
            if j == 0:
                if two:
                    return self.ipoly(x, ctx)
                return Y.ip_v(self.atom(2, [], [], [(x, 2)]))
            mx = self.range_of(x, ctx)
            return Y.ip_v(self.atom(5, [], [], [(x, mx), (j, j + 1)]))
        if isinstance(f, (P.bitdot, P.ddot)):
            a, b = f.args[0], f.args[1]
            d = sympy.Integer(2) if isinstance(f, P.bitdot) else f.args[2]
            n = self.known_range(a) or self.known_range(b) or self.default
            if n is None:
                n = self.range_of(a, None) if isinstance(a, sympy.Symbol) else self.range_of(b, ctx)
            return Y.ip_v(self.atom(0, [], [d, n], [(a, n), (b, n)]))
        if isinstance(f, (P.pop, P.dsum)):
            v = f.args[0]
            d = sympy.Integer(2) if isinstance(f, P.pop) else f.args[1]
            n = self.range_of(v, ctx)
            return Y.ip_v(self.atom(6, [], [d, n], [(v, n)]))
        if isinstance(f, sympy.Piecewise):
            raise CertifyError(f"the piecewise value {f}")
        body = getattr(type(f), "_body", None)
        if isinstance(f, sympy.Function) and body is not None:
            unfolded = body.xreplace(dict(zip(type(f)._params, f.args, strict=True)))
            saved = (list(self.atoms), self.next_atom, list(self.funcs))
            try:
                return self.ipoly(unfolded, ctx)
            except CertifyError:
                self.atoms, self.next_atom, self.funcs = saved
        if isinstance(f, sympy.Function):
            name = type(f).__name__
            if name not in self.funcs:
                self.funcs.append(name)
            args = [(a, self.range_of(a, ctx)) for a in f.args]
            return Y.ip_v(self.atom(100 + self.funcs.index(name), [], [], args))
        raise CertifyError(f"the index expression {f}")

    def less_one(self, m: sympy.Expr) -> sympy.Expr | None:
        """``N`` when ``m = N - 1`` for a dimension monomial ``N`` that is not constant."""
        big = sympy.expand(m + 1)
        if big.is_Integer or not big.free_symbols:
            return None
        try:
            dm = self.dmon(big)
        except CertifyError:
            return None
        return big if not Y.dm_const(dm) else None

    def wrap_range(self, e: sympy.Expr, big: sympy.Expr) -> sympy.Expr:
        """``e`` with each index variable of range ``big`` read modulo ``big``."""
        sub = {
            v: sympy.Mod(v, big, evaluate=False)
            for v in sympy.sympify(e).free_symbols
            if isinstance(v, sympy.Symbol)
            and v in self.ids
            and self.ids[v] in self.ranges
            and sympy.expand(self.ranges[self.ids[v]] - big) == 0
        }
        return sympy.sympify(e).xreplace(sub)

    def bit_wrap(self, e: sympy.Expr) -> sympy.Expr:
        """``e`` with each index of two levels that multiplies another factor read as itself
        modulo 2."""
        e = sympy.expand(e)
        bits = set()
        for term in sympy.Add.make_args(e):
            fs = [f for f in sympy.Mul.make_args(term) if not f.is_Number]
            if len(fs) >= 2:
                bits |= {
                    f
                    for f in fs
                    if isinstance(f, sympy.Symbol)
                    and f in self.ids
                    and sympy.sympify(self.ranges.get(self.ids[f], 0)) == 2
                }
        return e.xreplace({f: sympy.Mod(f, 2, evaluate=False) for f in bits})

    def loop_power(self, e: sympy.Expr) -> tuple[sympy.Expr, sympy.Symbol] | None:
        """``(d, j)`` when ``e`` is ``d^j`` for a loop variable ``j`` and a dimension or
        integer ``d``."""
        if (
            isinstance(e, sympy.Pow)
            and e.exp in self.loops
            and (e.base.is_Integer or e.base in self.dsyms)
        ):
            return e.base, cast(sympy.Symbol, e.exp)
        return None

    def digit_atom(self, f: sympy.Expr, ctx: sympy.Expr | None) -> Y.IPoly | None:
        """``floor(x/d^j) % d``, ``x % d^j`` and ``floor(x/d^j)`` for a loop variable ``j`` as
        the atoms digit, low digits and high digits."""
        z = sympy.Integer(0)
        if isinstance(f, sympy.Mod):
            u, m = f.args
            lp = self.loop_power(m)
            if lp is not None:
                return Y.ip_v(self.atom(10, [], [lp[0]], [(u, self.range_of(u, ctx)), (lp[1], z)]))
            if isinstance(u, sympy.floor):
                q = self.high_parts(u.args[0])
                if q is not None and sympy.expand(q[1] - m) == 0:
                    x, d, j = q
                    return Y.ip_v(self.atom(9, [], [d], [(x, self.range_of(x, ctx)), (j, z)]))
        if isinstance(f, sympy.floor):
            q = self.high_parts(f.args[0])
            if q is not None:
                x, d, j = q
                return Y.ip_v(self.atom(11, [], [d], [(x, self.range_of(x, ctx)), (j, z)]))
        return None

    def high_parts(self, w: sympy.Expr) -> tuple[sympy.Expr, sympy.Expr, sympy.Symbol] | None:
        """``(x, d, j)`` when ``w`` is ``x / d^j`` for a loop variable ``j``."""
        num, den = sympy.fraction(sympy.together(w))
        lp = self.loop_power(den)
        if lp is None:
            for f in sympy.Mul.make_args(w):
                b, k = f.as_base_exp()
                if (-k) in self.loops and (b.is_Integer or b in self.dsyms):
                    return sympy.expand(w * b ** (-k)), b, cast(sympy.Symbol, -k)
            return None
        return num, lp[0], lp[1]

    def phase(self, r: sympy.Expr) -> tuple[Y.CMon, list[Y.Fac]]:
        """``e^(2 pi i r)`` as a root of unity of a dimension monomial."""
        r = sympy.expand(r)
        den: sympy.Expr = sympy.Integer(1)
        for term in sympy.Add.make_args(r):
            den = sympy.lcm(den, sympy.fraction(term)[1])
        num = sympy.expand(r * den)
        dm = self.dmon(den)
        if not num.free_symbols and not num.atoms(sympy.Function):
            if dm[1]:
                return Y.of_q(1), [(dm, self.ipoly(num))]
            q = sympy.Rational(num, dm[0])
            return Y.ex_q(Fraction(int(q.p), int(q.q))), []
        poly = self.ipoly(num, den)
        if dm == (1, ()):
            return Y.of_q(1), []
        if Y.dm_const(dm):
            c0 = next((c for m, c in poly if m == ()), 0)
            if c0:
                poly = Y.ip_sub(poly, Y.ip_c(c0))
                ex = Y.ex_q(Fraction(c0, dm[0]))
                return ex, [(dm, poly)] if poly else []
        return Y.of_q(1), [(dm, poly)]

    def amp(
        self, amp: sympy.Expr
    ) -> list[tuple[Y.CMon, list[Y.Fac], list[Y.Fac], tuple[Z.APw, ...]]]:
        """An amplitude as terms: a coefficient, deltas, roots of unity and powers of coefficient
        atoms."""
        out = []
        amp = self.angles(self.unit_param(self.grover(sympy.sympify(amp))))
        expanded = sympy.expand(amp, log=False, power_exp=False, power_base=False)
        for term in sympy.Add.make_args(expanded):
            if term == 0:
                continue
            try:
                out.append(self.amp_term(term))
            except CertifyError:
                simpler = sympy.expand(sympy.radsimp(term), log=False, power_exp=False)
                if sympy.expand(simpler - term) == 0 and simpler == term:
                    raise
                out += self.amp(simpler)
        return out

    def grover(self, e: sympy.Expr) -> sympy.Expr:
        """``e`` with ``cos(c θ)``, ``sin(c θ)`` of ``θ = acos(1 - 2/N)`` for a dimension ``N``
        read through ``u = u_N``, ``θ = 2 asin(N^(-1/2))``: ``cos(c θ) = (u^(2c) + u^(-2c))/2``,
        ``sin(c θ) = (u^(2c) - u^(-2c))/(2 i)``, and ``sqrt(N - 1) = sqrt(N)/(2 q_N)``."""
        acs = [f for f in e.atoms(sympy.acos) if f.args[0].free_symbols]
        for f in acs:
            big = sympy.simplify(2 / (1 - f.args[0]))
            try:
                dm = self.dmon(big)
            except CertifyError:
                continue
            if dm[0] != 1 or sum(dm[1]) != 1 or dm[1][-1] != 1:
                continue
            i = len(dm[1]) - 1
            self.needs_width = True
            u = sympy.Symbol(f"u_{i}", nonzero=True)
            q = sympy.Symbol(f"q_{i}", nonzero=True)
            self.gsyms[u], self.gsyms[q] = GB + 4 * i, GB + 4 * i + 2

            def trig(g: sympy.Basic, f: sympy.Basic = f) -> bool:
                return isinstance(g, (sympy.cos, sympy.sin)) and g.args[0].has(f)

            def rd(g: sympy.Basic, f: sympy.Basic = f, u: sympy.Symbol = u) -> sympy.Expr:
                c = sympy.simplify(g.args[0] / f)
                if c.has(sympy.acos):
                    raise CertifyError(f"the angle {g.args[0]}")
                a, b = u ** sympy.expand(2 * c), u ** sympy.expand(-2 * c)
                return (a + b) / 2 if isinstance(g, sympy.cos) else (a - b) / (2 * sympy.I)

            e = e.replace(trig, rd)

            def root(g: sympy.Basic, big: sympy.Expr = big) -> bool:
                return (
                    g.is_Pow
                    and g.exp in (sympy.Rational(1, 2), sympy.Rational(-1, 2))
                    and sympy.expand(g.base - big + 1) == 0
                )

            def rr(g: sympy.Basic, big: sympy.Expr = big, q: sympy.Symbol = q) -> sympy.Expr:
                v = sympy.sqrt(big) / (2 * q)
                return v if g.exp > 0 else 1 / v

            e = e.replace(root, rr)
        return e

    def real_angle_symbols(self, e: sympy.Basic) -> list[sympy.Symbol]:
        return [
            x
            for x in e.free_symbols
            if isinstance(x, sympy.Symbol)
            and x.is_real
            and not x.is_integer
            and x not in self.dsyms
            and x not in self.angle_atoms.values()
        ]

    def unit_param(self, e: sympy.Expr) -> sympy.Expr:
        """``e`` with each parameter ``p`` of :attr:`unit_params` read as ``sin^2(a)`` of an angle
        ``a`` in ``0..pi/2``, through the atom ``z = e^(i a)``: ``sqrt(p) = (z - conj z)/(2 i)``,
        ``sqrt(1 - p) = (z + conj z)/2`` and ``p = (2 z conj z - z^2 - conj(z)^2)/4``."""
        hit = [q for q in self.unit_params if q in e.free_symbols]
        if not hit:
            return e
        for q in hit:
            z = self.angle_atoms.setdefault(
                sympy.Symbol(f"asin(sqrt({q.name}))", real=True),
                sympy.Symbol(f"e^(i*asin(sqrt({q.name})))", complex=True),
            )
            zc = sympy.conjugate(z)
            sin, cos = (z - zc) / (2 * sympy.I), (z + zc) / 2
            e = e.replace(
                lambda f, q=q: f.is_Pow and f.exp == sympy.Rational(1, 2) and f.base == q,
                lambda f, sin=sin: sin,
            )
            e = e.replace(
                lambda f, q=q: (
                    f.is_Pow and f.exp == sympy.Rational(1, 2) and sympy.expand(f.base - 1 + q) == 0
                ),
                lambda f, cos=cos: cos,
            )
            e = e.xreplace({q: (2 * z * zc - z**2 - zc**2) / 4})
        return e

    def angles(self, e: sympy.Expr) -> sympy.Expr:
        """``e`` with ``e^(i c t)``, ``cos(c t)`` and ``sin(c t)`` of a real symbol ``t`` and an
        integer ``c`` read through the atom ``z_t = e^(i t)``: ``e^(i c t)`` is ``z_t^c`` and
        ``e^(-i c t)`` is ``conj(z_t)^c``."""

        def trig(f: sympy.Basic) -> bool:
            return isinstance(f, (sympy.exp, sympy.cos, sympy.sin)) and bool(
                self.real_angle_symbols(f)
            )

        if not e.atoms(sympy.exp, sympy.cos, sympy.sin) or not any(
            trig(f) for f in e.atoms(sympy.exp, sympy.cos, sympy.sin)
        ):
            return e
        e = e.replace(
            lambda f: isinstance(f, (sympy.cos, sympy.sin)) and bool(self.real_angle_symbols(f)),
            lambda f: f.rewrite(sympy.exp),
        )

        def split(f: sympy.exp) -> sympy.Expr:
            out: sympy.Expr = sympy.Integer(1)
            rest: sympy.Expr = sympy.Integer(0)
            for term in sympy.Add.make_args(sympy.expand(f.args[0])):
                syms = self.real_angle_symbols(term)
                if not syms:
                    rest += term
                    continue
                if len(syms) != 1:
                    raise CertifyError(f"the angle {term}")
                t = syms[0]
                c = sympy.simplify(term / (sympy.I * t))
                if not (c.is_Integer or integer_index(c)) and self.cfunc_match(term):
                    rest += term
                    continue
                if not (c.is_Integer or integer_index(c)):
                    raise CertifyError(f"the angle {term}: not an integer multiple of {t}")
                z = self.angle_atoms.setdefault(t, sympy.Symbol(f"e^(i*{t.name})", complex=True))
                if not c.is_Integer:
                    out *= z ** sympy.expand(c)
                    continue
                out *= z ** int(c) if c > 0 else sympy.conjugate(z) ** int(-c)
            return out * sympy.exp(rest)

        e = e.replace(
            lambda f: isinstance(f, sympy.exp) and bool(self.real_angle_symbols(f)), split
        )
        return e

    def amp_term(
        self, term: sympy.Expr
    ) -> tuple[Y.CMon, list[Y.Fac], list[Y.Fac], tuple[Z.APw, ...]]:
        """One product of an amplitude: a coefficient, deltas, roots of unity and powers of
        coefficient atoms."""
        cm, dels, phs = Y.of_q(1), [], []
        aps: list[Z.APw] = []
        for f in sympy.Mul.make_args(term):
            if isinstance(f, sympy.KroneckerDelta):
                dels.append(self.kronecker(f))
                continue
            ap = self.atom_power(f)
            if ap is not None:
                aps.append(ap)
                continue
            if isinstance(f, sympy.exp):
                left = sympy.Integer(0)
                for part in sympy.Add.make_args(sympy.expand(f.args[0])):
                    hit = self.cfunc_match(part)
                    if hit is None:
                        left += part
                        continue
                    aps.append((FB + 2 * hit[0], self.ipoly(hit[1]), ()))
                if left != sympy.expand(f.args[0]):
                    f = sympy.exp(left)
                    if left == 0:
                        continue
            c2, p2 = self.factor(f)
            cm = Y.cm_mul(cm, c2)
            phs += p2
        return cm, dels, phs, tuple(sorted(aps))

    def cfunc(self, arg: sympy.Expr, k: sympy.Symbol) -> int:
        """The opaque function ``k -> e^(arg(k))`` of an index, numbered in order."""
        for i, (kk, a) in enumerate(self.cfuncs):
            if sympy.simplify(a.xreplace({kk: k}) - arg) == 0:
                return i
        kk = sympy.Dummy("K", integer=True)
        self.cfuncs.append((kk, arg.xreplace({k: kk})))
        return len(self.cfuncs) - 1

    def cfunc_match(self, part: sympy.Expr) -> tuple[int, sympy.Expr] | None:
        """``(i, k)`` when ``e^part`` is the opaque function ``i`` at the index ``k``."""
        for i, (kk, a) in enumerate(self.cfuncs):
            for k in part.free_symbols:
                if k in self.ids and sympy.simplify(a.xreplace({kk: k}) - part) == 0:
                    return i, k
        return None

    def atom_power(self, f: sympy.Expr) -> Z.APw | None:
        """``z^E`` of a coefficient atom ``z`` and an integer index expression ``E`` as the power
        of the atom by ``E``, read through its own table of atoms numbered from ``PID``."""
        base, k = f.as_base_exp()
        if base in self.gsyms:
            return (self.gsyms[base], Y.ip_c(int(k)) if k.is_Integer else self.count(k), ())
        if k.is_Integer or not k.free_symbols:
            return None
        j = self.coefficient(base)
        if j is None and isinstance(base, sympy.conjugate):
            j = self.coefficient(base.args[0])
            j = None if j is None else j + 1
        if j is None:
            return None
        poly = self.count(k)
        need = {v for m, _ in poly for v in m if v >= AID}
        grew = True
        while grew:
            grew = False
            for a in self.atoms:
                if a[0] in need:
                    for v in Z.at_vs(a):
                        if v >= AID and v not in need:
                            need.add(v)
                            grew = True
        table = [a for a in self.atoms if a[0] in need]
        names = {a[0]: PID + i for i, a in enumerate(table)}

        def m(v: int) -> int:
            return names.get(v, v)

        return (j, Z.ip_ren(m, poly), tuple(Z.at_ren(m, a) for a in table))

    def kronecker(self, f: sympy.KroneckerDelta) -> Y.Fac:
        """``[a = b]`` as a delta modulo the range of an index on one side, the other side a
        constant 0 or 1 or an index of the same range."""
        a, b = f.args[0], f.args[1]
        for x, y in ((a, b), (b, a)):
            if isinstance(x, sympy.Symbol) and x in self.ids and self.ids[x] in self.ranges:
                m = self.ranges[self.ids[x]]
                ok = (
                    (y.is_Integer and 0 <= int(y) <= 1)
                    or (y.is_Integer and m.is_Integer and 0 <= int(y) < int(m))
                    or (
                        isinstance(y, sympy.Symbol)
                        and y in self.ids
                        and self.ranges.get(self.ids[y]) == m
                    )
                )
                if ok:
                    if y.is_Integer and int(y) == 1:
                        self.needs_width = True
                    return self.dmon(m), Y.ip_sub(self.ipoly(x), self.ipoly(y))
        for x, y in ((a, b), (b, a)):
            if y == 0 and isinstance(x, sympy.Mod):
                try:
                    return self.dmon(x.args[1]), self.ipoly(x.args[0])
                except CertifyError:
                    break
        raise CertifyError(f"the delta {f}")

    def factor(self, f: sympy.Expr) -> tuple[Y.CMon, list[Y.Fac]]:
        cm, phs = self.factor_raw(f)
        return prime_radicals(cm), phs

    def coefficient(self, s: sympy.Basic) -> int | None:
        """The coefficient atom of a complex parameter ``s``: ``2 k`` for the ``k``-th, its
        conjugate ``2 k + 1``."""
        if not isinstance(s, sympy.Symbol) or s in self.dsyms or s in self.widths:
            return None
        if s.is_integer and (isinstance(s, sympy.Dummy) or s in self.ids or s in self.loops):
            return None
        if s not in self.catoms:
            self.catoms.append(s)
        return 2 * self.catoms.index(s)

    def factor_raw(self, f: sympy.Expr) -> tuple[Y.CMon, list[Y.Fac]]:
        base, k = f.as_base_exp()
        if k.is_Integer:
            j = self.coefficient(base)
            if j is not None:
                return Y.atom_p(j, int(k)), []
            if isinstance(base, sympy.conjugate):
                j = self.coefficient(base.args[0])
                if j is not None:
                    return Y.atom_p(j + 1, int(k)), []
            if isinstance(base, sympy.Abs) and int(k) % 2 == 0:
                j = self.coefficient(base.args[0])
                if j is not None:
                    return Y.cm_mul(Y.atom_p(j, int(k) // 2), Y.atom_p(j + 1, int(k) // 2)), []
        return self.factor_core(f)

    def factor_core(self, f: sympy.Expr) -> tuple[Y.CMon, list[Y.Fac]]:
        if f.is_Rational:
            return Y.of_q(Fraction(int(f.p), int(f.q))), []
        if f == sympy.I:
            return Y.ex_q(Fraction(1, 4)), []
        if isinstance(f, sympy.exp):
            return self.phase(f.args[0] / (2 * sympy.pi * sympy.I))
        base, k = f.as_base_exp()
        if base == -1:
            return self.phase(k / 2)
        if base == sympy.I:
            return self.phase(k / 4)
        if base.is_Rational and base < 0:
            raise CertifyError(f"the amplitude factor {f}")
        if k.is_Rational and (2 * k).is_Integer:
            return Y.rt_d(self.dmon(base), int(2 * k)), []
        if k.free_symbols and (base.is_Integer or base in self.dsyms):
            e2 = sympy.expand(2 * k)
            if len(e2.free_symbols) == 1:
                n = next(iter(e2.free_symbols))
                poly = sympy.Poly(e2, n)
                cs = poly.all_coeffs()
                if poly.degree() == 1 and all(c.is_Integer for c in cs):
                    a, b = int(cs[0]), int(cs[1])
                    c0 = self.anchors.get((base, n), 0)
                    m = Y.rt_d(self.dmon(self.power(base, n + c0)), a)
                    return Y.cm_mul(m, Y.rt_d(self.dmon(base), b - a * c0)), []
        raise CertifyError(f"the amplitude factor {f}")


def exp_text(n: sympy.Expr) -> str:
    """A width exponent ``a n + b`` as Lean text over ``ℕ``."""
    if isinstance(n, sympy.Symbol):
        return str(n.name)
    (w,) = sympy.sympify(n).free_symbols
    a, b = (int(x) for x in sympy.Poly(n, w).all_coeffs())
    head = w.name if a == 1 else f"{a} * {w.name}"
    return f"({head} - {-b})" if b < 0 else f"({head} + {b})"


def prime_radicals(cm: Y.CMon) -> Y.CMon:
    """``cm`` with each constant radicand written as distinct primes, squares moved into the
    rational factor."""
    if not cm[3]:
        return cm
    q = cm[0]
    rc: tuple[int, ...] = ()
    for c in cm[3]:
        for p, e in sympy.factorint(c).items():
            q *= int(p) ** (e // 2)
            if e % 2:
                k, rc = Y.rc_ins(int(p), rc)
                q *= k
    return (q, cm[1], cm[2], rc, cm[4], cm[5])


# path sums read from syntax trees


@dataclass(frozen=True)
class Ket:
    """A ket built from a syntax tree: registers and terms ``(amp, sums, kets)``, each sum a
    symbol and its number of values from 0."""

    widths: tuple[sympy.Expr, ...]
    dims: tuple[sympy.Expr | None, ...]
    terms: tuple[
        tuple[sympy.Expr, tuple[tuple[sympy.Symbol, sympy.Expr], ...], tuple[sympy.Expr, ...]], ...
    ]


def _tensor(a: Ket, b: Ket) -> Ket:
    terms = tuple((x[0] * y[0], x[1] + y[1], x[2] + y[2]) for x in a.terms for y in b.terms)
    return Ket(a.widths + b.widths, a.dims + b.dims, terms)


def _merge(k: Ket) -> Ket | None:
    """``k`` with its registers, of one dimension, joined into one big-endian register."""
    if len(k.widths) <= 1:
        return k
    if any(w is None for w in k.widths) or any(d is None for d in k.dims):
        return None
    d = k.dims[0]
    if any(sympy.expand(x - d) != 0 for x in k.dims):  # type: ignore[operator]
        return None
    shifts = [sympy.Add(*k.widths[i + 1 :]) for i in range(len(k.widths))]
    terms = tuple(
        (t[0], t[1], (sympy.Add(*(v * d**sh for v, sh in zip(t[2], shifts, strict=True))),))
        for t in k.terms
    )
    return Ket((sympy.Add(*k.widths),), (d,), terms)


def _scale(c: sympy.Expr, k: Ket) -> Ket:
    return Ket(k.widths, k.dims, tuple((c * t[0], t[1], t[2]) for t in k.terms))


@dataclass(frozen=True)
class Slot:
    """A pattern variable in scope: its symbol, width and dimension."""

    symbol: sympy.Symbol
    width: sympy.Expr | None = None
    dim: sympy.Expr | None = None
    size: sympy.Expr | None = None


class Reader:
    """Evaluates the syntax trees of states and gate bodies into :class:`Ket` and sympy
    scalars, against a snapshot of the program's variables."""

    def __init__(
        self,
        parse: Callable[[str], object],
        values: Mapping[str, object],
        funcs: Mapping[str, Callable[..., sympy.Expr]] | None = None,
    ) -> None:
        self.parse = parse
        self.values = values
        self.funcs = funcs or {}

    def scalar(self, node: object, loc: Mapping[str, Slot]) -> sympy.Expr:
        v = self.eval(node, loc)
        if isinstance(v, Ket):
            raise CertifyError("a state where a scalar is expected")
        return v

    def eval(self, node: object, loc: Mapping[str, Slot]) -> sympy.Expr | Ket:
        from diracula import lang as L

        if isinstance(node, L.Num):
            return node.value
        if isinstance(node, L.Name):
            if node.id in loc:
                return loc[node.id].symbol
            if node.id in self.values:
                v = self.values[node.id]
                if isinstance(v, sympy.Basic):
                    return v
                raise CertifyError(f"{node.id} is not a scalar")
            consts = {"pi": sympy.pi, "e": sympy.E, "i": sympy.I}
            if node.id in consts:
                return consts[node.id]
            raise CertifyError(f"{node.id} is not a scalar")
        if isinstance(node, L.Neg):
            v = self.eval(node.arg, loc)
            return _scale(sympy.Integer(-1), v) if isinstance(v, Ket) else -v
        if isinstance(node, L.Call):
            fns = {"sqrt": sympy.sqrt, "exp": sympy.exp, **self.funcs}
            if node.name not in fns or node.name in ("rand", "arg", "normalise"):
                raise CertifyError(f"the function {node.name}")
            return fns[node.name](*(self.scalar(a, loc) for a in node.args))
        if isinstance(node, L.SumNode):
            lo = self.scalar(node.lo, loc)
            hi = self.scalar(node.hi, loc) + (1 if node.inclusive else 0)
            if lo != 0:
                raise CertifyError("a sum that does not start at 0")
            s = sympy.Dummy(node.var, integer=True)
            body = self.eval(node.body, {**loc, node.var: Slot(s, size=hi)})
            if not isinstance(body, Ket):
                if not (hi.is_Integer and int(hi) <= UNROLL):
                    raise CertifyError("a scalar sum over a symbolic range")
                return sympy.Add(*(body.xreplace({s: sympy.Integer(j)}) for j in range(int(hi))))
            return Ket(
                body.widths, body.dims, tuple((t[0], ((s, hi),) + t[1], t[2]) for t in body.terms)
            )
        if isinstance(node, L.Braket):
            if node.bra:
                raise CertifyError("a bra inside a state")
            return self.ket(node, loc)
        if isinstance(node, L.VectorNode):
            amps = [self.scalar(e, loc) for e in node.items]
            w, d = L._matrix_layout(sympy.Integer(len(amps)))
            terms = tuple((a, (), (sympy.Integer(k),)) for k, a in enumerate(amps) if a != 0)
            return Ket((w,), (d,), terms or ((sympy.Integer(0), (), (sympy.Integer(0),)),))
        if isinstance(node, L.Juxt) or (isinstance(node, L.Bin) and node.op in ("@", "*")):
            a, b = self.eval(node.left, loc), self.eval(node.right, loc)
            if isinstance(a, Ket) and isinstance(b, Ket):
                if isinstance(node, L.Bin) and node.op == "*":
                    raise CertifyError("a product of states")
                return _tensor(a, b)
            if isinstance(a, Ket):
                return _scale(b, a)
            if isinstance(b, Ket):
                return _scale(a, b)
            return a * b
        if isinstance(node, L.Bin):
            a, b = self.eval(node.left, loc), self.eval(node.right, loc)
            if node.op in ("+", "-") and isinstance(a, Ket) and isinstance(b, Ket):
                if a.widths != b.widths or a.dims != b.dims:
                    ma, mb = _merge(a), _merge(b)
                    if ma is None or mb is None:
                        raise CertifyError("a sum of states of different layouts")
                    a, b = ma, mb
                if a.widths != b.widths or a.dims != b.dims:
                    raise CertifyError("a sum of states of different layouts")
                if node.op == "-":
                    b = _scale(sympy.Integer(-1), b)
                return Ket(a.widths, a.dims, a.terms + b.terms)
            if node.op == "^@" and isinstance(a, Ket):
                return self.power(a, b)
            if isinstance(a, Ket) or isinstance(b, Ket):
                if node.op == "/" and isinstance(a, Ket):
                    return _scale(1 / b, a)  # type: ignore[operator]
                raise CertifyError(f"the operator {node.op} on a state")
            ops: dict[str, Callable[[Any, Any], Any]] = {
                "xor": self.funcs.get("xor", lambda x, y: sympy.Function("xor")(x, y)),
                "+": lambda x, y: x + y,
                "-": lambda x, y: x - y,
                "/": lambda x, y: x / y,
                "^": lambda x, y: x**y,
                "%": sympy.Mod,
            }
            if node.op not in ops:
                raise CertifyError(f"the operator {node.op}")
            return ops[node.op](a, b)
        raise CertifyError(f"the expression {type(node).__name__}")

    def power(self, a: Ket, n: sympy.Expr) -> Ket:
        if len(a.widths) != 1 or len(a.terms) != 1 or a.terms[0][1] or a.widths[0] not in (1, None):
            raise CertifyError("a tensor power of a state other than one basis qudit")
        a = Ket((sympy.Integer(1),), a.dims, a.terms)
        amp, _, (v,) = a.terms[0]
        if amp != 1:
            raise CertifyError("a tensor power of a scaled basis state")
        if v == 0:
            return Ket((n,), a.dims, ((sympy.Integer(1), (), (sympy.Integer(0),)),))
        d = a.dims[0] if a.dims[0] is not None else sympy.Integer(2)
        return Ket((n,), a.dims, ((sympy.Integer(1), (), (v * (d**n - 1) / (d - 1),)),))

    def ket(self, node: object, loc: Mapping[str, Slot]) -> Ket:
        from diracula import lang as L

        assert isinstance(node, L.Braket)
        content = node.content.strip()
        dim = None if node.dim is None else self.scalar(self.parse(node.dim), loc)
        if len(content) > 1 and content.endswith("`") and content[:-1].isdigit():
            parts = [
                self.basis(sympy.Integer(int(c)), None, dim, explicit=dim is not None)
                for c in content[:-1]
            ]
            out = parts[0]
            for p in parts[1:]:
                out = _tensor(out, p)
            return out
        if content in _BUILTIN_KETS and dim is None:
            c = _BUILTIN_KETS[content]
            half = 1 / sympy.sqrt(2)
            return Ket(
                (sympy.Integer(1),),
                (sympy.Integer(2),),
                ((half, (), (sympy.Integer(0),)), (c * half, (), (sympy.Integer(1),))),
            )
        ast = self.parse(content)
        value = self.scalar(ast, loc)
        slot = loc.get(ast.id) if isinstance(ast, L.Name) else None
        return self.basis(value, slot, dim, explicit=dim is not None)

    def basis(
        self, value: sympy.Expr, slot: Slot | None, dim: sympy.Expr | None, explicit: bool
    ) -> Ket:
        if dim is None and slot is not None and slot.dim is not None:
            dim = slot.dim
        width: sympy.Expr | None = None
        if slot is not None and slot.width is not None:
            width = slot.width
        elif slot is not None and slot.size is not None:
            d = dim if dim is not None else sympy.Integer(2)
            if sympy.expand(slot.size - d) == 0:
                width = sympy.Integer(1)
        elif explicit:
            width = sympy.Integer(1)
        return Ket((width,), (dim,), ((sympy.Integer(1), (), (value,)),))


def fix_layout(k: Ket, widths: Sequence[sympy.Expr], dims: Sequence[sympy.Expr]) -> Ket:
    """``k`` laid out on ``widths`` and ``dims``; its unresolved registers take them."""
    if len(k.widths) != len(widths):
        raise CertifyError("the registers do not match the engine's layout")
    for w, d, w2, d2 in zip(k.widths, k.dims, widths, dims, strict=True):
        if w is not None and sympy.expand(w - w2) != 0:
            raise CertifyError("a register width does not match the engine's layout")
        if d is not None and sympy.expand(d - d2) != 0:
            raise CertifyError("a register dimension does not match the engine's layout")
    return Ket(tuple(widths), tuple(dims), k.terms)


def P_pop(x: sympy.Expr) -> sympy.Expr:
    """The number of ones in the binary digits of ``x``."""
    from diracula import pathsum as P

    return P.pop(x)


def integer_index(c: sympy.Expr) -> bool:
    """Whether ``c`` is a polynomial with integer coefficients in integer symbols and integer
    functions."""
    try:
        poly = sympy.Poly(sympy.expand(c))
    except sympy.PolynomialError:
        return False
    return all(x.is_Integer for x in poly.coeffs()) and all(g.is_integer for g in poly.gens)


def term_atoms(vs: Vars, facs: Sequence[Y.Fac]) -> tuple[Atom, ...]:
    """The atoms the factors read, with the atoms those read, in creation order."""
    need = {v for f in facs for v in Z.ip_vs(f[1]) if v >= AID}
    grew = True
    while grew:
        grew = False
        for a in vs.atoms:
            if a[0] in need:
                for v in Z.at_vs(a):
                    if v >= AID and v not in need:
                        need.add(v)
                        grew = True
    return tuple(a for a in vs.atoms if a[0] in need)


UNROLL = 4096
"""The largest number of terms a concrete sum is written out as."""


def unrolled(vs: Vars, terms: Sequence[Any]) -> list[Any]:
    """The terms, each whose amplitude is outside the amplitude grammar and sums over concrete
    ranges written out term by term."""
    import copy
    import itertools

    out = []
    for amp, sums, kets in terms:
        probe = copy.deepcopy(vs)
        try:
            for s, n in sums:
                probe.bound(s, n)
            probe.amp(amp)
            out.append((amp, sums, kets))
            continue
        except CertifyError:
            pass
        small = [(s, n) for s, n in sums if n.is_Integer and int(n) <= UNROLL and amp.has(s)]
        if not small or sympy.prod([n for _, n in small]) > UNROLL:
            out.append((amp, sums, kets))
            continue
        keep = tuple(p for p in sums if p not in small)
        for vals in itertools.product(*(range(int(n)) for _, n in small)):
            sub = {s: sympy.Integer(v) for (s, _), v in zip(small, vals, strict=True)}
            out.append(
                (amp.xreplace(sub), keep, tuple(sympy.sympify(x).xreplace(sub) for x in kets))
            )
    return out


def ket_terms(vs: Vars, k: Ket) -> list[ATm]:
    """``Σ amp Π_i [L_i ∣ o_i - v_i]``, output register ``i`` at variable ``i``."""
    lexprs = [d**w for w, d in zip(k.widths, k.dims, strict=True)]
    levels = [vs.dmon(x) for x in lexprs]
    for i, x in enumerate(lexprs):
        vs.ranges[i] = x
    saved = vs.default
    vs.default = lexprs[0] if len(lexprs) == 1 else None
    try:
        return ket_terms_core(vs, k, lexprs, levels)
    finally:
        vs.default = saved


def unfold_user(v: sympy.Expr) -> sympy.Expr:
    """``v`` with each user function whose body is a case split replaced by that body."""
    v = sympy.sympify(v)
    body = getattr(type(v), "_body", None)
    if isinstance(v, sympy.Function) and body is not None:
        u = body.xreplace(dict(zip(type(v)._params, v.args, strict=True)))
        if isinstance(u, sympy.Piecewise):
            return u
    return v


def case_split(vs: Vars, k: Any, lx: Any) -> tuple[Any, Any, Any] | None:
    """``(A, B, y)`` of a ket ``ifelse(y < L - 1, A, B)`` with ``y`` reduced modulo ``L``."""
    v = unfold_user(k)
    if not isinstance(v, sympy.Piecewise) or len(v.args) != 2 or v.args[1][1] != sympy.true:
        return None
    (a, cond), (b, _) = v.args
    if not isinstance(cond, (sympy.StrictLessThan, sympy.StrictGreaterThan)):
        return None
    y = sympy.expand(lx - 1 - (cond.gts - cond.lts))
    reduced = (isinstance(y, sympy.Mod) and sympy.expand(y.args[1] - lx) == 0) or (
        vs.known_range(y) is not None and sympy.expand(vs.known_range(y) - lx) == 0
    )
    return (a, b, y) if reduced else None


def pieces(
    vs: Vars, kets: Sequence[Any], lexprs: Sequence[Any]
) -> list[tuple[int, tuple[Any, ...], list[Y.Fac]]]:
    """The kets with each case split ``ifelse(y < L - 1, A, B)`` on a register of ``L`` levels
    written as ``A - [L ∣ y + 1] A + [L ∣ y + 1] B``: sign, kets and the extra deltas; a user
    function of one argument is read on its argument modulo ``L``."""
    out: list[tuple[int, tuple[Any, ...], list[Y.Fac]]] = [(1, tuple(kets), [])]
    for i, lx in enumerate(lexprs):
        nxt = []
        for sg, ks, extra in out:
            k0 = sympy.sympify(ks[i])
            if not isinstance(unfold_user(k0), sympy.Piecewise):
                nxt.append((sg, ks, extra))
                continue
            c = case_split(vs, k0, lx)
            if c is None and not isinstance(k0, sympy.Piecewise) and len(k0.args) == 1:
                c = case_split(vs, k0.func(sympy.Mod(k0.args[0], lx)), lx)
            if c is None:
                raise CertifyError(f"the piecewise value {unfold_user(k0)}")
            a, b, y = c
            dc = (vs.dmon(lx), vs.ipoly(y + 1))
            ka = ks[:i] + (a,) + ks[i + 1 :]
            kb = ks[:i] + (b,) + ks[i + 1 :]
            nxt += [(sg, ka, extra), (-sg, ka, extra + [dc]), (sg, kb, extra + [dc])]
        out = nxt
    return out


def ket_terms_core(vs: Vars, k: Ket, lexprs: list[Any], levels: list[Y.DMon]) -> list[ATm]:
    """``ket_terms`` with the registers' levels found."""
    out: list[ATm] = []
    for amp0, sums, kets0 in unrolled(vs, k.terms):
        for sg, kets, extra in pieces(vs, kets0, lexprs):
            amp = amp0 if sg == 1 else -amp0
            bound = tuple((vs.bound(s, n), vs.dmon(n)) for s, n in sums)
            dels = list(extra)
            for i, (v, lv, lx) in enumerate(zip(kets, levels, lexprs, strict=True)):
                if isinstance(v, sympy.Mod) and sympy.expand(v.args[1] - lx) == 0:
                    v = v.args[0]
                dels.append((lv, Y.ip_sub(Y.ip_v(i), vs.ipoly(v, lx))))
            for cm, adels, phs, aps in vs.amp(amp):
                facs = dels + adels + phs
                out.append((cm, bound, term_atoms(vs, facs), tuple(dels + adels), tuple(phs), aps))
    return out


def scalar_terms(vs: Vars, v: sympy.Expr) -> list[ATm]:
    """A scalar as constant terms."""
    out: list[ATm] = []
    for cm, dels, phs, aps in vs.amp(v):
        out.append((cm, (), term_atoms(vs, dels + phs), tuple(dels), tuple(phs), aps))
    return out


def state_terms(vs: Vars, s: State) -> list[ATm]:
    """A printed state as an expression."""
    terms = []
    for t in s.terms:
        sums = []
        for b in t.bound:
            if b.lo != 0:
                raise CertifyError("a printed sum that does not start at 0")
            sums.append((b.symbol, b.hi + 1))
            vs.bound(b.symbol, b.hi + 1)
        terms.append((t.amp, tuple(sums), t.kets))
    widths = tuple(w for w in s.widths)
    dims = tuple(d for d in s.dims)
    return ket_terms(vs, Ket(widths, dims, tuple(terms)))


# checking


def _lake() -> str | None:
    found = shutil.which("lake")
    home = os.path.expanduser("~/.elan/bin/lake")
    return found or (home if os.path.exists(home) else None)


def lean_project() -> str:
    """The bundled Lean project's directory."""
    return os.path.join(os.path.dirname(__file__), "lean")


def check_file(path: str) -> tuple[bool, str]:
    """``lake env lean path`` inside the bundled Lean project: ``(accepted, output)``."""
    lake = _lake()
    if lake is None:
        return False, "Lean (lake) is not installed"
    done = subprocess.run(
        [lake, "env", "lean", os.path.abspath(path)],
        cwd=lean_project(),
        capture_output=True,
        text=True,
        check=False,
    )
    text = (done.stdout + done.stderr).strip()
    bad = done.returncode != 0 or "error" in text or "sorry" in text
    lines = text.splitlines()
    errors = [i for i, x in enumerate(lines) if "error" in x or "sorry" in x]
    shown = [x for i in errors for x in lines[i : i + 4]][:40]
    return not bad, "\n".join(shown) if bad else text


def lean_nat(e: sympy.Expr, names: Mapping[sympy.Symbol, str]) -> str:
    """A natural-number expression with floors as Lean text."""
    e = sympy.sympify(e)
    if e.is_Integer:
        return str(int(e))
    if isinstance(e, sympy.Symbol):
        if e not in names:
            raise CertifyError(f"the outcome expression {e}")
        return names[e]
    if isinstance(e, sympy.Add):
        return "(" + " + ".join(lean_nat(a, names) for a in e.args) + ")"
    if isinstance(e, sympy.Mul):
        num, den = sympy.fraction(e)
        if den != 1:
            return f"({lean_nat(num, names)} / {lean_nat(den, names)})"
        return "(" + " * ".join(lean_nat(a, names) for a in e.args) + ")"
    if isinstance(e, sympy.Pow) and e.exp.is_Integer and int(e.exp) > 0:
        return f"({lean_nat(e.base, names)} ^ {int(e.exp)})"
    if isinstance(e, sympy.Pow) and isinstance(e.exp, sympy.Symbol) and e.exp in names:
        return f"({lean_nat(e.base, names)} ^ {names[e.exp]})"
    if isinstance(e, sympy.floor):
        num, den = sympy.fraction(sympy.together(e.args[0]))
        return f"({lean_nat(sympy.expand(num), names)} / {lean_nat(den, names)})"
    if isinstance(e, sympy.Mod) and e.args[1].is_Integer:
        return f"({lean_nat(e.args[0], names)} % {int(e.args[1])})"
    raise CertifyError(f"the outcome expression {e}")


def lean_rat(e: sympy.Expr, names: Mapping[sympy.Symbol, str]) -> str:
    """A rational expression over natural numbers and their floors as Lean text over ``ℚ``."""
    e = sympy.sympify(e)
    if e.is_Integer:
        return f"({int(e)} : ℚ)"
    if e.is_Rational:
        return f"(({e.p} : ℚ) / {e.q})"
    if isinstance(e, sympy.Add):
        return "(" + " + ".join(lean_rat(a, names) for a in e.args) + ")"
    if isinstance(e, sympy.Mul):
        num, den = sympy.fraction(e)
        if den != 1:
            return f"({lean_rat(num, names)} / {lean_rat(den, names)})"
        return "(" + " * ".join(lean_rat(a, names) for a in e.args) + ")"
    return f"(({lean_nat(e, names)} : ℕ) : ℚ)"


def true_div(e: sympy.Expr) -> bool:
    """Whether ``e`` divides outside its floors."""
    e = sympy.sympify(e)
    e = e.xreplace({f: sympy.Dummy("f", integer=True) for f in e.atoms(sympy.floor)})
    return bool(sympy.fraction(sympy.together(e))[1] != 1)


def pos_c(t: ATm) -> bool:
    """Whether a term is a coefficient alone whose value is a positive real (``posC``)."""
    c = t[0]
    return (
        t[1:] == ((), (), (), (), ())
        and c[1] == 0
        and c[4] == ()
        and c[5] == ()
        and c[0] > 0
        and all(x > 0 for x in c[3])
    )


DECIDES = "(by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)"


MINUS = Prog("leaf", ([(Y.of_q(-1), (), (), (), (), ())],))


# the certifier


Layout = tuple[tuple[sympy.Expr, ...], tuple[sympy.Expr, ...]]


@dataclass(frozen=True)
class Event:
    """A recorded state update: ``assign`` (``nodes`` is the right side), ``apply``
    (``nodes`` are the operators applied in place, outermost first) or ``opaque`` (``source``
    says what was not recorded); ``value`` is the state after it and ``values`` the variables
    then."""

    kind: str
    name: str
    nodes: tuple[object, ...]
    source: str
    value: object
    values: Mapping[str, object]


@dataclass(frozen=True)
class GateTree:
    """A gate's pattern slots, body syntax tree and source line."""

    slots: tuple[tuple[str, str | None], ...]
    body: object
    source: str


_BUILTIN_KETS = {"+": sympy.Integer(1), "-": sympy.Integer(-1), "i": sympy.I, "-i": -sympy.I}


def _clean(name: str) -> str:
    return "".join(c if c.isalnum() or c == "_" else "_" for c in name)


class Certifier:
    """Builds the certificate of one result from an interpreter's recorded trees."""

    def __init__(
        self,
        trees: Mapping[str, GateTree],
        log: Sequence[Event],
        parse: Callable[[str], object],
        script: str,
        funcs: Mapping[str, Callable[..., sympy.Expr]] | None = None,
    ) -> None:
        self.trees = trees
        self.log = list(log)
        self.parse = parse
        self.script = _clean(script) if script[:1].isalpha() else f"s_{_clean(script)}"
        self.funcs = funcs or {}
        self.upto = 0
        self.assumptions: list[sympy.Basic] = []
        self.outcome_fn: Callable[[sympy.Expr], sympy.Expr] = lambda v: v
        self.norms: Mapping[int, Sequence[sympy.Expr]] = {}
        self.nrm_obls: list[tuple[Prog, list[Y.DMon], ATm, sympy.Expr]] = []
        self.side_obls: list[tuple[str, Prog, list[ATm]]] = []
        """Theorems a translation relies on: a title, a program and its value."""
        self.channels: Mapping[str, object] = {}
        self.aliases: Mapping[str, object] = {}
        """Each gate named by an operator expression: that expression's tree."""
        """Each channel's defining syntax tree."""
        self.hooks: dict[str, Callable[..., Any]] = {}
        """Engine values a translation needs: ``layout`` of an operator tree, ``power`` the state
        ``A^J |s>`` for a symbolic ``J``."""
        self.vs = Vars()
        self.decls: list[tuple[str, Prog]] = []
        self.wl_used: list[tuple[int, Y.DMon, Y.DMon]] = []
        self.ctx_any = False
        self.ctx_used = False
        self.real_rs: list[int] = []
        self.real_any: list[int] = []
        self.real_kind = "real"
        """Whether the atoms of ``real_rs`` are real or of modulus 1."""
        self.unit_any: list[int] = []
        self.gate_layouts: dict[object, Layout] = {}
        self.rounds = 1
        self.nfs2: list[ATm | None] = []
        self.done: dict[object, Prog] = {}
        self.text = Text()

    # names and declarations

    def declare(self, key: object, base: str, comment: str, p: Prog) -> Prog:
        names = {q.name for q in self.done.values()}
        name, k = base, 1
        while name in names:
            k += 1
            name = f"{base}_{k}"
        named = Prog(p.kind, p.args, name)
        self.done[key] = named
        self.decls.append((comment, named))
        return named

    # the left side

    def kind(self, node: object) -> str:
        from diracula import lang as L

        if isinstance(node, (L.MatrixNode, L.MatrixFor)):
            return "op"
        if isinstance(node, L.Name):
            if node.id in self.aliases:
                return "op"
            return "op" if node.id in self.trees or node.id == "I" else "scalar"
        if isinstance(node, L.Braket):
            return "bra" if node.bra else "ket"
        if isinstance(node, L.SumNode):
            return self.kind(node.body)
        if isinstance(node, L.Neg):
            return self.kind(node.arg)
        if isinstance(node, L.Juxt) or (isinstance(node, L.Bin) and node.op in ("*", "/")):
            a, b = self.kind(node.left), self.kind(node.right)
            if a == "scalar":
                return b
            if b == "scalar":
                return a
            if (a, b) == ("bra", "ket"):
                return "scalar"
            if (a, b) in (("op", "op"), ("ket", "bra")):
                return "op"
            return "ket" if b == "ket" else a
        if isinstance(node, L.Bin) and node.op in ("@", "^@", "+", "-"):
            return self.kind(node.left)
        if isinstance(node, L.Call) and node.name == "normalise" and len(node.args) == 1:
            return self.kind(node.args[0])
        if isinstance(node, L.Call) and node.name == "adj" and len(node.args) == 1:
            inner = self.kind(node.args[0])
            return {"ket": "bra", "bra": "ket"}.get(inner, inner)
        if isinstance(node, L.Call) and node.name == "inv" and len(node.args) == 1:
            return self.kind(node.args[0])
        if (
            isinstance(node, L.Call)
            and node.name in ANALYTIC
            and len(node.args) == 1
            and self.kind(node.args[0]) == "op"
        ):
            return "op"
        if isinstance(node, L.Bin) and node.op == "^" and self.kind(node.left) == "op":
            return "op"
        return "scalar"

    def named(self, node: object) -> bool:
        """Whether ``node`` reads a named state or applies an operator."""
        from diracula import lang as L

        if isinstance(node, L.Braket):
            return self.is_state(node.content.strip())
        if isinstance(node, L.Name):
            return self.kind(node) == "op"
        if isinstance(node, L.Call) and (node.name in ("adj", "inv") or node.name in ANALYTIC):
            return any(self.named(a) for a in node.args)
        children = [getattr(node, f) for f in ("left", "right", "arg", "body") if hasattr(node, f)]
        return any(self.named(c) for c in children)

    def bra_only(self, node: object) -> bool:
        """Whether ``node`` is a bra or a tensor product of bras."""
        from diracula import lang as L

        if isinstance(node, L.Braket):
            return node.bra
        if isinstance(node, L.Bin) and node.op == "@":
            return self.bra_only(node.left) and self.bra_only(node.right)
        return False

    def flip(self, node: object) -> object:
        """The ket of a bra or of a tensor product of bras."""
        from diracula import lang as L

        if isinstance(node, L.Braket):
            return L.Braket(node.content, False, node.dim)
        assert isinstance(node, L.Bin)
        return L.Bin("@", self.flip(node.left), self.flip(node.right))

    def has_bra(self, node: object) -> bool:
        """Whether ``node`` contains a bra."""
        from diracula import lang as L

        if isinstance(node, L.Braket):
            return node.bra
        children = [getattr(node, f) for f in ("left", "right", "arg", "body") if hasattr(node, f)]
        return any(self.has_bra(c) for c in children)

    def is_state(self, name: str) -> bool:
        return any(e.name == name for e in self.log[: self.upto])

    def layout_of(self, value: object) -> Layout:
        if not isinstance(value, State):
            raise CertifyError("a density matrix")
        if any(w is None or d is None for w, d in zip(value.widths, value.dims, strict=True)):
            raise CertifyError("an unresolved register")
        return tuple(value.widths), tuple(value.dims)

    def levels(self, lay: Layout) -> list[Y.DMon]:
        return [self.vs.dmon(d**w) for w, d in zip(*lay, strict=True)]

    def state(self, index: int) -> tuple[Prog, Layout]:
        """The program of the state after event ``index``."""
        ev = self.log[index]
        if index in self.done:
            return self.done[index], self.layout_of(ev.value)
        if ev.kind == "opaque":
            raise CertifyError(ev.source)
        saved = self.upto
        saved_reader = getattr(self, "reader", None)
        self.upto = index
        self.reader = Reader(self.parse, ev.values, self.funcs)
        try:
            lay = self.layout_of(ev.value)
            if ev.kind == "assign":
                p, got = self.expr(ev.nodes[0], lay)
            elif ev.kind == "loop":
                p, got = self.loop(ev, index)
            else:
                prev = self.previous(ev.name, index)
                p, got = self.state(prev)
                for pos, op in enumerate(reversed(ev.nodes)):
                    cnt = self.symbolic_count(op)
                    if cnt is not None and pos == 0:
                        p = self.power_loop(op.left, cnt, p, got, self.log[prev].value)  # type: ignore[attr-defined]
                        continue
                    q, out = self.op(op, got)
                    p, got = Prog("app", (self.levels(got), q, p)), out
        finally:
            self.upto = saved
            if saved_reader is not None:
                self.reader = saved_reader
        self.match(got, lay)
        return self.declare(index, f"state_{_clean(ev.name)}", ev.source, p), lay

    def loop(self, ev: Event, index: int) -> tuple[Prog, Layout]:
        """A loop over a symbolic range whose body updates the state by operators applied to
        it: the loop node with the engine's invariant."""
        from diracula import lang as L

        body, var_sym, lo, hi, invariant = ev.nodes
        if var_sym not in self.vs.loops:
            self.vs.loops.append(cast(sympy.Symbol, var_sym))
        try:
            inv = invariant()  # type: ignore[operator]
        except Exception as exc:
            raise CertifyError(f"the loop has no closed-form invariant: {exc}") from exc
        init, lay = self.state(self.previous(ev.name, index))
        self.reader = Reader(self.parse, ev.values, self.funcs)
        ops: list[object] = []
        node = body
        while isinstance(node, L.Juxt):
            ops.append(node.left)
            node = node.right
        if not (
            ops and isinstance(node, L.Braket) and not node.bra and node.content.strip() == ev.name
        ):
            raise CertifyError("a loop body other than operators applied to the updated state")
        step, out = self.op(ops[-1], lay)
        for o in reversed(ops[:-1]):
            q, mid = self.op(o, out)
            step, out = Prog("app", (self.levels(out), q, step)), mid
        self.match(out, lay)
        if not (sympy.sympify(lo).is_Integer):
            raise CertifyError("a loop whose range does not start at an integer")
        lo_e, hi_e = sympy.sympify(lo), sympy.sympify(hi)
        j = self.vs.var(cast(sympy.Basic, var_sym))
        cnt = self.vs.count(sympy.expand(hi_e + 1 - lo_e))
        inv_terms = state_terms(self.vs, self.reduced_params(cast(State, inv), var_sym))
        return Prog(
            "loop", (self.levels(lay), j, int(lo_e), cnt, step, init, inv_terms, (), ())
        ), lay

    def reduced_params(self, inv: State, j: Any) -> State:
        """The invariant with each parameter in a case-split ket read modulo the register's
        levels."""
        from diracula import pathsum as P

        if not any(isinstance(v, sympy.Piecewise) for t in inv.terms for v in t.kets):
            return inv
        terms = []
        for t in inv.terms:
            bound = {b.symbol for b in t.bound}
            kets = []
            for v, w, d in zip(t.kets, inv.widths, inv.dims, strict=True):
                lx = cast(sympy.Expr, d) ** w
                sub = {
                    q: sympy.Mod(q, lx)
                    for q in sympy.sympify(v).free_symbols
                    if isinstance(q, sympy.Symbol)
                    and q.is_integer
                    and q not in bound
                    and q != j
                    and q not in self.vs.dsyms
                    and q not in self.vs.widths
                }
                kets.append(sympy.sympify(v).xreplace(sub) if isinstance(v, sympy.Piecewise) else v)
            terms.append(P.Term(t.amp, t.bound, tuple(kets)))
        return P.State(inv.widths, tuple(terms), inv.bra, inv.dims)

    def previous(self, name: str, index: int) -> int:
        for k in range(index - 1, -1, -1):
            if self.log[k].name == name:
                return k
        raise CertifyError(f"|{name}> is not defined")

    @staticmethod
    def match(got: Layout, want: Layout) -> None:
        for a, b in zip(got[0] + got[1], want[0] + want[1], strict=True):
            if sympy.expand(a - b) != 0:
                raise CertifyError("the registers differ from the engine's layout")

    def leaf(self, node: object, want: Layout | None) -> tuple[Prog, Layout]:
        k = self.reader.eval(node, {})
        if not isinstance(k, Ket):
            raise CertifyError("a scalar where a state is expected")
        if want is not None and len(want[0]) == 1 and len(k.widths) > 1:
            k = _merge(k) or k
        if want is not None and len(want[0]) == len(k.widths):
            k = fix_layout(k, *want)
        else:
            k = fix_layout(
                k,
                [w if w is not None else sympy.Integer(1) for w in k.widths],
                [d if d is not None else sympy.Integer(2) for d in k.dims],
            )
        return Prog("leaf", (ket_terms(self.vs, k),)), (k.widths, k.dims)

    def normalised(self, node: Any, want: Layout | None) -> tuple[Prog, Layout]:
        """``normalise(s)`` as ``k s`` for ``k = 1/norm`` of the run, with the obligation
        ``k² <s|s> = 1`` proved in the same file."""
        norms: list[sympy.Expr] = []
        for x in self.norms.get(id(node), []):
            if not any(sympy.simplify(x - y) == 0 for y in norms):
                norms.append(x)
        if len(norms) != 1:
            raise CertifyError("normalise of a state whose norm the run does not fix")
        p, lay = self.expr(node.args[0], want)
        kt = scalar_terms(self.vs, 1 / norms[0])
        if len(kt) != 1 or not pos_c(kt[0]):
            raise CertifyError(f"the norm {norms[0]}")
        i = len(self.nrm_obls)
        psi = self.declare(("nrm_s", i), f"nstate_{i}", f"the argument of normalise #{i}", p)
        self.nrm_obls.append((psi, self.levels(lay), kt[0], norms[0]))
        return Prog("mul", (Prog("leaf", ([kt[0]],)), psi)), lay

    def scalar_leaf(self, node: object) -> Prog:
        return Prog("leaf", (scalar_terms(self.vs, self.reader.scalar(node, {})),))

    def scalar_prog(self, node: object) -> Prog:
        """A scalar-valued tree."""
        from diracula import lang as L

        if isinstance(node, L.Call) and node.name == "tr" and len(node.args) == 1:
            arg = node.args[0]
            if self.kind(arg) == "op":
                if "layout" not in self.hooks:
                    raise CertifyError("the trace of an operator of unknown registers")
                pairs = self.hooks["layout"](arg)
                lay = (tuple(w for w, _ in pairs), tuple(d for _, d in pairs))
                q, out = self.op(arg, lay)
                self.match(out, lay)
                return self.op_trace(q, lay)
            if self.mixed_valued(arg):
                v, lay = self.dens(arg)
                return self.diag_sum(v, lay, len(lay[0]))
            p, lay = self.expr(arg)
            return Prog("inn", (self.levels(lay), p, p))

        if not self.named(node) and not self.has_bra(node):
            return self.scalar_leaf(node)
        if isinstance(node, L.Juxt) and self.kind(node.left) == "bra" and self.bra_only(node.left):
            ket = self.flip(node.left)
            pb, lb = self.expr(node.right)
            pa, la = self.expr(ket, lb)
            self.match(la, lb)
            return Prog("inn", (self.levels(la), pa, pb))
        if isinstance(node, L.Juxt) or (isinstance(node, L.Bin) and node.op == "*"):
            return Prog("mul", (self.scalar_prog(node.left), self.scalar_prog(node.right)))
        if isinstance(node, L.Bin) and node.op in ("+", "-"):
            q = self.scalar_prog(node.right)
            if node.op == "-":
                q = Prog("mul", (MINUS, q))
            return Prog("add", (self.scalar_prog(node.left), q))
        if isinstance(node, L.Neg):
            return Prog("mul", (MINUS, self.scalar_prog(node.arg)))
        if isinstance(node, L.Name):
            raise CertifyError(
                f"{node.id} is not a scalar; only scalar and state equations are certified"
            )
        raise CertifyError(f"the scalar expression {type(node).__name__}")

    def expr(self, node: object, want: Layout | None = None) -> tuple[Prog, Layout]:
        """A state-valued tree."""
        from diracula import lang as L

        if isinstance(node, L.Call) and node.name == "normalise" and len(node.args) == 1:
            return self.normalised(node, want)
        if not self.named(node):
            return self.leaf(node, want)
        if isinstance(node, L.Braket) and not node.bra:
            return self.state(self.previous(node.content.strip(), self.upto))
        if isinstance(node, L.Juxt) or (isinstance(node, L.Bin) and node.op in ("*", "/")):
            ka, kb = self.kind(node.left), self.kind(node.right)
            if isinstance(node, L.Juxt) and ka == "op" and kb == "ket":
                p, lay = self.expr(node.right)
                cnt = self.symbolic_count(node.left)
                if cnt is not None:
                    init_value = self.hooks["value"](node.right) if "value" in self.hooks else None
                    base = cast(Any, node.left).left
                    return self.power_loop(base, cnt, p, lay, init_value), lay
                q, out = self.op(node.left, lay)
                return Prog("app", (self.levels(lay), q, p)), out
            if (
                ka == "scalar" and kb == "ket" and node.op != "/"
                if isinstance(node, L.Bin)
                else ka == "scalar" and kb == "ket"
            ):
                p, lay = self.expr(node.right, want)
                return Prog("mul", (self.scalar_prog(node.left), p)), lay
            if ka == "ket" and kb == "scalar":
                p, lay = self.expr(node.left, want)
                if isinstance(node, L.Bin) and node.op == "/":
                    s = L.Bin("/", L.Num(sympy.Integer(1)), node.right)
                    return Prog("mul", (self.scalar_leaf(s), p)), lay
                return Prog("mul", (self.scalar_prog(node.right), p)), lay
            if ka == "ket" and kb == "ket" and isinstance(node, L.Juxt):
                return self.tensor(node.left, node.right)
            raise CertifyError(f"juxtaposing a {ka} and a {kb}")
        if isinstance(node, L.Bin) and node.op == "@":
            return self.tensor(node.left, node.right)
        if isinstance(node, L.Bin) and node.op in ("+", "-"):
            p, lay = self.expr(node.left, want)
            q, lay2 = self.expr(node.right, lay)
            self.match(lay2, lay)
            if node.op == "-":
                q = Prog("mul", (MINUS, q))
            return Prog("add", (p, q)), lay
        if isinstance(node, L.Neg):
            p, lay = self.expr(node.arg, want)
            return Prog("mul", (MINUS, p)), lay
        if isinstance(node, L.SumNode):
            lo = self.reader.scalar(node.lo, {})
            hi = self.reader.scalar(node.hi, {}) + (1 if node.inclusive else 0)
            if lo != 0:
                raise CertifyError("a sum that does not start at 0")
            s = sympy.Dummy(node.var, integer=True)
            x = self.vs.bound(s, hi)
            saved = self.reader.values
            self.reader.values = {**saved, node.var: s}
            try:
                p, lay = self.expr(node.body, want)
            finally:
                self.reader.values = saved
            return Prog("sum", (self.vs.dmon(hi), x, p)), lay
        raise CertifyError(f"the state expression {type(node).__name__}")

    def tensor(self, a: object, b: object) -> tuple[Prog, Layout]:
        p, la = self.expr(a)
        q, lb = self.expr(b)
        return Prog("ten", (len(la[0]), p, q)), (la[0] + lb[0], la[1] + lb[1])

    def op(self, node: object, lay: Layout) -> tuple[Prog, Layout]:
        """An operator-valued tree acting on registers of layout ``lay``."""
        from diracula import lang as L

        if isinstance(node, L.Name) and node.id == "I":
            return self.ident(lay), lay
        if isinstance(node, L.Name) and node.id in self.aliases:
            return self.op(self.aliases[node.id], lay)
        if isinstance(node, (L.MatrixNode, L.MatrixFor)):
            self.anon = getattr(self, "anon", 0) + 1
            name = f"matrix_{self.anon}"
            return self.matrix_gate(name, GateTree((), node, name), lay)
        if isinstance(node, L.Name):
            return self.gate(node.id, lay)
        if isinstance(node, L.Bin) and node.op == "@":
            return self.op_tensor(self.factors(node), lay)
        if isinstance(node, L.Juxt) or (isinstance(node, L.Bin) and node.op == "*"):
            ka, kb = self.kind(node.left), self.kind(node.right)
            if ka == "op" and kb == "op":
                q, mid = self.op(node.right, lay)
                p, out = self.op(node.left, mid)
                return Prog("app", (self.levels(mid), p, q)), out
            if ka == "scalar" and kb == "op":
                p, out = self.op(node.right, lay)
                return Prog("mul", (self.scalar_leaf(node.left), p)), out
            if ka == "ket" and kb == "bra":
                return self.outer(node.left, node.right, lay)
        if isinstance(node, L.Bin) and node.op == "^@":
            return self.power(node, lay)
        if isinstance(node, L.Bin) and node.op in ("+", "-"):
            p, out = self.op(node.left, lay)
            q, out2 = self.op(node.right, lay)
            self.match(out2, out)
            if node.op == "-":
                q = Prog("mul", (MINUS, q))
            return Prog("add", (p, q)), out
        if isinstance(node, L.Neg):
            p, out = self.op(node.arg, lay)
            return Prog("mul", (MINUS, p)), out
        if isinstance(node, L.Call) and node.name == "adj" and len(node.args) == 1:
            p, out = self.op(node.args[0], lay)
            self.match(out, lay)
            return Prog("cnj", (Prog("ren", (swap_io(len(lay[0])), p)),)), lay
        if isinstance(node, L.Call) and node.name == "inv" and len(node.args) == 1:
            return self.inverse(node.args[0], lay, _op_label(node.args[0])), lay
        if isinstance(node, L.Call) and node.name in ANALYTIC and len(node.args) == 1:
            return self.op_function(node.name, node.args[0], lay, None), lay
        if isinstance(node, L.Bin) and node.op == "^":
            cnt = self.reader.scalar(node.right, {})
            if cnt.is_integer is not True:
                return self.op_function("pow", node.left, lay, cnt), lay
            if not cnt.is_Integer:
                raise CertifyError(
                    f"the symbolic power {cnt} of an operator not applied to a state"
                )
            n = int(cnt)
            if n < 0:
                q = self.inverse(node.left, lay, _op_label(node.left))
                n = -n
            else:
                q, out = self.op(node.left, lay)
                self.match(out, lay)
            if n == 0:
                return self.ident(lay), lay
            res = q
            for _ in range(n - 1):
                res = Prog("app", (self.levels(lay), q, res))
            return res, lay
        raise CertifyError(f"the operator expression {type(node).__name__}")

    def outer(self, ket: object, bra: object, lay: Layout) -> tuple[Prog, Layout]:
        """``|a><b|`` as the kernel ``a(o) conj(b(in))``: ``b`` read on the input registers."""
        from diracula import lang as L

        if not (isinstance(bra, L.Braket) and bra.bra):
            raise CertifyError("an outer product with a bra expression")
        pa, la = self.expr(ket)
        pb, lb = self.expr(L.Braket(bra.content, False, bra.dim), lay)
        self.match(lb, lay)
        return Prog("ten", (IN, pa, Prog("cnj", (pb,)))), la

    def power(self, node: object, lay: Layout) -> tuple[Prog, Layout]:
        """``U^@n`` on one register of width ``n``: the digit-wise kernel
        ``c^n ω_d^(α ddot(x, o))`` of a one-qudit kernel ``c ω_d^(α x o)``."""
        from diracula import lang as L

        assert isinstance(node, L.Bin)
        g = node.left
        if not (isinstance(g, L.Name) and g.id in self.trees and len(self.trees[g.id].slots) == 1):
            raise CertifyError("a tensor power of an operator other than a one-register gate")
        if len(lay[0]) != 1:
            raise CertifyError("a tensor power applied to several registers")
        w, d = lay[0][0], lay[1][0]
        tree = self.trees[g.id]
        q, want = tree.slots[0]
        count = self.reader.scalar(node.right, {})
        bind: dict[str, sympy.Expr] = {}
        if sympy.expand(count - w) != 0:
            if not (isinstance(node.right, L.Name) and self.free_symbol(node.right.id)):
                raise CertifyError(f"{g.id}^@{count} on a register of width {w}")
            bind[node.right.id] = w
        if want is not None and sympy.expand(self.reader.scalar(self.parse(want), {}) - d) != 0:
            if not self.free_symbol(want):
                raise CertifyError(f"{g.id}: |{q}>_{want} on a dimension-{d} register")
            bind[want] = d
        if bind:
            saved = self.reader.values
            self.reader.values = {**saved, **bind}
            try:
                return self.power_core(g, tree, q, lay, w, d, count, bind)
            finally:
                self.reader.values = saved
        return self.power_core(g, tree, q, lay, w, d, count, bind)

    def free_symbol(self, name: str) -> bool:
        """Whether the variable ``name`` is a symbol without a value, bound per application."""
        v = self.reader.values.get(name)
        return isinstance(v, sympy.Symbol) and v.name == name

    def power_core(
        self, g: Any, tree: GateTree, q: str, lay: Layout, w: Any, d: Any, count: Any, bind: Any
    ) -> tuple[Prog, Layout]:
        """The digit-wise kernel of ``g^@count`` on the register ``lay``."""
        key = ("pow", g.id, lay)
        if key in self.done:
            return self.done[key], lay
        x = sympy.Dummy(q, integer=True)
        o = sympy.Dummy("o", integer=True)
        self.vs.ids[x], self.vs.ids[o] = IN, 0
        k = self.reader.eval(tree.body, {q: Slot(x, sympy.Integer(1), d)})
        if not (isinstance(k, Ket) and len(k.terms) == 1 and len(k.terms[0][1]) == 1):
            raise CertifyError(f"{g.id} is not a phase kernel")
        amp, ((y, size),), (val,) = k.terms[0]
        if isinstance(val, sympy.Mod):
            val = val.args[0]
        if val != y or sympy.expand(size - d) != 0:
            raise CertifyError(f"{g.id} is not a phase kernel")
        yid = self.vs.bound(y, d)
        terms = self.vs.amp(amp)
        dm = self.vs.dmon(d)
        if len(terms) != 1 or terms[0][1] or len(terms[0][2]) != 1 or terms[0][3]:
            raise CertifyError(f"{g.id} is not a phase kernel")
        cm, _, ((pd, poly),), _ = terms[0]
        mono = tuple(sorted((IN, yid)))
        if pd != dm or len(poly) != 1 or poly[0][0] != mono:
            raise CertifyError(f"{g.id} is not a phase kernel")
        alpha = poly[0][1]
        ks = [kk for kk in range(-4, 5) if Y.rt_d(dm, kk) == cm]
        if not ks:
            raise CertifyError(f"{g.id} has a coefficient other than a power of sqrt({d})")
        n_lev = d**w
        self.vs.ranges[IN] = n_lev
        self.vs.ranges[0] = n_lev
        aid = self.vs.atom(0, [], [d, n_lev], [(x, n_lev), (o, n_lev)])
        atom = next(a for a in self.vs.atoms if a[0] == aid)
        term: ATm = (
            Y.rt_d(self.vs.dmon(n_lev), ks[0]),
            (),
            (atom,),
            (),
            ((dm, (((aid,), alpha),)),),
            (),
        )
        p = Prog("leaf", ([term],))
        return self.declare(
            key, f"gate_{_clean(g.id)}_pow", f"gate {tree.source}, to the power @{count}", p
        ), lay

    def factors(self, node: object) -> list[object]:
        from diracula import lang as L

        if isinstance(node, L.Bin) and node.op == "@":
            return self.factors(node.left) + self.factors(node.right)
        return [node]

    def span(self, node: object) -> int | None:
        from diracula import lang as L

        if isinstance(node, L.Bin) and node.op == "^@":
            return 1
        if isinstance(node, L.Name) and node.id in self.trees:
            return len(self.trees[node.id].slots)
        if isinstance(node, L.Juxt):
            return self.span(node.right)
        if isinstance(node, L.Bin) and node.op == "@":
            parts = [self.span(f) for f in self.factors(node)]
            return None if any(x is None for x in parts) else sum(x for x in parts if x is not None)
        return None

    def op_tensor(self, fs: list[object], lay: Layout) -> tuple[Prog, Layout]:
        from diracula import lang as L

        n = len(lay[0])
        if len(fs) == 1:
            return self.op(fs[0], lay)
        f = fs[0]
        k = self.span(f)
        if k is None:
            if isinstance(f, L.Name) and f.id == "I":
                k = 1
            else:
                raise CertifyError("an operator factor of unknown span")
        if k >= n:
            raise CertifyError("the operator does not cover the registers")
        head = (lay[0][:k], lay[1][:k])
        tail = (lay[0][k:], lay[1][k:])
        p, ph = self.op(f, head)
        if len(ph[0]) != k:
            raise CertifyError("a tensor factor that changes the number of registers")
        q, pt = self.op_tensor(fs[1:], tail)
        return Prog("ten", (k, p, q)), (ph[0] + pt[0], ph[1] + pt[1])

    def ident(self, lay: Layout) -> Prog:
        key = ("I", lay)
        if key in self.done:
            return self.done[key]
        dels = tuple(
            (lv, Y.ip_sub(Y.ip_v(i), Y.ip_v(IN + i))) for i, lv in enumerate(self.levels(lay))
        )
        p = Prog("leaf", ([(Y.of_q(1), (), (), dels, (), ())],))
        return self.declare(key, "ident", f"I on {len(lay[0])} register(s)", p)

    def gate(self, name: str, lay: Layout) -> tuple[Prog, Layout]:
        from diracula import lang as L

        if name not in self.trees:
            raise CertifyError(f"{name} is not a gate")
        tree = self.trees[name]
        if isinstance(tree.body, L.MatrixFor):
            raise CertifyError(f"the matrix gate {name}")
        if isinstance(tree.body, L.MatrixNode):
            return self.matrix_gate(name, tree, lay)
        if len(tree.slots) != len(lay[0]):
            raise CertifyError(f"{name} acts on {len(tree.slots)} register(s), got {len(lay[0])}")
        key: Any = ("gate", name, lay)
        if name.startswith("_"):
            bound = tuple(
                sorted((k, v) for k, v in self.reader.values.items() if isinstance(v, sympy.Dummy))
            )
            key = ("gate", name, lay, bound)
        loc = {}
        for i, ((q, want), w, d) in enumerate(zip(tree.slots, *lay, strict=True)):
            if want is not None and sympy.expand(self.reader.scalar(self.parse(want), {}) - d) != 0:
                raise CertifyError(f"{name}: |{q}>_{want} on a dimension-{d} register")
            s = sympy.Dummy(q, integer=True)
            self.vs.ids[s] = IN + i
            self.vs.ranges[IN + i] = d**w
            loc[q] = Slot(s, w, d)
        try:
            k = self.reader.eval(tree.body, loc)
        except CertifyError:
            if not self.named(tree.body) and not self.has_bra(tree.body):
                raise
            return self.gate_prog(name, tree, lay, loc, key)
        if not isinstance(k, Ket):
            raise CertifyError(f"the body of {name} is not a ket")
        if len(k.widths) == len(lay[0]):
            widths = [w if w is not None else lw for w, lw in zip(k.widths, lay[0], strict=True)]
            dims = [d if d is not None else ld for d, ld in zip(k.dims, lay[1], strict=True)]
        else:
            widths = [w if w is not None else sympy.Integer(1) for w in k.widths]
            dims = [d if d is not None else sympy.Integer(2) for d in k.dims]
        k = fix_layout(k, widths, dims)
        out: Layout = (k.widths, k.dims)
        if key in self.done:
            return self.done[key], out
        p = Prog("leaf", (ket_terms(self.vs, k),))
        return self.declare(key, f"gate_{_clean(name)}", f"gate {tree.source}", p), out

    def gate_prog(
        self, name: str, tree: GateTree, lay: Layout, loc: Mapping[str, Slot], key: object
    ) -> tuple[Prog, Layout]:
        """A gate whose body reads named states, its kernel built as a program with the pattern
        variables on the input registers."""
        if key in self.done:
            return self.done[key], self.gate_layouts[key]
        saved = self.reader.values
        self.reader.values = {**saved, **{q: sl.symbol for q, sl in loc.items()}}
        try:
            p, out = self.expr(tree.body)
        finally:
            self.reader.values = saved
        self.gate_layouts[key] = out
        return self.declare(key, f"gate_{_clean(name)}", f"gate {tree.source}", p), out

    def matrix_gate(self, name: str, tree: GateTree, lay: Layout) -> tuple[Prog, Layout]:
        """A matrix gate on one register as the kernel ``Σ_{i,j} M_ij [o = i][in = j]``."""
        if len(lay[0]) != 1:
            raise CertifyError(f"the matrix gate {name} on several registers")
        from diracula import lang as L

        if isinstance(tree.body, L.MatrixFor):
            return self.matrix_for(name, tree, lay)
        rows = [[self.reader.scalar(e, {}) for e in row] for row in tree.body.rows]  # type: ignore[attr-defined]
        w, d = lay[0][0], lay[1][0]
        if sympy.expand(d**w - len(rows)) != 0:
            raise CertifyError(f"the matrix gate {name} on a register of {d**w} levels")
        key = ("gate", name, lay)
        if key in self.done:
            return self.done[key], lay
        s = sympy.Dummy("in", integer=True)
        self.vs.ids[s] = IN
        self.vs.ranges[IN] = d**w
        terms = tuple(
            (a * sympy.KroneckerDelta(s, j), (), (sympy.Integer(i),))
            for i, row in enumerate(rows)
            for j, a in enumerate(row)
            if a != 0
        )
        k = Ket((w,), (d,), terms or ((sympy.Integer(0), (), (sympy.Integer(0),)),))
        p = Prog("leaf", (ket_terms(self.vs, k),))
        return self.declare(key, f"gate_{_clean(name)}", f"gate {name} = {tree.source}", p), lay

    def matrix_for(self, name: str, tree: GateTree, lay: Layout) -> tuple[Prog, Layout]:
        """A matrix comprehension on one register as the kernel ``Σ_r body(r, in) [o = r]``."""
        node = cast(Any, tree.body)
        w, d = lay[0][0], lay[1][0]
        lo = self.reader.scalar(node.lo, {})
        hi = self.reader.scalar(node.hi, {}) + (1 if node.inclusive else 0)
        if lo != 0 or sympy.expand(d**w - hi) != 0:
            raise CertifyError(f"the matrix {name} on a register of {d**w} levels")
        key = ("gate", name, lay)
        if key in self.done:
            return self.done[key], lay
        s = sympy.Dummy("in", integer=True)
        self.vs.ids[s] = IN
        self.vs.ranges[IN] = d**w
        r = sympy.Dummy(node.row, integer=True)
        saved = self.reader.values
        self.reader.values = {**saved, node.row: r, node.col: s}
        try:
            amp = self.reader.scalar(node.body, {})
        finally:
            self.reader.values = saved
        k = Ket((w,), (d,), ((amp, ((r, d**w),), (r,)),))
        p = Prog("leaf", (ket_terms(self.vs, k),))
        return self.declare(key, f"gate_{_clean(name)}", f"gate {name} = {tree.source}", p), lay

    # the theorem

    def split_scalar(self, node: object) -> tuple[sympy.Expr, object]:
        """``(c, A)`` for the tree ``c A`` of a scalar ``c`` and an operator ``A``."""
        from diracula import lang as L

        c: sympy.Expr = sympy.Integer(1)
        while True:
            if (
                (isinstance(node, L.Juxt) or (isinstance(node, L.Bin) and node.op == "*"))
                and self.kind(node.left) == "scalar"
                and self.kind(node.right) == "op"
            ):
                c, node = c * self.reader.scalar(node.left, {}), node.right
                continue
            if isinstance(node, L.Neg) and self.kind(node.arg) == "op":
                c, node = -c, node.arg
                continue
            return c, node

    def holds(self, p: Prog, q: Prog) -> bool:
        """Whether the mirror predicts that the normaliser proves ``p = q``."""
        rhs = prog_sym(q, self.floors(), self.vs.pw)
        return rhs is not None and cert_check(self.floors(), self.vs.pw, p, rhs)

    def scalar_value(self, v: sympy.Expr) -> Prog:
        return Prog("leaf", (scalar_terms(self.vs, p_tidy(v)),))

    def op_function(self, name: str, arg: object, lay: Layout, t: sympy.Expr | None) -> Prog:
        """``f(c A)`` read as its interpolation ``sum_j f(c l_j) E_j`` on the eigenvalues of
        ``A``, the minimal polynomial that gives it proved as a side obligation; a diagonal
        ``A`` on one register of at most 4 levels as ``sum_v f(c a(v)) [o = v][x = v]``."""
        from diracula import operators as O

        c, a_node = self.split_scalar(arg)
        f = O.scalar_function(name, t)
        base = _op_label(a_node)
        label = f"{base}^{t}" if name == "pow" else f"{name}({base})"
        if name == "exp":
            local = self.local_exp(c, a_node, lay, label)
            if local is not None:
                return local
            shift = self.shift_exp(c, a_node, lay, label)
            if shift is not None:
                return shift
        a, out = self.op(a_node, lay)
        self.match(out, lay)
        levels = self.levels(lay)
        ident = self.ident(lay)

        def mul(x: Prog, y: Prog) -> Prog:
            return Prog("app", (levels, x, y))

        def lin(coef: sympy.Expr, x: Prog) -> Prog:
            return Prog("mul", (self.scalar_value(coef), x))

        def side(title: str, p: Prog, q: Prog) -> None:
            self.side_obls.append((f"{title}, which gives {label}", p, prog_sym(q) or []))

        square = mul(a, a)
        if self.holds(square, ident):
            side(f"{base}^2 = I", square, ident)
            plus = Prog("add", (ident, a))
            minus = Prog("add", (ident, Prog("mul", (MINUS, a))))
            return Prog("add", (lin(f(c) / 2, plus), lin(f(-c) / 2, minus)))  # type: ignore[operator]
        if self.holds(square, a):
            side(f"{base}^2 = {base}", square, a)
            rest = Prog("add", (ident, Prog("mul", (MINUS, a))))
            return Prog("add", (lin(f(sympy.Integer(0)), rest), lin(f(c), a)))  # type: ignore[operator]
        pw = [ident, a, square]
        for m in range(3, O.MAX_ORDER + 1):
            pw.append(mul(a, pw[-1]))
            if self.holds(pw[m], ident):
                side(f"{base}^{m} = I", pw[m], ident)
                om = sympy.exp(2 * sympy.pi * sympy.I / m)
                total: Prog | None = None
                for j in range(m):
                    proj: Prog | None = None
                    for r in range(m):
                        term = lin(om ** (-j * r) / m, pw[r])
                        proj = term if proj is None else Prog("add", (proj, term))
                    assert proj is not None
                    part = lin(f(c * om**j), proj)  # type: ignore[operator]
                    total = part if total is None else Prog("add", (total, part))
                assert total is not None
                return total
        diag = self.diagonal_kernel(a_node, lay)
        if diag is not None:
            vals, leaf_a = diag
            side(f"{base} is diagonal", a, leaf_a)
            return self.diag_leaf([f(c * v) for v in vals], lay)  # type: ignore[operator]
        raise CertifyError(f"{label}: no certified spectral form")

    def local_exp(self, c: sympy.Expr, node: object, lay: Layout, label: str) -> Prog | None:
        """``exp(c sum_{j<n} I^@j @ G @ I^@(n-1-j))`` on one register of ``n`` qubits, ``G``
        diagonal with values ``l0, l1`` (a side obligation), as the kernel
        ``[o = x] e^(c (l0 (n - pop(o)) + l1 pop(o)))``; None for another operator."""
        from diracula import lang as L

        if not (isinstance(node, L.SumNode) and len(lay[0]) == 1 and lay[1][0] == 2):
            return None
        w = lay[0][0]
        lo = self.reader.scalar(node.lo, {})
        hi = self.reader.scalar(node.hi, {}) + (1 if node.inclusive else 0)
        if lo != 0 or sympy.expand(hi - w) != 0 or w.is_Integer:
            return None
        fs = self.factors(node.body)
        j = sympy.Symbol(node.var, integer=True)
        if len(fs) != 3:
            return None

        def ident_power(f: object, k: sympy.Expr) -> bool:
            if not (isinstance(f, L.Bin) and f.op == "^@"):
                return False
            if not (isinstance(f.left, L.Name) and f.left.id == "I"):
                return False
            saved = self.reader.values
            self.reader.values = {**saved, node.var: j}
            try:
                cnt = self.reader.scalar(f.right, {})
            finally:
                self.reader.values = saved
            return bool(sympy.expand(cnt - k) == 0)

        if not (ident_power(fs[0], j) and ident_power(fs[2], w - 1 - j)):
            return None
        vals = self.qubit_diagonal(fs[1])
        if vals is None:
            return None
        o = sympy.Dummy("o", integer=True)
        n_lev = sympy.Integer(2) ** w
        self.vs.ids[o] = 0
        self.vs.ranges[0] = n_lev
        amp = sympy.exp(sympy.expand(c * (vals[0] * (w - P_pop(o)) + vals[1] * P_pop(o))))
        lv = self.levels(lay)[0]
        dels = [(lv, Y.ip_sub(Y.ip_v(0), Y.ip_v(IN)))]
        terms: list[ATm] = []
        for cm, d2, phs, aps in self.vs.amp(amp):
            facs = dels + list(d2)
            terms.append(
                (cm, (), term_atoms(self.vs, facs + list(phs)), tuple(facs), tuple(phs), aps)
            )
        return Prog("leaf", (terms,))

    def shift_exp(self, c: sympy.Expr, node: object, lay: Layout, label: str) -> Prog | None:
        """``exp(c A)`` of a gate ``A |y>_d = |(y + s) % d>_d``, ``s = ±1``, as
        ``sum_k e^(c w^(-k s)) E_k``, ``E_k = (1/d) w^(k (o - x))``; the side theorems
        ``A = sum_k w^(-k s) E_k``, ``sum_k E_k = I`` and ``E_k E_l = [k = l] E_k``."""
        from diracula import lang as L

        if not (isinstance(node, L.Name) and node.id in self.trees and len(lay[0]) == 1):
            return None
        tree = self.trees[node.id]
        if len(tree.slots) != 1 or lay[0][0] != 1:
            return None
        d = lay[1][0]
        q = tree.slots[0][0]
        y = sympy.Dummy(q, integer=True)
        try:
            k = self.reader.eval(tree.body, {q: Slot(y, sympy.Integer(1), d)})
        except CertifyError:
            return None
        if not (isinstance(k, Ket) and len(k.terms) == 1 and not k.terms[0][1]):
            return None
        amp, _, kets = k.terms[0]
        if amp != 1 or len(kets) != 1:
            return None
        v = kets[0]
        if isinstance(v, sympy.Mod) and sympy.expand(v.args[1] - d) == 0:
            v = v.args[0]
        sh = sympy.expand(v - y)
        if sh not in (1, -1):
            return None
        s = int(sh)
        a, out = self.op(node, lay)
        self.match(out, lay)
        dm = self.vs.dmon(d)
        lv = self.levels(lay)[0]
        ksym = sympy.Dummy("k", integer=True)
        kid = self.vs.bound(ksym, d)
        oi = Y.ip_sub(Y.ip_v(0), Y.ip_v(IN))
        rd = Y.rt_d(dm, -2)

        def proj(kv: int, extra: Y.IPoly = ()) -> Y.Fac:
            return (dm, Y.ip_add(Y.ip_mul(Y.ip_v(kv), oi), extra))

        spec = (rd, ((kid, dm),), (), (), (proj(kid, Y.ip_smul(-s, Y.ip_v(kid))),), ())
        res = (rd, ((kid, dm),), (), (), (proj(kid),), ())
        k1, l1 = self.low_var(), self.low_var()
        e_k = Prog("leaf", ([(rd, (), (), (), (proj(k1),), ())],))
        e_l = Prog("leaf", ([(rd, (), (), (), (proj(l1),), ())],))
        e_kl = Prog(
            "leaf", ([(rd, (), (), ((lv, Y.ip_sub(Y.ip_v(k1), Y.ip_v(l1))),), (proj(k1),), ())],)
        )
        obls = [
            (f"{node.id} = sum_k w^(-k s) E_k", a, Prog("leaf", ([spec],))),
            ("sum_k E_k = I", Prog("leaf", ([res],)), self.ident(lay)),
            ("E_k E_l = [k = l] E_k", Prog("app", (self.levels(lay), e_k, e_l)), e_kl),
        ]
        for title, p, r in obls:
            if not self.holds(p, r):
                raise CertifyError(f"{label}: the spectral form of {node.id} ({title})")
        for title, p, r in obls:
            self.side_obls.append((f"{title}, which gives {label}", p, prog_sym(r) or []))
        arg = sympy.expand(c * sympy.exp(-2 * sympy.pi * sympy.I * ksym * s / d))
        fi = self.vs.cfunc(arg, ksym)
        term = (rd, ((kid, dm),), (), (), (proj(kid),), ((FB + 2 * fi, Y.ip_v(kid), ()),))
        return Prog("leaf", ([term],))

    def qubit_diagonal(self, node: object) -> list[sympy.Expr] | None:
        """The values ``a(0), a(1)`` of a one-qubit gate defined as ``|y> -> a(y) |y>``."""
        from diracula import lang as L

        if not (isinstance(node, L.Name) and node.id in self.trees):
            return None
        tree = self.trees[node.id]
        if len(tree.slots) != 1:
            return None
        q, want = tree.slots[0]
        if want is not None and sympy.expand(self.reader.scalar(self.parse(want), {}) - 2) != 0:
            return None
        vals = []
        for v in (0, 1):
            k = self.reader.eval(tree.body, {q: Slot(sympy.Integer(v), sympy.Integer(1), 2)})
            if not (isinstance(k, Ket) and len(k.terms) == 1 and not k.terms[0][1]):
                return None
            amp, _, kets = k.terms[0]
            if len(kets) != 1 or sympy.expand(sympy.Mod(kets[0], 2) - v) != 0:
                return None
            vals.append(sympy.sympify(amp))
        return vals

    def diag_leaf(self, values: Sequence[sympy.Expr], lay: Layout) -> Prog:
        """The kernel ``sum_v values[v] [o = v][x = v]`` on one register."""
        lv = self.levels(lay)[0]
        terms: list[ATm] = []
        for v, val in enumerate(values):
            dels = [(lv, Y.ip_sub(Y.ip_v(0), Y.ip_c(v))), (lv, Y.ip_sub(Y.ip_v(IN), Y.ip_c(v)))]
            for cm, d2, phs, aps in self.vs.amp(p_tidy(val)):
                facs = dels + list(d2)
                terms.append(
                    (cm, (), term_atoms(self.vs, facs + list(phs)), tuple(facs), tuple(phs), aps)
                )
        return Prog("leaf", (terms,))

    def diagonal_kernel(self, a_node: object, lay: Layout) -> tuple[list[sympy.Expr], Prog] | None:
        """The diagonal values ``a(v)`` of an operator on one register of at most 4 levels and
        its kernel ``sum_v a(v) [o = v][x = v]``; None for another operator."""
        from diracula import pathsum as P

        if len(lay[0]) != 1 or "value" not in self.hooks:
            return None
        n = sympy.sympify(lay[1][0] ** lay[0][0])
        if not (n.is_Integer and int(n) <= 4):
            return None
        op = self.hooks["value"](a_node)
        vals = []
        for v in range(int(n)):
            img = P.apply(op, P.basis(sympy.Integer(v), lay[0][0], lay[1][0]))
            if len(img.terms) != 1 or img.terms[0].bound or img.terms[0].kets != (v,):
                return None
            vals.append(img.terms[0].amp)
        return vals, self.diag_leaf(vals, lay)

    def symbolic_count(self, node: object) -> sympy.Expr | None:
        """The exponent of ``A^k`` for a symbolic ``k``, or None."""
        from diracula import lang as L

        if isinstance(node, L.Bin) and node.op == "^" and self.kind(node.left) == "op":
            cnt = self.reader.scalar(node.right, {})
            if not cnt.is_Integer and cnt.is_integer:
                return cnt
        return None

    def certify_density(
        self, label: str, node: object, values: Mapping[str, object], value: Any
    ) -> str:
        """The Lean source certifying the printed density matrix of the shown tree ``node``,
        vectorised."""
        self.setup(len(self.log))
        self.reader = Reader(self.parse, values, self.funcs)
        v, lay = self.dens(node)
        self.match(lay, self.mixed_layout(value))
        p = self.declare(("dexpr", label), "shown", f"show({label})", v)
        return self.density_source(label, f"{self.script}_show_{_clean(label)}", p, value)

    def certify_dstate(self, name: str, value: Any) -> str:
        """The Lean source certifying the density matrix ``|name>``, vectorised."""
        index = self.last(name)
        self.setup(len(self.log))
        p, _ = self.dens_event(index)
        return self.density_source(f"|{name}>", f"{self.script}_{_clean(name)}", p, value)

    def density_source(self, what: str, thm: str, p: Prog, value: Any) -> str:
        rhs = state_terms(self.vs, value.vec)
        self.check(p, rhs)
        head = f"/-- The printed density matrix of {what}, vectorised. -/\n"
        extra = [
            head + f"def printed : List ATm :=\n  {self.text.ex(rhs)}\n",
            *self.hint_decls(),
        ]
        return self.source(
            what, thm, self.lit_stmt(p, "printed"), self.lit_proof(p, "printed", ""), extra, []
        )

    def certify_pdist(
        self, name: str, label: str, index: int, values: Mapping[str, object], raw: Any
    ) -> str:
        """The Lean source certifying the distribution of the partial measurement at event
        ``index`` of ``|label>``: each branch's probability is the diagonal of the reduced
        density matrix, the probabilities sum to 1 and ``tr rho = 1``."""
        ev = self.log[index]
        self.setup(index + 1)
        self.reader = Reader(self.parse, ev.values, self.funcs)
        self.upto = index
        rho, lay = self.dens_event(self.previous(label, index))
        k = len(lay[0])
        regs_node, basis = ev.nodes
        regs = self.regs(regs_node, k)
        v = rho
        if basis is not None:
            v = self.conj_by(self.adjoint(self.on_regs(basis, lay, regs), lay), v, lay)
        red, rlay = self.partial(v, lay, regs)
        kk = len(rlay[0])
        decls: list[str] = []
        parts: list[tuple[str, str, str, str]] = []
        total: list[ATm] = []
        for b_i, br in enumerate(raw.branches, 1):
            for b in br.free:
                if b.lo != 0:
                    raise CertifyError("a branch index that does not start at 0")
                self.vs.ids.setdefault(b.symbol, PAR + 500 + len(self.vs.ids))
                self.vs.params.append(b.symbol.name)
            q = red
            if len(br.registers) != kk:
                raise CertifyError("a branch whose registers differ from the measured ones")
            for i, val in enumerate(br.registers):
                ip = self.vs.ipoly(sympy.sympify(val))
                q = Prog("sub", (i, ip, Prog("sub", (kk + i, ip, q))))
            prob = self.declare(("pprob", b_i), f"prob_{b_i}", f"branch {b_i}: <k|rho_R|k>", q)
            d, pr = self.lit(
                prob, scalar_terms(self.vs, br.prob), f"_{b_i}", f"The probability of branch {b_i}."
            )
            decls.append(d)
            parts.append(
                (
                    f"branch {b_i} of the measurement of |{label}>: probability {br.prob}",
                    f"{self.script}_{_clean(name)}_branch_{b_i}",
                    self.lit_stmt(prob, f"R_{b_i}"),
                    pr,
                )
            )
            sums = []
            for b in br.free:
                sid = self.vs.bound(sympy.Dummy(b.symbol.name, integer=True), b.hi + 1)
                sums.append((sid, self.vs.dmon(b.hi + 1)))
            for t in scalar_terms(self.vs, br.prob):
                total.append((t[0], tuple(sums) + t[1], t[2], t[3], t[4], t[5]))
        tot = self.declare(
            ("ptotal",),
            "total",
            f"the probabilities of measuring |{label}>",
            Prog("leaf", (total,)),
        )
        d, pr = self.lit(
            tot, scalar_terms(self.vs, sympy.Integer(1)), "_total", "The total probability."
        )
        decls.append(d)
        parts.append(
            (
                "the probabilities sum to 1",
                f"{self.script}_{_clean(name)}_total",
                self.lit_stmt(tot, "R_total"),
                pr,
            )
        )
        tr = self.declare(("ptr",), "trace", f"tr rho of |{label}>", self.diag_sum(rho, lay, k))
        d, pr = self.lit(tr, scalar_terms(self.vs, sympy.Integer(1)), "_norm", "One.")
        decls.append(d)
        parts.append(
            (
                f"tr rho of |{label}> = 1",
                f"{self.script}_{_clean(name)}_norm",
                self.lit_stmt(tr, "R_norm"),
                pr,
            )
        )
        first = parts[0]
        return self.source(first[0], first[1], first[2], first[3], decls, parts[1:])

    def low_var(self) -> int:
        """A variable no state or kernel reads, below the parameters: ``LOW + j``."""
        self.lows = getattr(self, "lows", 0) + 1
        return LOW + self.lows

    def vec(self, p: Prog, lay: Layout) -> Prog:
        """The vectorised density matrix ``psi(o) conj(psi(o'))`` of a state program."""
        return Prog("ten", (len(lay[0]), p, Prog("cnj", (p,))))

    def conj_by(self, k_prog: Prog, v: Prog, lay: Layout) -> Prog:
        """``K rho K^dagger`` vectorised: ``rho`` contracted with the kernel ``K (x) conj(K)``."""
        k = len(lay[0])
        levels = self.levels(lay)
        return Prog("app", (levels + levels, Prog("ten", (k, k_prog, Prog("cnj", (k_prog,)))), v))

    def adjoint(self, k_prog: Prog, lay: Layout) -> Prog:
        """The kernel ``conj(K(x, o))``."""
        return Prog("cnj", (Prog("ren", (swap_io(len(lay[0])), k_prog)),))

    @staticmethod
    def mixed_layout(value: Any) -> Layout:
        k = len(value.vec.widths) // 2
        return tuple(value.vec.widths[:k]), tuple(value.vec.dims[:k])

    def mixed_valued(self, node: object) -> bool:
        """Whether ``node`` denotes a density matrix built by a channel, a partial trace or a
        partial measurement."""
        from diracula import lang as L
        from diracula import pathsum as P

        if isinstance(node, L.Braket) and not node.bra:
            name = node.content.strip()
            if not self.is_state(name):
                return False
            return isinstance(self.log[self.previous(name, self.upto)].value, P.Mixed)
        if isinstance(node, L.Call) and node.name in ("tr", "keep") and len(node.args) == 2:
            return True
        if isinstance(node, L.Juxt):
            return self.is_channel(node.left) or self.mixed_valued(node.right)
        return False

    def is_channel(self, node: object) -> bool:
        from diracula import lang as L

        if isinstance(node, L.Name):
            return node.id in self.channels
        if isinstance(node, L.Call):
            return node.name in ("depolarize", "dephase", "amp_damp")
        if isinstance(node, L.Juxt):
            return self.is_channel(node.left) or self.is_channel(node.right)
        return False

    def regs(self, node: object, k: int) -> list[int]:
        from diracula import lang as L

        items = node.items if isinstance(node, L.SetNode) else (node,)
        out = []
        for item in items:
            v = self.reader.scalar(item, {})
            if not (v.is_Integer and 0 <= v < k):
                raise CertifyError(f"the register position {v}")
            out.append(int(v))
        return out

    def dens_event(self, index: int) -> tuple[Prog, Layout]:
        """The vectorised density matrix of the state after event ``index``."""
        from diracula import pathsum as P

        ev = self.log[index]
        if not isinstance(ev.value, P.Mixed):
            p, lay = self.state(index)
            return self.vec(p, lay), lay
        key = ("dens", index)
        if key in self.done:
            return self.done[key], self.mixed_layout(ev.value)
        saved = self.upto
        saved_reader = getattr(self, "reader", None)
        self.upto = index
        self.reader = Reader(self.parse, ev.values, self.funcs)
        try:
            if ev.kind == "dapply":
                v, lay = self.dens_event(self.previous(ev.name, index))
                for node in reversed(ev.nodes):
                    v, lay = self.dmap(node, v, lay)
            elif ev.kind == "pmeasure":
                v, lay = self.dens_event(self.previous(ev.name, index))
                v = self.dephase(v, lay, ev.nodes[0], ev.nodes[1])
            elif ev.kind == "dassign":
                v, lay = self.dens(ev.nodes[0])
            else:
                raise CertifyError(
                    ev.source if ev.kind == "opaque" else "an unrecorded density matrix"
                )
        finally:
            self.upto = saved
            if saved_reader is not None:
                self.reader = saved_reader
        self.match(lay, self.mixed_layout(ev.value))
        return self.declare(key, f"rho_{_clean(ev.name)}", ev.source, v), lay

    def dens(self, node: object) -> tuple[Prog, Layout]:
        """A density-valued tree, vectorised."""
        from diracula import lang as L

        if isinstance(node, L.Braket) and not node.bra:
            return self.dens_event(self.previous(node.content.strip(), self.upto))
        if isinstance(node, L.Call) and node.name in ("tr", "keep") and len(node.args) == 2:
            v, lay = self.dens_or_vec(node.args[0])
            k = len(lay[0])
            regs = self.regs(node.args[1], k)
            kept = sorted(regs) if node.name == "keep" else [r for r in range(k) if r not in regs]
            if not kept:
                raise CertifyError("a partial trace over every register")
            return self.partial(v, lay, kept)
        if isinstance(node, L.Juxt):
            v, lay = self.dens_or_vec(node.right)
            return self.dmap(node.left, v, lay)
        raise CertifyError(f"the density expression {type(node).__name__}")

    def dens_or_vec(self, node: object) -> tuple[Prog, Layout]:
        if self.mixed_valued(node):
            return self.dens(node)
        p, lay = self.expr(node)
        return self.vec(p, lay), lay

    def partial(self, v: Prog, lay: Layout, kept: Sequence[int]) -> tuple[Prog, Layout]:
        """``tr_R rho`` of the vectorised ``v``, keeping the registers ``kept`` in that order: each
        traced pair read as one summed variable, the kept registers renumbered."""
        k = len(lay[0])
        levels = self.levels(lay)
        q = v
        sums: list[tuple[Y.DMon, int]] = []
        for r in range(k):
            if r in kept:
                continue
            x = self.low_var()
            q = Prog("sub", (r, Y.ip_v(x), Prog("sub", (k + r, Y.ip_v(x), q))))
            sums.append((levels[r], x))
        kk = len(kept)
        pairs = tuple((kept[i], i) for i in range(kk)) + tuple(
            (k + kept[i], kk + i) for i in range(kk)
        )
        pairs = tuple(pr for pr in pairs if pr[0] != pr[1])
        if pairs:
            q = Prog("ren", (pairs, q))
        for lv, x in reversed(sums):
            q = Prog("sum", (lv, x, q))
        return q, (tuple(lay[0][r] for r in kept), tuple(lay[1][r] for r in kept))

    def diag_sum(self, q: Prog, lay: Layout, second: int) -> Prog:
        """``sum_x q`` with output register ``i`` and register ``second + i`` read as one summed
        variable each."""
        levels = self.levels(lay)
        sums: list[tuple[Y.DMon, int]] = []
        for i in range(len(lay[0])):
            x = self.low_var()
            q = Prog("sub", (i, Y.ip_v(x), Prog("sub", (second + i, Y.ip_v(x), q))))
            sums.append((levels[i], x))
        for lv, x in reversed(sums):
            q = Prog("sum", (lv, x, q))
        return q

    def on_regs(self, node: object, lay: Layout, regs: Sequence[int]) -> Prog:
        """The kernel of the operator ``node`` on the consecutive registers ``regs``, the
        identity on the others."""
        k = len(lay[0])
        lo, hi = min(regs), max(regs) + 1
        if sorted(regs) != list(range(lo, hi)):
            raise CertifyError("a measurement basis on registers that are not consecutive")
        mid = (lay[0][lo:hi], lay[1][lo:hi])
        q, out = self.op(node, mid)
        self.match(out, mid)
        if hi < k:
            q = Prog("ten", (hi - lo, q, self.ident((lay[0][hi:], lay[1][hi:]))))
        if lo > 0:
            q = Prog("ten", (lo, self.ident((lay[0][:lo], lay[1][:lo])), q))
        return q

    def dephase(self, v: Prog, lay: Layout, regs_node: object, basis: object) -> Prog:
        """``sum_k P_k rho P_k``, ``P_k = B|k><k|B^dagger`` on the registers ``regs_node``."""
        k = len(lay[0])
        regs = self.regs(regs_node, k)
        levels = self.levels(lay)
        b = None
        if basis is not None:
            b = self.on_regs(basis, lay, regs)
            v = self.conj_by(self.adjoint(b, lay), v, lay)
        dels = tuple((levels[r], Y.ip_sub(Y.ip_v(r), Y.ip_v(k + r))) for r in regs)
        v = Prog("mul", (Prog("leaf", ([(Y.of_q(1), (), (), dels, (), ())],)), v))
        if b is not None:
            v = self.conj_by(b, v, lay)
        return v

    def dmap(self, node: object, v: Prog, lay: Layout) -> tuple[Prog, Layout]:
        """A channel or an operator applied to the vectorised ``v``."""
        from diracula import lang as L

        if isinstance(node, L.Juxt) and self.is_channel(node):
            v, lay = self.dmap(node.right, v, lay)
            return self.dmap(node.left, v, lay)
        if isinstance(node, L.Name) and node.id in self.channels:
            self.trace_preserving(node.id, self.channels[node.id], lay)
            return self.kraus(self.channels[node.id], v, lay), lay
        if isinstance(node, L.Call) and node.name in ("depolarize", "dephase", "amp_damp"):
            tree = self.builtin_kraus(node, lay)
            self.trace_preserving(node.name, tree, lay)
            return self.kraus(tree, v, lay), lay
        kq, kout = self.op(node, lay)
        self.match(kout, lay)
        return self.conj_by(kq, v, lay), lay

    def builtin_kraus(self, node: Any, lay: Layout) -> object:
        """The Kraus operators of a built-in channel as a tree, for a concrete parameter."""
        par = self.reader.scalar(node.args[0], {})
        if par.free_symbols and not (isinstance(par, sympy.Symbol) and par in self.vs.unit_params):
            raise CertifyError(
                f"{node.name}({par}): the Kraus amplitude sqrt(1 - {par}) of a parameter not "
                "assumed in 0..1"
            )
        if len(lay[0]) != 1:
            raise CertifyError(f"{node.name} on several registers")
        d = f"({sympy.sstr(lay[1][0] ** lay[0][0])})"
        q = f"({sympy.sstr(par)})"
        if node.name == "depolarize":
            dim = sympy.sstr(lay[1][0])
            body = self.parse(f"e^(2*pi*i*b*x/{d}) |(x + a) % {d}>_{d}")
            self.trees = {**self.trees, "_pauli": GateTree((("x", dim),), body, "X^a Z^b")}
            text = (
                f"{{sqrt(1 - {q}) I, sum(a in 0..{d}){{ sum(b in 0..{d}){{ "
                f"sqrt({q})/{d} _pauli }} }} }}"
            )
        elif node.name == "dephase":
            text = f"{{sqrt(1 - {q}) I, sum(k in 0..{d}){{ sqrt({q}) |k>_{d}<k|_{d} }}}}"
        else:
            text = (
                f"{{sqrt(1 - {q}) I + (1 - sqrt(1 - {q})) |0>_{d}<0|_{d}, "
                f"sum(j in 0..{d} - 1){{ sqrt({q}) |0>_{d}<j + 1|_{d} }}}}"
            )
        return self.parse(text)

    def trace_preserving(self, name: str, tree: object, lay: Layout) -> None:
        """The theorem ``sum_k K_k^dagger K_k = I`` of a channel, as a side obligation when the
        mirror predicts its proof."""
        try:
            tp = self.kraus_tp(tree, lay)
        except CertifyError:
            return
        for unit in (self.ident(lay), self.concrete_ident(lay)):
            if unit is not None and self.holds(tp, unit):
                rhs = prog_sym(unit, self.floors(), self.vs.pw) or []
                self.side_obls.append((f"the channel {name} is trace preserving", tp, rhs))
                return

    def kraus_tp(self, node: object, lay: Layout) -> Prog:
        """``sum_k K_k^dagger K_k`` over the Kraus operators of the tree ``node``."""
        from diracula import lang as L

        if isinstance(node, L.Call) and node.name in ("depolarize", "dephase", "amp_damp"):
            return self.kraus_tp(self.builtin_kraus(node, lay), lay)
        if isinstance(node, L.Name) and node.id in self.channels:
            return self.kraus_tp(self.channels[node.id], lay)
        if isinstance(node, L.SetNode):
            parts = [self.kraus_tp(item, lay) for item in node.items]
            out = parts[0]
            for q in parts[1:]:
                out = Prog("add", (out, q))
            return out
        if isinstance(node, L.SumNode):
            lo = self.reader.scalar(node.lo, {})
            hi = self.reader.scalar(node.hi, {}) + (1 if node.inclusive else 0)
            if lo != 0:
                raise CertifyError("a Kraus family that does not start at 0")
            sym = sympy.Dummy(node.var, integer=True)
            x = self.low_var()
            self.vs.ids[sym] = x
            self.vs.ranges[x] = hi
            saved = self.reader.values
            self.reader.values = {**saved, node.var: sym}
            try:
                body = self.kraus_tp(node.body, lay)
            finally:
                self.reader.values = saved
            return Prog("sum", (self.vs.dmon(hi), x, body))
        kq, kout = self.op(node, lay)
        self.match(kout, lay)
        return Prog("app", (self.levels(lay), self.adjoint(kq, lay), kq))

    def kraus(self, node: object, v: Prog, lay: Layout) -> Prog:
        """``sum_k K_k rho K_k^dagger`` over the Kraus operators of the tree ``node``."""
        from diracula import lang as L

        if isinstance(node, L.Call) and node.name in ("depolarize", "dephase", "amp_damp"):
            return self.kraus(self.builtin_kraus(node, lay), v, lay)
        if isinstance(node, L.Name) and node.id in self.channels:
            return self.kraus(self.channels[node.id], v, lay)
        if isinstance(node, L.SetNode):
            parts = [self.kraus(item, v, lay) for item in node.items]
            out = parts[0]
            for q in parts[1:]:
                out = Prog("add", (out, q))
            return out
        if isinstance(node, L.SumNode):
            lo = self.reader.scalar(node.lo, {})
            hi = self.reader.scalar(node.hi, {}) + (1 if node.inclusive else 0)
            if lo != 0:
                raise CertifyError("a Kraus family that does not start at 0")
            sym = sympy.Dummy(node.var, integer=True)
            x = self.low_var()
            self.vs.ids[sym] = x
            self.vs.ranges[x] = hi
            saved = self.reader.values
            self.reader.values = {**saved, node.var: sym}
            try:
                body = self.kraus(node.body, v, lay)
            finally:
                self.reader.values = saved
            return Prog("sum", (self.vs.dmon(hi), x, body))
        kq, kout = self.op(node, lay)
        self.match(kout, lay)
        return self.conj_by(kq, v, lay)

    def op_trace(self, q: Prog, lay: Layout) -> Prog:
        """``sum_x A(x, x)`` of an operator kernel."""
        return self.diag_sum(q, lay, IN)

    def inverse(self, node: object, lay: Layout, label: str) -> Prog:
        """The inverse of an operator ``U``: its adjoint when ``U^dagger U = I``, else the
        transpose of a monomial kernel with its coefficient inverted, else the exact inverse of
        an explicit matrix; ``V U = I`` is a side obligation."""
        q, out = self.op(node, lay)
        self.match(out, lay)
        ident = self.ident(lay)
        levels = self.levels(lay)
        title = f"{label}^-1 {label} = I"
        cands: list[tuple[str, Callable[[], Prog | None]]] = [
            ("its adjoint", lambda: self.adjoint(q, lay))
        ]
        cands.append(
            (
                "the transpose of its kernel, coefficients inverted",
                lambda: self.monomial_inverse(q, lay),
            )
        )
        cands.append(("the inverse of its matrix", lambda: self.matrix_inverse(node, lay)))
        for how, make in cands:
            try:
                v = make()
            except CertifyError:
                continue
            if v is None:
                continue
            left = Prog("app", (levels, v, q))
            for unit in (ident, self.concrete_ident(lay)):
                if unit is not None and self.holds(left, unit):
                    rhs = prog_sym(unit, self.floors(), self.vs.pw) or []
                    self.side_obls.append((f"{title}: the inverse of {label} is {how}", left, rhs))
                    return v
        raise CertifyError(f"the inverse of {label}: no certified left inverse")

    def concrete_ident(self, lay: Layout) -> Prog | None:
        """``sum_v [o = v][x = v]`` on one register of at most 16 levels."""
        if len(lay[0]) != 1:
            return None
        n = sympy.sympify(lay[1][0] ** lay[0][0])
        if not (n.is_Integer and int(n) <= 16):
            return None
        return self.diag_leaf([sympy.Integer(1)] * int(n), lay)

    def monomial_inverse(self, q: Prog, lay: Layout) -> Prog | None:
        """``V(o, x) = [x = g(o)] / c(o)`` for the kernel ``U(o, x) = c(x) [o = g(x)]``."""
        e = prog_sym(q, self.floors(), self.vs.pw)
        if e is None or len(e) != 1 or e[0][1]:
            return None
        t = e[0]
        cm = cm_inverse(t[0])
        if cm is None:
            return None
        phs = tuple((dm, Y.ip_smul(-1, poly)) for dm, poly in t[4])
        leaf = Prog("leaf", ([(cm, t[1], t[2], t[3], phs, t[5])],))
        return Prog("ren", (swap_io(len(lay[0])), leaf))

    def matrix_inverse(self, node: object, lay: Layout) -> Prog | None:
        """The kernel of the exact inverse of a gate given by a matrix of concrete size."""
        from diracula import lang as L

        if "value" not in self.hooks:
            return None
        g = self.hooks["value"](node)
        if getattr(g, "matrix", None) is None:
            return None
        m = sympy.Matrix(g.matrix())
        det = p_tidy(m.det())
        if det == 0:
            return None
        inv = (m.adjugate() / det).applyfunc(p_tidy)
        rows = tuple(tuple(L.Num(inv[r, c]) for c in range(inv.cols)) for r in range(inv.rows))
        name = f"{_op_label(node)}_inv"
        tree = GateTree(
            getattr(self.trees.get(_op_label(node)), "slots", ()), L.MatrixNode(rows), name
        )
        prog, out = self.matrix_gate(name, tree, lay)
        self.match(out, lay)
        return prog

    def power_loop(
        self, op_node: object, cnt: sympy.Expr, init: Prog, lay: Layout, init_value: Any
    ) -> Prog:
        """``A^k |s>`` for a symbolic ``k`` as the loop of ``k`` steps of ``A`` from ``|s>``, its
        invariant the engine's ``A^J |s>``."""
        step, out = self.op(op_node, lay)
        self.match(out, lay)
        if "power" not in self.hooks:
            raise CertifyError("a symbolic power without the engine's iterate")
        j_sym = sympy.Symbol(f"J{len(self.vs.loops)}", integer=True, nonnegative=True)
        try:
            inv = self.hooks["power"](op_node, j_sym, init_value)
        except Exception as exc:
            raise CertifyError(f"the power has no closed-form iterate: {exc}") from exc
        self.vs.loops.append(j_sym)
        j = self.vs.var(j_sym)
        inv_terms = state_terms(self.vs, self.reduced_params(inv, j_sym))
        k0: list[tuple[ATm, int, int]] = []
        k1: list[tuple[ATm, int, int]] = []
        if any(a[0] >= GB for t in inv_terms for a in t[5]):
            k0, k1 = self.loop_cofactors(self.levels(lay), j, step, init, inv_terms)
        return Prog(
            "loop",
            (
                self.levels(lay),
                j,
                0,
                self.vs.count(cnt),
                step,
                init,
                inv_terms,
                tuple(k0),
                tuple(k1),
            ),
        )

    def loop_cofactors(
        self, levels: Any, j: int, step: Prog, init: Prog, inv: list[ATm]
    ) -> tuple[list[tuple[ATm, int, int]], list[tuple[ATm, int, int]]]:
        """The relation cofactors of the two checks of a loop from ``J = 0``."""
        fl, pw = self.floors(), self.vs.pw
        x0, y0 = prog_sym(step, fl, pw), prog_sym(init, fl, pw)
        if x0 is None or y0 is None:
            raise CertifyError("a loop step or start without an expression")
        v0, v1 = Y.ip_c(0), Y.ip_add(Y.ip_v(j), Y.ip_c(1))
        e0 = list(y0) + Z.ax_neg([t_sub(j, v0, t) for t in inv])
        e1 = app_sym(levels, apart(fresh(x0, inv), x0), inv)
        if e1 is None:
            raise CertifyError("a loop step that does not apply to the invariant")
        e1 = e1 + Z.ax_neg(j_pass(0, j, [t_sub(j, v1, t) for t in inv]))
        k0, k1 = rel_cofactors(fl, pw, e0), rel_cofactors(fl, pw, e1)
        if k0 is None or k1 is None:
            raise CertifyError("the invariant's angle relations have no cofactors")
        return k0, k1

    def anchor(self, base: Any, k: Any) -> None:
        """Lowers the anchor offset of ``base^(n + c)`` for an exponent ``k = n + c``."""
        k = sympy.sympify(k)
        if base is None or len(k.free_symbols) != 1:
            return
        (n,) = k.free_symbols
        p = sympy.Poly(k, n)
        if p.degree() != 1 or not all(x.is_Integer for x in p.all_coeffs()):
            return
        a, b = (int(x) for x in p.all_coeffs())
        if a == 1 and b < self.vs.anchors.get((base, n), 0):
            self.vs.anchors[(base, n)] = b

    def setup(self, upto: int) -> None:
        self.upto = upto
        self.vs.unit_params = self.unit_ranged()
        for ev in self.log:
            if isinstance(ev.value, State):
                for w, d in zip(ev.value.widths, ev.value.dims, strict=True):
                    if w is not None:
                        self.anchor(d, w)
                    if d is not None:
                        for f in sympy.preorder_traversal(sympy.sympify(d)):
                            if isinstance(f, sympy.Pow):
                                self.anchor(f.base, f.exp)
        self.vs.divs = []
        for a in self.assumptions:
            if isinstance(a, sympy.Eq) and a.rhs == 0 and isinstance(a.lhs, sympy.Mod):
                self.vs.divs.append((a.lhs.args[0], a.lhs.args[1]))
        for ev in self.log[:upto]:
            if isinstance(ev.value, State):
                for d in ev.value.dims:
                    ex: set[sympy.Basic] = set()
                    for f in sympy.preorder_traversal(sympy.sympify(d)) if d is not None else ():
                        if isinstance(f, sympy.Pow):
                            ex |= f.exp.free_symbols
                    for s in sympy.sympify(d).free_symbols if d is not None else ():
                        if s in ex:
                            if s not in self.vs.widths:
                                self.vs.widths.append(s)
                        else:
                            self.vs.dim(s)
                for w in ev.value.widths:
                    for s in sympy.sympify(w).free_symbols if w is not None else ():
                        if s not in self.vs.widths:
                            self.vs.widths.append(s)

    def last(self, name: str) -> int:
        for k in range(len(self.log) - 1, -1, -1):
            if self.log[k].name == name:
                return k
        raise CertifyError(f"|{name}> has no recorded definition")

    def floors(self) -> list[int]:
        wide = self.vs.needs_width
        return [
            (
                2
                if (wide and isinstance(self.vs.powers[s][1], sympy.Symbol))
                or self.offset_low(self.vs.powers[s][1]) is not None
                else 0
            )
            if s in self.vs.powers
            else 2
            for s in self.vs.dsyms
        ]

    def unit_ranged(self) -> set[sympy.Symbol]:
        """The real parameters assumed at least 0 and at most 1."""
        lo: set[sympy.Symbol] = set()
        hi: set[sympy.Symbol] = set()
        for fact in getattr(self, "assumptions", []):
            for rel in (fact, getattr(fact, "reversed", fact)):
                x = getattr(rel, "lhs", None)
                if not (isinstance(x, sympy.Symbol) and x.is_real and not x.is_integer):
                    continue
                if isinstance(rel, sympy.GreaterThan) and rel.rhs == 0:
                    lo.add(x)
                if isinstance(rel, sympy.LessThan) and rel.rhs == 1:
                    hi.add(x)
        return lo & hi

    def width_low(self, n: sympy.Symbol) -> int | None:
        """The greatest lower bound ``L`` of the width ``n`` an assumption states, or None."""
        best = None
        for fact in getattr(self, "assumptions", []):
            for rel in (fact, getattr(fact, "reversed", fact)):
                if isinstance(rel, (sympy.GreaterThan, sympy.StrictGreaterThan)) and rel.lhs == n:
                    b = rel.rhs
                    if b.is_Integer:
                        lo = int(b) + (1 if isinstance(rel, sympy.StrictGreaterThan) else 0)
                        best = lo if best is None else max(best, lo)
        return best

    def offset_low(self, e: sympy.Expr) -> tuple[sympy.Symbol, int] | None:
        """``(n, L)`` for an exponent ``n + c``, ``c < 0``, of a width ``n`` assumed at least
        ``L`` with ``L + c >= 1``; None otherwise."""
        e = sympy.sympify(e)
        if isinstance(e, sympy.Symbol) or len(e.free_symbols) != 1:
            return None
        (n,) = e.free_symbols
        c = sympy.expand(e - n)
        if not (c.is_Integer and c < 0 and n in self.vs.widths):
            return None
        lo = self.width_low(n)
        if lo is None or lo + int(c) < 1:
            return None
        return n, lo

    def wl(self) -> list[tuple[int, Y.DMon, Y.DMon]]:
        """The width links: ``(ν k, d, N)`` for each power ``N = d^n`` whose width ``n`` is the
        parameter ``ν k`` (a loop count)."""
        out = []
        for a, (base, n) in self.vs.powers.items():
            if isinstance(n, sympy.Symbol) and n.name in self.vs.params:
                out.append(
                    (PAR + self.vs.params.index(n.name), self.vs.dmon(base), self.vs.dmon(a))
                )
        return out

    def dv(self) -> list[tuple[Y.DMon, Y.DMon]]:
        """``(D1, D2)`` for each assumption ``D2 % D1 == 0`` between dimension monomials."""
        out = []
        for a, b in self.vs.divs:
            try:
                out.append((self.vs.dmon(b), self.vs.dmon(a)))
            except CertifyError:
                continue
        return out

    def ctx(self) -> Z.Ctx:
        """The context of the closing pass: the width links and divisibilities."""
        return ((), tuple(self.wl()), tuple(self.dv()))

    def check(self, p: Prog, rhs: Sequence[ATm]) -> list[str]:
        """The translation and normal-form declarations of a closing check."""
        self.wl_used = []
        self.ctx_used = False
        ok = cert_check(self.floors(), self.vs.pw, p, rhs)
        if not ok and self.vs.powers and not self.vs.needs_width:
            self.vs.needs_width = True
            ok = cert_check(self.floors(), self.vs.pw, p, rhs)
        self.rounds = 1
        if not ok and (self.wl() or self.dv()):
            ok = cert_check(self.floors(), self.vs.pw, p, rhs, self.ctx())
            if not ok:
                ok = cert_check(self.floors(), self.vs.pw, p, rhs, self.ctx(), 2)
                self.rounds = 2 if ok else 1
            self.wl_used = self.wl() if ok else []
            self.ctx_used = ok
            self.ctx_any = self.ctx_any or ok
        self.real_rs = []
        self.real_kind = "real"
        rs = [k for k, c in enumerate(self.vs.catoms) if c.is_integer]
        if not ok and rs:
            e0 = prog_sym(p, self.floors(), self.vs.pw)
            if e0 is not None and not Z.nf_a(
                self.floors(), self.vs.pw, [Z.real_t(rs, t) for t in e0 + Z.ax_neg(rhs)]
            ):
                ok, self.real_rs, self.ctx_used, self.rounds = True, rs, False, 1
                self.real_any = sorted(set(self.real_any) | set(rs))
        us = [k for k, c in enumerate(self.vs.catoms) if c in self.vs.angle_atoms.values()]
        if not ok and us:
            e0 = prog_sym(p, self.floors(), self.vs.pw)
            if e0 is not None and not Z.nf_a(
                self.floors(), self.vs.pw, [Z.unit_t(us, t) for t in e0 + Z.ax_neg(rhs)]
            ):
                ok, self.real_rs, self.ctx_used, self.rounds = True, us, False, 1
                self.real_kind = "unit"
                self.unit_any = sorted(set(self.unit_any) | set(us))
        self.gauss_used = False
        if not ok:
            e0 = prog_sym(p, self.floors(), self.vs.pw)
            if e0 is not None:
                nf1 = Z.nf_a(self.floors(), self.vs.pw, e0 + Z.ax_neg(rhs))
                if nf1 and not Z.nf_a(self.floors(), self.vs.pw, Z.gauss_a(nf1)):
                    ok, self.ctx_used, self.rounds, self.gauss_used = True, False, 2, True
                    self.gauss_any = True
        if not ok:
            raise CertifyError("the normaliser does not close the difference")
        e = prog_sym(p, self.floors(), self.vs.pw)
        assert e is not None
        fl, pw = self.floors(), self.vs.pw
        if self.real_rs:
            conj_t = Z.unit_t if self.real_kind == "unit" else Z.real_t
            ns0 = [conj_t(self.real_rs, t) for t in e + Z.ax_neg(rhs)]
            self.sym, self.nfs, self.nfs2 = e, [Z.norm_a(fl, pw, Z.AROUNDS, t) for t in ns0], []
            return []
        e2 = Z.x_pass(self.ctx(), e) if self.ctx_used else e
        ns = [Z.norm_a(fl, pw, Z.AROUNDS, t) for t in e2 + Z.ax_neg(rhs)]
        self.nfs2 = []
        if self.gauss_used:
            nf1 = Z.nf_a(fl, pw, e + Z.ax_neg(rhs))
            self.nfs2 = [Z.norm_a(fl, pw, Z.AROUNDS, t) for t in Z.gauss_a(nf1)]
        elif self.rounds == 2:
            nf1 = Z.nf_a(fl, pw, e2 + Z.ax_neg(rhs))
            self.nfs2 = [Z.norm_a(fl, pw, Z.AROUNDS, t) for t in Z.x_pass(self.ctx(), nf1)]
        self.sym, self.nfs = e, ns
        return []

    def hint_decls(self, k: str = "") -> list[str]:
        nfs = ",\n   ".join("none" if t is None else f"some {self.text.tm(t)}" for t in self.nfs)
        second = []
        if self.rounds == 2:
            nfs2 = ",\n   ".join(
                "none" if t is None else f"some {self.text.tm(t)}" for t in self.nfs2
            )
            second = [
                (
                    f"/-- The normal form of each term of the second round. -/\n"
                    f"def NF2{k} : List (Option ATm) :=\n  [{nfs2}]\n"
                )
            ]
        return [
            *second,
            (
                f"/-- The program as one expression. -/\ndef SYM{k} : List ATm :=\n  "
                f"{self.text.ex(self.sym)}\n"
            ),
            (
                f"/-- The normal form of each term of the difference. -/\n"
                f"def NF{k} : List (Option ATm) :=\n  [{nfs}]\n"
            ),
        ]

    def lit(self, p: Prog, rhs: Sequence[ATm], k: str, label: str) -> tuple[str, str]:
        """The declarations and proof of ``p.sem V = fun ν => axDen V ν R``."""
        self.check(p, rhs)
        decls = [
            f"/-- {label} -/\ndef R{k} : List ATm :=\n  {self.text.ex(rhs)}\n",
            *self.hint_decls(k),
        ]
        return "\n".join(decls), self.lit_proof(p, f"R{k}", k)

    def wl_hyps(self) -> list[tuple[int, str]]:
        """``(ν k, n)`` for each width link the last check used."""
        out: list[tuple[int, str]] = []
        for v, _, _ in self.wl_used:
            if (v, self.vs.params[v - PAR]) not in out:
                out.append((v, self.vs.params[v - PAR]))
        return out

    def wl_intro(self) -> tuple[str, str]:
        """The hypotheses ``ν k = n`` of the last check's width links and their names."""
        hyps = self.wl_hyps()
        return (
            "".join(f"ν {v} = ({n} : ℤ) → " for v, n in hyps),
            " ".join(f"h_ν{v}" for v, _ in hyps),
        )

    def rs_names(self) -> str:
        return "US USOK" if self.real_kind == "unit" else "RS RSOK"

    def lit_proof(self, p: Prog, r: str, k: str) -> str:
        if getattr(self, "gauss_used", False):
            return (
                f"DiracULA.LGauss.certify_gauss_c V hρ FL FLOK PW PWOK {p.name} {r} SYM{k} NF{k} "
                f"NF2{k} {DECIDES} (by decide +kernel)"
            )
        if self.real_rs:
            return (
                f"certify_{self.real_kind}_c V hρ FL FLOK PW PWOK {self.rs_names()} {p.name} {r} "
                f"SYM{k} NF{k} " + DECIDES
            )
        if self.ctx_used:
            _, names = self.wl_intro()
            if self.rounds == 2:
                return (
                    f"fun ν {names} => certify_w2_c V hρ FL FLOK PW PWOK CTX {p.name} {r} SYM{k} "
                    f"NF{k} NF2{k} {DECIDES} (by decide +kernel) ν (CTXOK ν ⟪ASM⟫ {names})"
                )
            return (
                f"fun ν {names} => certify_w_c V hρ FL FLOK PW PWOK CTX {p.name} {r} SYM{k} "
                f"NF{k} {DECIDES} ν (CTXOK ν ⟪ASM⟫ {names})"
            )
        if counts(p):
            return f"certify_lit_c V hρ FL FLOK PW PWOK {p.name} {r} SYM{k} NF{k} " + DECIDES
        return f"certify_lit V hρ FL FLOK PW PWOK {p.name} {r} SYM{k} NF{k} " + DECIDES

    def lit_stmt(self, p: Prog, r: str) -> str:
        if self.real_rs or getattr(self, "gauss_used", False):
            return (
                f"∀ ν : ℕ → ℤ, (∀ c ∈ {p.name}.counts, 0 ≤ ipDen ν c) → "
                f"{p.name}.sem V ν = axDen V ν {r}"
            )
        if self.ctx_used:
            hyps, _ = self.wl_intro()
            return (
                f"∀ ν : ℕ → ℤ, {hyps}(∀ c ∈ {p.name}.counts, 0 ≤ ipDen ν c) → "
                f"{p.name}.sem V ν = axDen V ν {r}"
            )
        if counts(p):
            return (
                f"∀ ν : ℕ → ℤ, (∀ c ∈ {p.name}.counts, 0 ≤ ipDen ν c) → "
                f"{p.name}.sem V ν = axDen V ν {r}"
            )
        return f"{p.name}.sem V = fun ν => axDen V ν {r}"

    def certify_state(self, name: str, value: State) -> str:
        """The Lean source certifying the printed value of ``|name>``."""
        index = self.last(name)
        self.setup(len(self.log))
        p, _ = self.state(index)
        rhs = state_terms(self.vs, value)
        self.check(p, rhs)
        printed = f"printed_{_clean(name)}"
        extra = [
            (
                f"/-- The printed value of |{name}>. -/\ndef {printed} : List ATm :=\n  "
                f"{self.text.ex(rhs)}\n"
            ),
            *self.hint_decls(),
        ]
        return self.source(
            f"|{name}>",
            f"{self.script}_{_clean(name)}",
            self.lit_stmt(p, printed),
            self.lit_proof(p, printed, ""),
            extra,
            [],
        )

    def certify_expr(
        self, label: str, node: object, values: Mapping[str, object], value: State
    ) -> str:
        """The Lean source certifying the printed value of the shown state expression
        ``node``."""
        self.setup(len(self.log))
        for tree in self.trees.values():
            for _, dim in tree.slots:
                v = values.get(dim) if dim else None
                if isinstance(v, sympy.Basic):
                    for sym in v.free_symbols:
                        if isinstance(sym, sympy.Symbol) and sym not in self.vs.widths:
                            self.vs.dim(sym)
        self.reader = Reader(self.parse, values, self.funcs)
        lay = self.layout_of(value)
        p0, got = self.expr(node, lay)
        self.match(got, lay)
        p = self.declare(("expr", label), "shown", f"show({label})", p0)
        rhs = state_terms(self.vs, value)
        self.check(p, rhs)
        extra = [
            (
                f"/-- The printed value of {label}. -/\ndef printed : List ATm :=\n  "
                f"{self.text.ex(rhs)}\n"
            ),
            *self.hint_decls(),
        ]
        return self.source(
            label,
            f"{self.script}_show_{_clean(label)}",
            self.lit_stmt(p, "printed"),
            self.lit_proof(p, "printed", ""),
            extra,
            [],
        )

    def lit_use(self, p: Prog, proof: str, hc: str) -> tuple[list[tuple[str, str]], str]:
        """The hypotheses of the last ``lit`` check of ``p`` and its proof applied at ``ν``."""
        cnt = (hc, f"∀ c ∈ {p.name}.counts, 0 ≤ ipDen ν c")
        if self.ctx_used:
            hyps = [(f"h_ν{v}", f"ν {v} = ({n} : ℤ)") for v, n in self.wl_hyps()]
            names = " ".join(a for a, _ in hyps)
            return [*hyps, cnt], f"(({proof}) ν {names} {hc})"
        if counts(p) or self.real_rs:
            return [cnt], f"(({proof}) ν {hc})"
        return [], f"(congrFun ({proof}) ν)"

    @staticmethod
    def binders(hyps: Sequence[tuple[str, str]]) -> tuple[str, str]:
        """``(a : T) → ...`` text of distinct hypotheses and their names."""
        seen: dict[str, str] = {}
        for a, t in hyps:
            seen.setdefault(a, t)
        return "".join(f"({t}) → " for t in seen.values()), " ".join(seen)

    def certify_norm(
        self, label: str, node: Any, values: Mapping[str, object], value: State, norm: sympy.Expr
    ) -> str:
        """The Lean source certifying ``normalise(s)``: ``k s`` is the printed value and
        ``k² <s|s> = 1`` for the positive real ``k = 1/norm``."""
        self.setup(len(self.log))
        self.reader = Reader(self.parse, values, self.funcs)
        lay = self.layout_of(value)
        p0, got = self.expr(node.args[0], lay)
        self.match(got, lay)
        psi = self.declare(("expr", label), "state", f"the state normalised in {label}", p0)
        kt = scalar_terms(self.vs, 1 / norm)
        if len(kt) != 1 or not pos_c(kt[0]):
            raise CertifyError(f"the norm {norm}")
        kleaf = Prog("leaf", ([kt[0]],))
        inn = self.declare(
            ("nrm_in",), "inner", f"<s|s> of {label}", Prog("inn", (self.levels(lay), psi, psi))
        )
        sa = self.declare(("nrm_a",), "scaled", f"k s of {label}", Prog("mul", (kleaf, psi)))
        da, pa = self.lit(sa, state_terms(self.vs, value), "_a", f"The printed value of {label}.")
        ha, ua = self.lit_use(sa, pa, "hc_a")
        sb = self.declare(
            ("nrm_b",),
            "unit",
            f"k² <s|s> of {label}",
            Prog("mul", (Prog("mul", (kleaf, kleaf)), inn)),
        )
        db, pb = self.lit(sb, scalar_terms(self.vs, sympy.Integer(1)), "_b", "One.")
        hb, ub = self.lit_use(sb, pb, "hc_b")
        bind, names = self.binders(ha + hb)
        kdecl = (
            f"/-- The coefficient k = 1/({norm}). -/\ndef KT : ATm :=\n  {self.text.tm(kt[0])}\n"
        )
        stmt = (
            f"∀ ν : ℕ → ℤ, {bind}axDen V ν R_a = "
            f"((Real.sqrt ({inn.name}.sem V ν).re : ℝ) : ℂ)⁻¹ * {psi.name}.sem V ν"
        )
        proof = (
            f"fun ν {names} => nrm_cert V hρ _ {psi.name} R_a KT (by decide +kernel) ν {ua} {ub}"
        )
        return self.source(
            label, f"{self.script}_show_{_clean(label)}", stmt, proof, [kdecl, da, db], []
        )

    def printed_op(self, v: Any, lay: Layout) -> Prog:
        """A printed operator as a program: outer products of printed states, scaled sums and
        identities."""
        from diracula import pathsum as P

        if isinstance(v, P.Outer):
            ket = Prog("leaf", (state_terms(self.vs, v.ket),))
            bra = Prog(
                "leaf",
                (state_terms(self.vs, P.State(v.bra.widths, v.bra.terms, False, v.bra.dims)),),
            )
            return Prog("ten", (IN, ket, bra))
        if isinstance(v, P.Scaled):
            return Prog(
                "mul",
                (Prog("leaf", (scalar_terms(self.vs, v.factor),)), self.printed_op(v.op, lay)),
            )
        if isinstance(v, P.OpSum):
            out = self.printed_op(v.ops[0], lay)
            for o in v.ops[1:]:
                out = Prog("add", (out, self.printed_op(o, lay)))
            return out
        if isinstance(v, P.Identity):
            return self.ident(lay)
        raise CertifyError(f"the printed operator {type(v).__name__}")

    def op_layout(self, v: Any) -> Layout:
        """The input layout of a printed operator."""
        from diracula import pathsum as P

        if isinstance(v, P.Outer):
            return tuple(v.bra.widths), tuple(v.bra.dims)
        if isinstance(v, P.Scaled):
            return self.op_layout(v.op)
        if isinstance(v, P.OpSum):
            for o in v.ops:
                try:
                    return self.op_layout(o)
                except CertifyError:
                    continue
        raise CertifyError("an operator of unknown layout")

    def check_rg(self, p: Prog, rhs: Sequence[ATm], rg: Sequence[tuple[int, Y.DMon]]) -> None:
        """The hints of a closing check with the variables of ``rg`` in their ranges."""
        fl, pw = self.floors(), self.vs.pw
        e = prog_sym(p, fl, pw)
        if e is None:
            raise CertifyError("the program does not translate")
        d = [Z.rg_t(rg, t) for t in e + Z.ax_neg(rhs)]
        if Z.nf_a(fl, pw, d):
            raise CertifyError("the normaliser does not close the difference")
        self.sym, self.nfs, self.nfs2, self.rounds = (
            e,
            [Z.norm_a(fl, pw, Z.AROUNDS, t) for t in d],
            [],
            1,
        )
        self.ctx_used, self.real_rs = False, []

    def rg_decl(self, rg: Sequence[tuple[int, Y.DMon]]) -> str:
        items = ", ".join(f"({v}, {self.text.dm(d)})" for v, d in rg)
        return (
            "/-- The output and input variables with their ranges `0 ≤ ν v < D`. -/\n"
            f"def RG : List (ℕ × DMon) := [{items}]\n"
        )

    def certify_op(self, label: str, node: object, values: Mapping[str, object], value: Any) -> str:
        """The Lean source certifying that the shown operator ``node`` equals its printed form."""
        self.setup(len(self.log))
        self.reader = Reader(self.parse, values, self.funcs)
        lay = self.op_layout(value)
        q, _ = self.op(node, lay)
        pl = self.declare(("opl", label), "shown", f"show({label})", q)
        pr = self.declare(
            ("opr", label), "printed", f"the printed value of {label}", self.printed_op(value, lay)
        )
        er = prog_sym(pr, self.floors(), self.vs.pw)
        if er is None:
            raise CertifyError("the printed operator does not translate")
        if counts(pl) or counts(pr):
            raise CertifyError("an operator with loops")
        rgd: list[str] = []
        try:
            self.check(pl, er)
            if self.real_rs or self.ctx_used:
                raise CertifyError("an operator with facts about its parameters")
            stmt = f"{pl.name}.sem V = {pr.name}.sem V"
            proof = f"certify_eq_lit V hρ FL FLOK PW PWOK {pl.name} {pr.name} SYM RSYM NF "
        except CertifyError:
            levels = self.levels(lay)
            rg = [(i, m) for i, m in enumerate(levels)] + [
                (IN + i, m) for i, m in enumerate(levels)
            ]
            self.check_rg(pl, er, rg)
            rgd = [self.rg_decl(rg)]
            stmt = f"∀ ν : ℕ → ℤ, RgOK V RG ν → {pl.name}.sem V ν = {pr.name}.sem V ν"
            proof = f"certify_eq_rg V hρ FL FLOK PW PWOK RG {pl.name} {pr.name} SYM RSYM NF "
        proof += DECIDES + " (by decide +kernel) (by decide +kernel)"
        extra = [
            *rgd,
            "/-- The printed operator as one expression. -/\ndef RSYM : List ATm :=\n  "
            + f"{self.text.ex(er)}\n",
            *self.hint_decls(),
        ]
        return self.source(label, f"{self.script}_show_{_clean(label)}", stmt, proof, extra, [])

    def certify_action(
        self, label: str, node: object, values: Mapping[str, object], probe: State, image: State
    ) -> str:
        """The Lean source certifying that the shown operator ``node`` maps the basis ket
        ``probe`` of free value to the printed ``image``."""
        self.setup(len(self.log))
        self.reader = Reader(self.parse, values, self.funcs)
        for t in probe.terms:
            for v in t.kets:
                for x in sympy.sympify(v).free_symbols:
                    if x not in self.vs.ids:
                        self.vs.ids[x] = PAR + 500 + len(self.vs.ids)
                        self.vs.params.append(x.name)
        lay = (tuple(probe.widths), tuple(probe.dims))
        q, _ = self.op(node, lay)
        pin = Prog("leaf", (state_terms(self.vs, probe),))
        pl = self.declare(
            ("act", label),
            "shown",
            f"show({label}) on a basis ket",
            Prog("app", (self.levels(lay), q, pin)),
        )
        rhs = state_terms(self.vs, image)
        rgd: list[str] = []
        try:
            self.check(pl, rhs)
            if self.real_rs:
                raise CertifyError("an operator with real parameters under conjugation")
            stmt, proof = self.lit_stmt(pl, "printed"), self.lit_proof(pl, "printed", "")
        except CertifyError:
            if counts(pl):
                raise
            levels = self.levels(lay)
            ins = []
            for i, v in enumerate(probe.terms[0].kets):
                for x in sympy.sympify(v).free_symbols:
                    ins.append((self.vs.ids[x], levels[i]))
            rg = [(i, m) for i, m in enumerate(levels)] + ins
            self.check_rg(pl, rhs, rg)
            rgd = [self.rg_decl(rg)]
            stmt = f"∀ ν : ℕ → ℤ, RgOK V RG ν → {pl.name}.sem V ν = axDen V ν printed"
            proof = f"certify_rg V hρ FL FLOK PW PWOK RG {pl.name} printed SYM NF " + DECIDES
        extra = [
            *rgd,
            (
                f"/-- The printed image of the basis ket under {label}. -/\n"
                "def printed : List ATm :=\n  "
                f"{self.text.ex(rhs)}\n"
            ),
            *self.hint_decls(),
        ]
        return self.source(label, f"{self.script}_show_{_clean(label)}", stmt, proof, extra, [])

    def certify_scalar(
        self, name: str, node: object, upto: int, values: Mapping[str, object], value: sympy.Expr
    ) -> str:
        """The Lean source certifying the printed value of the scalar ``name``."""
        self.setup(upto)
        self.reader = Reader(self.parse, values, self.funcs)
        p = self.declare(
            ("scalar", name), f"value_{_clean(name)}", f"var {name} = ...", self.scalar_prog(node)
        )
        rhs = scalar_terms(self.vs, value)
        self.check(p, rhs)
        printed = f"printed_{_clean(name)}"
        extra = [
            (
                f"/-- The printed value of {name}. -/\ndef {printed} : List ATm :=\n  "
                f"{self.text.ex(rhs)}\n"
            ),
            *self.hint_decls(),
        ]
        return self.source(
            name,
            f"{self.script}_{_clean(name)}",
            self.lit_stmt(p, printed),
            self.lit_proof(p, printed, ""),
            extra,
            [],
        )

    def certify_assert(
        self,
        label: str,
        left: object,
        right: object,
        upto: int,
        values: Mapping[str, object],
        source: str,
    ) -> str:
        """The Lean source certifying the assertion ``left == right``."""
        self.setup(upto)
        self.reader = Reader(self.parse, values, self.funcs)
        pl = self.declare(("lhs", label), "lhs", f"assert {source}", self.scalar_prog(left))
        pr = self.declare(("rhs", label), "rhs", f"assert {source}", self.scalar_prog(right))
        er = prog_sym(pr, self.floors(), self.vs.pw)
        if er is None:
            raise CertifyError("the right side does not translate")
        self.check(pl, er)
        extra = [
            (
                f"/-- The right side as one expression. -/\ndef RSYM : List ATm :=\n  "
                f"{self.text.ex(er)}\n"
            ),
            *self.hint_decls(),
        ]
        if self.real_rs:
            stmt = (
                f"∀ ν : ℕ → ℤ, (∀ c ∈ {pl.name}.counts ++ {pr.name}.counts, 0 ≤ ipDen ν c) "
                f"→ {pl.name}.sem V ν = {pr.name}.sem V ν"
            )
            proof = (
                f"certify_eq_{self.real_kind}_c V hρ FL FLOK PW PWOK {self.rs_names()} "
                f"{pl.name} {pr.name} SYM RSYM NF "
                + DECIDES
                + " (by decide +kernel) (by decide +kernel)"
            )
        elif self.ctx_used:
            hyps, names = self.wl_intro()
            stmt = (
                f"∀ ν : ℕ → ℤ, {hyps}(∀ c ∈ {pl.name}.counts ++ {pr.name}.counts, "
                f"0 ≤ ipDen ν c) → {pl.name}.sem V ν = {pr.name}.sem V ν"
            )
            two = self.rounds == 2
            proof = (
                f"fun ν {names} => certify_eq_w{'2' if two else ''}_c V hρ FL FLOK PW PWOK CTX "
                f"{pl.name} {pr.name} SYM RSYM NF {'NF2 ' if two else ''}{DECIDES} "
                f"{'(by decide +kernel) ' if two else ''}(by decide +kernel) (by decide +kernel) ν "
                f"(CTXOK ν ⟪ASM⟫ {names})"
            )
        elif counts(pl) or counts(pr):
            stmt = (
                f"∀ ν : ℕ → ℤ, (∀ c ∈ {pl.name}.counts ++ {pr.name}.counts, 0 ≤ ipDen ν c) "
                f"→ {pl.name}.sem V ν = {pr.name}.sem V ν"
            )
            proof = (
                f"certify_eq_lit_c V hρ FL FLOK PW PWOK {pl.name} {pr.name} SYM RSYM NF "
                + DECIDES
                + " (by decide +kernel) (by decide +kernel)"
            )
        else:
            stmt = f"{pl.name}.sem V = {pr.name}.sem V"
            proof = (
                f"certify_eq_lit V hρ FL FLOK PW PWOK {pl.name} {pr.name} SYM RSYM NF "
                + DECIDES
                + " (by decide +kernel) (by decide +kernel)"
            )
        return self.source(
            f"assert {source}", f"{self.script}_{_clean(label)}", stmt, proof, extra, []
        )

    def certify_dist(
        self, name: str, label: str, upto: int, values: Mapping[str, object], raw: Any, mapped: Any
    ) -> str:
        """The Lean source certifying the measured distribution of ``|label>``: each branch's
        probability is ``|<value|psi>|^2``, the probabilities sum to 1 and ``<psi|psi> = 1``;
        with ``mapped``, every outcome maps to its printed value."""
        index = None
        for k in range(upto - 1, -1, -1):
            if self.log[k].name == label and self.log[k].kind != "opaque":
                index = k
                break
        if index is None:
            raise CertifyError(f"|{label}> has no recorded definition before the measurement")
        self.setup(upto)
        psi, lay = self.state(index)
        levels = self.levels(lay)
        decls: list[str] = []
        parts: list[tuple[str, str, str, str]] = []
        total: list[ATm] = []
        for b_i, br in enumerate(raw.branches, 1):
            for b in br.free:
                if b.lo != 0:
                    raise CertifyError("a branch index that does not start at 0")
                self.vs.ids.setdefault(b.symbol, PAR + 500 + len(self.vs.ids))
                self.vs.params.append(b.symbol.name)
            ket = Ket(lay[0], lay[1], ((sympy.Integer(1), (), tuple(br.registers)),))
            leaf = Prog("leaf", (ket_terms(self.vs, ket),))
            amp = Prog("inn", (levels, leaf, psi))
            prob = self.declare(
                ("prob", b_i),
                f"prob_{b_i}",
                f"branch {b_i}: |<value|{label}>|^2",
                Prog("mul", (Prog("cnj", (amp,)), amp)),
            )
            d, pr = self.lit(
                prob, scalar_terms(self.vs, br.prob), f"_{b_i}", f"The probability of branch {b_i}."
            )
            decls.append(d)
            parts.append(
                (
                    f"branch {b_i} of measure|{label}>: probability {br.prob}",
                    f"{self.script}_{_clean(name)}_branch_{b_i}",
                    self.lit_stmt(prob, f"R_{b_i}"),
                    pr,
                )
            )
            sums = []
            for b in br.free:
                sid = self.vs.bound(sympy.Dummy(b.symbol.name, integer=True), b.hi + 1)
                sums.append((sid, self.vs.dmon(b.hi + 1)))
            for t in scalar_terms(self.vs, br.prob.xreplace({b.symbol: b.symbol for b in br.free})):
                total.append((t[0], tuple(sums) + t[1], t[2], t[3], t[4], t[5]))
        tot = self.declare(
            ("total",), "total", f"the probabilities of measure|{label}>", Prog("leaf", (total,))
        )
        d, pr = self.lit(
            tot, scalar_terms(self.vs, sympy.Integer(1)), "_total", "The total probability."
        )
        decls.append(d)
        parts.append(
            (
                f"the probabilities of measure|{label}> sum to 1",
                f"{self.script}_{_clean(name)}_total",
                self.lit_stmt(tot, "R_total"),
                pr,
            )
        )
        norm = self.declare(
            ("norm",), "norm", f"<{label}|{label}>", Prog("inn", (levels, psi, psi))
        )
        d, pr = self.lit(norm, scalar_terms(self.vs, sympy.Integer(1)), "_norm", "One.")
        decls.append(d)
        parts.append(
            (
                f"<{label}|{label}> = 1",
                f"{self.script}_{_clean(name)}_norm",
                self.lit_stmt(norm, "R_norm"),
                pr,
            )
        )
        if mapped is not None:
            parts.append(self.pushforward(name, raw, mapped))
        first = parts[0]
        return self.source(first[0], first[1], first[2], first[3], decls, parts[1:])

    def certify_mixed(self, name: str, upto: int, value: Any) -> str:
        """The Lean source certifying the density matrix a full measurement of ``|name>``
        leaves: vectorised, ``[o = o'] psi(o) conj(psi(o'))``."""
        index = None
        for k in range(upto - 1, -1, -1):
            if self.log[k].name == name and self.log[k].kind != "opaque":
                index = k
                break
        if index is None:
            raise CertifyError(f"|{name}> has no recorded definition before the measurement")
        self.setup(upto)
        psi, lay = self.state(index)
        k = len(lay[0])
        levels = self.levels(lay)
        diag = tuple((lv, Y.ip_sub(Y.ip_v(i), Y.ip_v(k + i))) for i, lv in enumerate(levels))
        rho = self.declare(
            ("mixed", name),
            f"rho_{_clean(name)}",
            f"measure|{name}>: the mixture of the outcomes, vectorised",
            Prog(
                "mul",
                (
                    Prog("leaf", ([(Y.of_q(1), (), (), diag, (), ())],)),
                    Prog("ten", (k, psi, Prog("cnj", (psi,)))),
                ),
            ),
        )
        rhs = state_terms(self.vs, value.vec)
        d, pr = self.lit(rho, rhs, "", f"The printed density matrix of |{name}>, vectorised.")
        return self.source(
            f"the density matrix of |{name}> after measuring it",
            f"{self.script}_{_clean(name)}",
            self.lit_stmt(rho, "R"),
            pr,
            [d],
            [],
        )

    def pushforward(self, name: str, raw: Any, mapped: Any) -> tuple[str, str, str, str]:
        """Every outcome of ``raw`` maps to the value of a branch of ``mapped`` of the same
        probability, the branches' values distinct."""
        fn = self.outcome_fn
        if len(mapped.branches) == 1 and not mapped.branches[0].free:
            return self.pushforward_one(name, raw, mapped)
        used: list[int] = []
        claims = []
        for br in raw.branches:
            image = sympy.simplify(fn(br.value))
            match = None
            for m_i, mb in enumerate(mapped.branches):
                if m_i in used or len(mb.free) != len(br.free):
                    continue
                sub = {f.symbol: g.symbol for f, g in zip(mb.free, br.free, strict=True)}
                same_range = all(
                    sympy.expand(f.hi - g.hi) == 0 for f, g in zip(mb.free, br.free, strict=True)
                )
                if (
                    same_range
                    and self.same_value(sympy.sympify(mb.value).xreplace(sub), image, br.free)
                    and sympy.simplify(sympy.sympify(mb.prob).xreplace(sub) - br.prob) == 0
                ):
                    match = m_i
                    break
            if match is None:
                raise CertifyError("an outcome whose image is no printed branch of its probability")
            used.append(match)
            names = {**self.size_names(), **{b.symbol: f"k{j}" for j, b in enumerate(br.free)}}
            binders = " ".join(
                f"∀ {names[b.symbol]} : ℕ, {names[b.symbol]} < {lean_nat(b.hi + 1, names)} →"
                for b in br.free
            )
            target = sympy.sympify(mapped.branches[match].value).xreplace(
                {
                    f.symbol: g.symbol
                    for f, g in zip(mapped.branches[match].free, br.free, strict=True)
                }
            )
            claims.append(
                f"{binders} {lean_nat(fn(br.value), names)} = {lean_nat(target, names)}".strip()
            )
        if len(used) != len(mapped.branches):
            raise CertifyError("a printed branch that is no image")
        if any(true_div(fn(br.value)) for br in raw.branches):
            return self.pushforward_rat(name, raw, mapped, used)
        distinct = []
        for a_i, ma in enumerate(mapped.branches):
            for b_i, mb in enumerate(mapped.branches):
                if b_i < a_i:
                    continue
                na = {**self.size_names(), **{f.symbol: f"a{j}" for j, f in enumerate(ma.free)}}
                nb = {**self.size_names(), **{f.symbol: f"b{j}" for j, f in enumerate(mb.free)}}
                bind = " ".join(
                    [
                        f"∀ {na[f.symbol]} : ℕ, {na[f.symbol]} < {lean_nat(f.hi + 1, na)} →"
                        for f in ma.free
                    ]
                    + [
                        f"∀ {nb[f.symbol]} : ℕ, {nb[f.symbol]} < {lean_nat(f.hi + 1, nb)} →"
                        for f in mb.free
                    ]
                )
                va, vb = lean_nat(ma.value, na), lean_nat(mb.value, nb)
                if a_i == b_i:
                    if not ma.free:
                        continue
                    eqs = " ∧ ".join(
                        f"{na[f.symbol]} = {nb[g.symbol]}"
                        for f, g in zip(ma.free, mb.free, strict=True)
                    )
                    distinct.append(f"{bind} {va} = {vb} → {eqs}")
                else:
                    distinct.append(f"{bind} {va} ≠ {vb}")
        allc = claims + distinct
        hyps, haves = self.div_facts()
        tac = (
            "first | omega "
            "| (intro k hk; rw [Nat.add_div_of_dvd_right (dvd_mul_of_dvd_left HD _), "
            "Nat.div_eq_of_lt hk, add_zero]) "
            "| (intro k hk; rw [Nat.add_div_of_dvd_right (Dvd.dvd.mul_left HD _), "
            "Nat.div_eq_of_lt hk, add_zero]) "
            "| (intro a ha b hb h; obtain ⟨q, hq⟩ := HD; "
            "have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq; omega); "
            "rw [hq, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_div_cancel_left _ HR, "
            "Nat.mul_div_cancel_left _ HR] at h; exact Nat.eq_of_mul_eq_mul_left hq0 h)"
        )
        body = (
            f"by ({tac})" if len(allc) == 1 else "⟨" + ", ".join(f"by ({tac})" for _ in allc) + "⟩"
        )
        stmt = " ∧ ".join(f"({c})" for c in allc)
        if hyps:
            stmt = " → ".join(hyps) + " → " + stmt
            intros = " ".join(f"h_a{i}" for i in range(len(hyps)))
            body = f"by\n  intro {intros}\n{haves}  exact {body}"
        return (
            (
                "every outcome of the measurement maps to a printed value of its probability, the "
                "printed values distinct"
            ),
            f"{self.script}_{_clean(name)}_values",
            stmt,
            body,
        )

    def pushforward_rat(
        self, name: str, raw: Any, mapped: Any, used: Sequence[int]
    ) -> tuple[str, str, str, str]:
        """``pushforward`` over ``ℚ``: each floor of an image read as its quotient under the
        assumed divisibility ``D2 = D1 q``."""
        fn = self.outcome_fn
        hyps, haves = self.div_facts()
        div = next(
            (
                x.lhs.args
                for x in self.assumptions
                if isinstance(x, sympy.Eq) and x.rhs == 0 and isinstance(x.lhs, sympy.Mod)
            ),
            None,
        )
        if div is None:
            raise CertifyError("a rational outcome without an assumed divisibility")
        d2, d1 = div
        qs = sympy.Symbol("q_", integer=True, positive=True)
        nz = (
            "first | exact Nat.cast_ne_zero.2 (by omega) "
            "| exact Nat.cast_ne_zero.2 (pow_ne_zero _ (by omega)) "
            "| exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))"
        )
        q0 = (
            "obtain ⟨q, hq⟩ := HD; have hq0 : 0 < q := Nat.pos_of_ne_zero "
            "(by rintro rfl; simp at hq <;> omega); "
            "have h2 : (q : ℚ) ≠ 0 := (by exact_mod_cast hq0.ne'); "
        )
        claims: list[tuple[str, str]] = []
        for br, m_i in zip(raw.branches, used, strict=True):
            names = {**self.size_names(), **{b.symbol: f"k{j}" for j, b in enumerate(br.free)}}
            nq = {**names, qs: "q"}
            image = fn(br.value)
            mb = mapped.branches[m_i]
            target = sympy.sympify(mb.value).xreplace(
                {f.symbol: g.symbol for f, g in zip(mb.free, br.free, strict=True)}
            )
            binders = " ".join(
                f"∀ {names[b.symbol]} : ℕ, {names[b.symbol]} < {lean_nat(b.hi + 1, names)} →"
                for b in br.free
            )
            intro = " ".join(f"k{j} hk{j}" for j in range(len(br.free)))
            hks = ", ".join(f"hk{j}" for j in range(len(br.free)))
            hfl, rws = [], []
            for i, fl in enumerate(sorted(sympy.sympify(image).atoms(sympy.floor), key=str)):
                num, den = sympy.fraction(sympy.together(fl.args[0]))
                w, _ = sympy.div(
                    sympy.expand(num.subs(d2, d1 * qs)), sympy.expand(den.subs(d2, d1 * qs))
                )
                hfl.append(
                    f"have hfl{i} : {lean_nat(fl, names)} = {lean_nat(w, nq)} := "
                    f"Nat.div_eq_of_lt_le (by (try rw [hq]) <;> nlinarith [{hks}]) "
                    f"(by (try rw [hq]) <;> nlinarith [{hks}]); "
                )
                rws.append(f"hfl{i}")
            den_t = lean_rat(sympy.fraction(sympy.together(target))[1], names)
            tac = (
                f"intro {intro}; {q0}{''.join(hfl)}"
                + (f"rw [{', '.join(rws)}]; " if rws else "")
                + f"have h1 : {den_t} ≠ 0 := (by {nz}); "
                + "(try rw [hq]); first | (push_cast; field_simp; done) "
                + "| (push_cast; field_simp; ring)"
            )
            claims.append(
                (f"{binders} {lean_rat(image, names)} = {lean_rat(target, names)}".strip(), tac)
            )
        for a_i, ma in enumerate(mapped.branches):
            for b_i, mb in enumerate(mapped.branches):
                if b_i < a_i or (a_i == b_i and not ma.free):
                    continue
                na = {**self.size_names(), **{f.symbol: f"a{j}" for j, f in enumerate(ma.free)}}
                nb = {**self.size_names(), **{f.symbol: f"b{j}" for j, f in enumerate(mb.free)}}
                bind = " ".join(
                    [
                        f"∀ {na[f.symbol]} : ℕ, {na[f.symbol]} < {lean_nat(f.hi + 1, na)} →"
                        for f in ma.free
                    ]
                    + [
                        f"∀ {nb[f.symbol]} : ℕ, {nb[f.symbol]} < {lean_nat(f.hi + 1, nb)} →"
                        for f in mb.free
                    ]
                )
                va, vb = lean_rat(ma.value, na), lean_rat(mb.value, nb)
                ia = " ".join(f"a{j} ha{j}" for j in range(len(ma.free)))
                ib = " ".join(f"b{j} hb{j}" for j in range(len(mb.free)))
                den_t = lean_rat(sympy.fraction(sympy.together(ma.value))[1], na)
                if a_i == b_i:
                    eqs = " ∧ ".join(
                        f"{na[f.symbol]} = {nb[g.symbol]}"
                        for f, g in zip(ma.free, mb.free, strict=True)
                    )
                    tac = (
                        f"intro {ia} {ib} h; have h1 : {den_t} ≠ 0 := (by {nz}); "
                        "first | (rw [div_left_inj' h1] at h; exact_mod_cast h) "
                        "| (field_simp at h; exact_mod_cast h)"
                    )
                    claims.append((f"{bind} {va} = {vb} → {eqs}", tac))
                else:
                    claims.append((f"{bind} {va} ≠ {vb}", f"intro {ia} {ib}; norm_num"))
        stmt = " ∧ ".join(f"({c})" for c, _ in claims)
        parts = [f"by\n    {t}" for _, t in claims]
        body = parts[0] if len(parts) == 1 else "⟨" + ",\n  ".join(f"({p})" for p in parts) + "⟩"
        if hyps:
            stmt = " → ".join(hyps) + " → " + stmt
            intros = " ".join(f"h_a{i}" for i in range(len(hyps)))
            body = f"by\n  intro {intros}\n{haves}  exact {body}"
        return (
            (
                "every outcome of the measurement maps to a printed value of its probability, the "
                "printed values distinct"
            ),
            f"{self.script}_{_clean(name)}_values",
            stmt,
            body,
        )

    def same_value(self, a: sympy.Expr, b: sympy.Expr, free: Sequence[Any]) -> bool:
        """Whether ``a = b`` given the assumed divisibilities and the indices' ranges."""
        if sympy.simplify(a - b) == 0:
            return True
        subs = {}
        for x in self.assumptions:
            if isinstance(x, sympy.Eq) and x.rhs == 0 and isinstance(x.lhs, sympy.Mod):
                d2, d1 = x.lhs.args
                subs[d2] = d1 * sympy.Dummy("q", integer=True, positive=True)
        if not subs:
            return False
        a2, b2 = sympy.sympify(a).subs(subs), sympy.sympify(b).subs(subs)
        a2, b2 = sympy.simplify(a2), sympy.simplify(b2)
        zero = {}
        for f in free:
            for fl in a2.atoms(sympy.floor) | b2.atoms(sympy.floor):
                num, den = sympy.fraction(sympy.together(fl.args[0]))
                if num == f.symbol and sympy.expand(den - (f.hi + 1)) == 0:
                    zero[fl] = sympy.Integer(0)
        return bool(sympy.simplify(a2.xreplace(zero) - b2.xreplace(zero)) == 0)

    def size_names(self) -> dict[sympy.Symbol, str]:
        """Lean names of the dimension and width symbols as natural numbers."""
        out: dict[sympy.Symbol, str] = {}
        for i, s in enumerate(self.vs.dsyms):
            out[s] = f"(V.ρ.dv {i})"
        for w in self.vs.widths:
            out[w] = w.name
        return out

    def div_facts(self) -> tuple[list[str], str]:
        """The assumptions as hypotheses, and ``HD : D1 ∣ D2``, ``HR : 0 < D1`` over ``ℕ`` for
        the first assumed divisibility."""
        props = [f"({self.lean_prop(a)})" for a in self.assumptions]
        for i, a in enumerate(self.assumptions):
            if isinstance(a, sympy.Eq) and a.rhs == 0 and isinstance(a.lhs, sympy.Mod):
                names = self.size_names()
                d2, d1 = (lean_nat(x, names) for x in a.lhs.args)
                haves = (
                    f"  have HD : {d1} ∣ {d2} := Int.natCast_dvd_natCast.1 (by push_cast; "
                    f"exact Int.dvd_of_emod_eq_zero h_a{i})\n"
                    f"  have HR : 0 < {d1} := by first | omega | positivity\n"
                )
                return props, haves
        return props, ""

    def pushforward_one(self, name: str, raw: Any, mapped: Any) -> tuple[str, str, str, str]:
        """Every outcome of ``raw`` maps to the value of the single branch of ``mapped``."""
        target = mapped.branches[0].value
        claims = []
        for br in raw.branches:
            names = {b.symbol: f"k{j}_{b.symbol.name.strip('_')}" for j, b in enumerate(br.free)}
            image = self.outcome_fn(br.value)
            binders = "".join(
                f"∀ {names[b.symbol]} : ℕ, {names[b.symbol]} < {b.hi + 1} → " for b in br.free
            )
            claims.append(f"{binders}{lean_nat(image, names)} = {lean_nat(target, names)}")
        stmt = " ∧ ".join(f"({c})" for c in claims)
        return (
            f"every outcome of the measurement maps to {target}",
            f"{self.script}_{_clean(name)}_values",
            stmt,
            "by omega" if len(claims) == 1 else "⟨" + ", ".join("by omega" for _ in claims) + "⟩",
        )

    def lean_int(self, e: sympy.Basic) -> str:
        """An integer expression over dimension and width symbols and parameters as Lean
        text."""
        vs = self.vs
        if isinstance(e, sympy.Integer):
            return f"({int(e)} : ℤ)"
        if isinstance(e, sympy.Symbol):
            if e in vs.dsyms:
                return f"(V.ρ.dv {vs.dsyms.index(e)} : ℤ)"
            if e in vs.widths:
                return f"({e.name} : ℤ)"
            return f"ν {vs.var(e)}"
        if isinstance(e, sympy.Add):
            return "(" + " + ".join(self.lean_int(a) for a in e.args) + ")"
        if isinstance(e, sympy.Mul):
            return "(" + " * ".join(self.lean_int(a) for a in e.args) + ")"
        if isinstance(e, sympy.Pow) and e.exp.is_Integer and int(e.exp) >= 0:
            return f"({self.lean_int(e.base)} ^ {int(e.exp)})"
        if isinstance(e, sympy.Pow) and e.exp in vs.widths:
            return f"({self.lean_int(e.base)} ^ {e.exp.name})"
        if isinstance(e, sympy.Mod):
            return f"({self.lean_int(e.args[0])} % {self.lean_int(e.args[1])})"
        raise CertifyError(f"the assumption term {e}")

    def lean_prop(self, a: sympy.Basic) -> str:
        """An assumption as a Lean proposition."""
        ops = {
            sympy.Eq: "=",
            sympy.Ne: "≠",
            sympy.Lt: "<",
            sympy.Le: "≤",
            sympy.Gt: ">",
            sympy.Ge: "≥",
        }
        for cls, op in ops.items():
            if isinstance(a, cls):
                return f"{self.lean_int(a.lhs)} {op} {self.lean_int(a.rhs)}"
        if isinstance(a, sympy.And):
            return " ∧ ".join(f"({self.lean_prop(x)})" for x in a.args)
        raise CertifyError(f"the assumption {a}")

    def assumed(self, stmt: str, proof: str) -> tuple[str, str]:
        """The statement and proof with every assumption a hypothesis on each valuation."""
        if not self.assumptions:
            return stmt, proof
        props = [self.lean_prop(a) for a in self.assumptions]
        proof = proof.replace("⟪ASM⟫", " ".join(f"h_a{i}" for i in range(len(props))))
        if stmt.startswith("∀ ν : ℕ → ℤ, "):
            hyp = " → ".join(f"({p})" for p in props)
            under = " ".join(f"h_a{i}" for i in range(len(props)))
            return (
                f"∀ ν : ℕ → ℤ, {hyp} → {stmt[len('∀ ν : ℕ → ℤ, ') :]}",
                f"fun ν {under} => ({proof}) ν",
            )
        if " = fun ν => " in stmt:
            lhs, rhs = stmt.split(" = fun ν => ", 1)
            body = f"{lhs} ν = {rhs}"
        else:
            lhs, rhs = stmt.split(" = ", 1)
            body = f"{lhs} ν = {rhs} ν"
        hyp = " → ".join(f"({p})" for p in props)
        under = " ".join(f"h_a{i}" for i in range(len(props)))
        return (f"∀ ν : ℕ → ℤ, {hyp} → {body}", f"fun ν {under} => congrFun ({proof}) ν")

    def source(
        self,
        what: str,
        thm: str,
        stmt: str,
        proof: str,
        extra: Sequence[str],
        more: Sequence[tuple[str, str, str, str]],
    ) -> str:
        vs = self.vs
        extra, more = list(extra), list(more)
        for i, (psi, levels, kt, norm) in enumerate(self.nrm_obls):
            inn = self.declare(
                ("nrm_in", i),
                f"ninner_{i}",
                f"<s|s> of normalise #{i}",
                Prog("inn", (levels, psi, psi)),
            )
            kleaf = Prog("leaf", ([kt],))
            sb = self.declare(
                ("nrm_b", i),
                f"nunit_{i}",
                f"k² <s|s> of normalise #{i}",
                Prog("mul", (Prog("mul", (kleaf, kleaf)), inn)),
            )
            db, pb = self.lit(sb, scalar_terms(self.vs, sympy.Integer(1)), f"_n{i}", "One.")
            hyb, ub = self.lit_use(sb, pb, "hc")
            bind, hnames = self.binders(hyb)
            extra += [
                f"/-- The coefficient 1/({norm}). -/\ndef KT_n{i} : ATm :=\n  {self.text.tm(kt)}\n",
                db,
            ]
            more.append(
                (
                    f"normalise #{i} is its argument over the root of its norm",
                    f"{thm}_nrm_{i}",
                    (
                        f"∀ ν : ℕ → ℤ, {bind}(Prog.mul (.leaf [KT_n{i}]) {psi.name}).sem V ν = "
                        f"((Real.sqrt ({inn.name}.sem V ν).re : ℝ) : ℂ)⁻¹ * {psi.name}.sem V ν"
                    ),
                    (
                        f"fun ν {hnames} => nrm_scale V hρ _ {psi.name} KT_n{i} "
                        f"(by decide +kernel) ν {ub}"
                    ),
                )
            )
        self.nrm_obls = []
        for i, (title, prog, value) in enumerate(self.side_obls):
            prog = self.declare(("side", i, title), f"side_{i}", title, prog)
            d, pr = self.lit(prog, value, f"_s{i}", title)
            extra.append(d)
            more.append((title, f"{thm}_side_{i}", self.lit_stmt(prog, f"R_s{i}"), pr))
        self.side_obls = []
        stmt, proof = self.assumed(stmt, proof)
        more = [
            (w, t, *self.assumed(st, pr))
            if " = " in st and not st.startswith("(")
            else (w, t, st, pr)
            for w, t, st, pr in more
        ]
        fl = self.floors()
        for i, s in enumerate(vs.dsyms):
            self.text.dms[(1, tuple([0] * i + [1]))] = f"dim_{_clean(s.name)}"
        dims = []
        for i, s in enumerate(vs.dsyms):
            shown = f"{vs.powers[s][0]}^{vs.powers[s][1]}" if s in vs.powers else s.name
            dims.append(
                f"/-- The dimension {shown}, `V.ρ.dv {i}`. -/\n"
                f"def dim_{_clean(s.name)} : DMon := ⟨1, {lean_nats([0] * i + [1])}⟩"
            )
        hyps = []
        for i, s in enumerate(vs.dsyms):
            if s not in vs.powers:
                hyps.append((f"h_{_clean(s.name)}", f"2 ≤ V.ρ.dv {i}"))
        for n in vs.widths:
            hyps.append((n.name, "ℕ"))
            if vs.needs_width:
                hyps.append((f"h_{n.name}", f"1 ≤ {n.name}"))
        lows = {}
        for s in vs.dsyms:
            if s in vs.powers:
                got = self.offset_low(vs.powers[s][1])
                if got is not None:
                    lows[got[0]] = got[1]
        for n, lo in lows.items():
            hyps.append((f"h_{n.name}_lo", f"{lo} ≤ {n.name}"))
        pw_cases = []
        for s, (base, n) in vs.powers.items():
            j = vs.dsyms.index(s)
            ex = exp_text(n)
            rhs = f"V.ρ.dv {vs.dsyms.index(base)} ^ {ex}" if base in vs.dsyms else f"{base} ^ {ex}"
            hname = f"h_{_clean(s.name)}"
            hyps.append((hname, f"V.ρ.dv {j} = {rhs}"))
            dnames = f"dim_{_clean(s.name)}" + (
                f", dim_{_clean(base.name)}" if base in vs.dsyms else ""
            )
            pw_cases.append(
                f"  · exact ⟨by simp [{dnames}, DMon.den, npow] <;> omega, {ex}, "
                f"by simp [{dnames}, DMon.den, npow, {hname}]⟩"
            )
        rs_lines: list[str] = []
        rsok = ""
        if self.real_any:
            for k in self.real_any:
                c = f"V.ρ.atom {2 * k}"
                hyps.append((f"h_re_{_clean(vs.catoms[k].name)}", f"starRingEnd ℂ ({c}) = {c}"))
            pats = " | ".join(["rfl"] * len(self.real_any))
            rs_lines = [
                (
                    "/-- The coefficient atoms of integer parameters, real. -/\n"
                    f"def RS : List ℕ := {lean_nats(self.real_any)}\n"
                )
            ]
            rsok = (
                "(fun j hj => by simp only [RS, List.mem_cons, List.not_mem_nil, or_false] at hj; "
                f"rcases hj with {pats} <;> assumption)"
            )
        usok = ""
        if self.unit_any:
            for k in self.unit_any:
                c = f"V.ρ.atom {2 * k}"
                hyps.append((f"h_un_{_clean(vs.catoms[k].name)}", f"{c} * starRingEnd ℂ ({c}) = 1"))
            pats = " | ".join(["rfl"] * len(self.unit_any))
            rs_lines.append(
                "/-- The coefficient atoms of angles, of modulus 1. -/\n"
                f"def US : List ℕ := {lean_nats(self.unit_any)}\n"
            )
            usok = (
                "(fun j hj => by simp only [US, List.mem_cons, List.not_mem_nil, or_false] at hj; "
                f"rcases hj with {pats} <;> assumption)"
            )
        hyp_text = " ".join(f"({a} : {b})" for a, b in hyps)
        args_text = " ".join(a for a, _ in hyps)
        fl_cases = []
        for i, s in enumerate(vs.dsyms):
            if s in vs.powers and fl[i] == 2:
                base, n = vs.powers[s]
                hb = f"h_{_clean(base.name)}" if base in vs.dsyms else "(by norm_num)"
                hn = f"h_{n.name}" if isinstance(n, sympy.Symbol) else "(by omega)"
                fl_cases.append(
                    f"  · simp only [flv, FL, List.getD_cons_succ, List.getD_cons_zero]\n"
                    f"    exact pow_floor _ _ _ h_{_clean(s.name)} {hb} {hn}"
                )
            else:
                fl_cases.append("  · simp [flv, FL] <;> omega")
        fl_cases.append("  · simp [flv, FL]")
        fl_proof = (
            "fun i => by\n  rcases i with "
            + " | ".join(["_"] * len(vs.dsyms) + ["i"])
            + "\n"
            + "\n".join(fl_cases)
        )
        pw_text = "[" + ", ".join(f"({self.text.dm(a)}, {self.text.dm(b)})" for a, b in vs.pw) + "]"
        if vs.pw:
            pw_proof = (
                "by\n  intro p hp\n  simp only [PW, List.mem_cons, List.not_mem_nil, "
                "or_false] at hp\n  rcases hp with "
                + " | ".join(["rfl"] * len(vs.pw))
                + "\n"
                + "\n".join(pw_cases)
            )
        else:
            pw_proof = "by intro p hp; simp [PW] at hp"
        ctx_lines: list[str] = []
        ctxok = ""
        if self.ctx_any:
            wl, dv = self.wl(), self.dv()
            wl_text = ", ".join(f"({v}, {self.text.dm(d)}, {self.text.dm(n)})" for v, d, n in wl)
            dv_text = ", ".join(f"({self.text.dm(a)}, {self.text.dm(b)})" for a, b in dv)
            vs_used: list[tuple[int, str]] = []
            for v, _, _ in wl:
                if (v, vs.params[v - PAR]) not in vs_used:
                    vs_used.append((v, vs.params[v - PAR]))
            props = [self.lean_prop(a) for a in self.assumptions]
            hyp_a = " ".join(f"(h_a{i} : {q})" for i, q in enumerate(props))
            hyp_nu = " ".join(f"(h_ν{v} : ν {v} = ({n} : ℤ))" for v, n in vs_used)
            nus = [f"h_ν{v}" for v, _ in vs_used]

            def names(*ms: Y.DMon) -> list[str]:
                return [self.text.dms[m] for m in ms if m in self.text.dms]

            def power_h(m: Y.DMon) -> list[str]:
                return [f"h_{_clean(a.name)}" for a in vs.powers if vs.dmon(a) == m]

            def wl_case(d: Y.DMon, n: Y.DMon) -> str:
                simps = ", ".join([*names(d, n), "DMon.den", "npow", *nus, *power_h(n)])
                return f"    · exact ⟨by simp [{', '.join(nus)}], by simp [{simps}]⟩"

            wl_cases = [wl_case(d, n) for _, d, n in wl]
            dv_cases = []
            for (a, b), asm in zip(
                dv,
                [
                    k
                    for k, x in enumerate(self.assumptions)
                    if isinstance(x, sympy.Eq) and isinstance(x.lhs, sympy.Mod)
                ],
            ):
                simps = ", ".join([*names(a, b), "DMon.den", "npow", *power_h(a), *power_h(b)])
                pos = (
                    f"by simp only [{simps}, pow_zero, pow_one, one_mul, mul_one]; "
                    f"first | omega | exact Nat.pow_pos (by omega) | positivity"
                )
                dv_cases.append(
                    f"    · refine ⟨{pos}, {pos}, ?_⟩\n"
                    f"      simp only [{simps}, pow_zero, pow_one, one_mul, mul_one]\n"
                    "      exact Int.natCast_dvd_natCast.1 (by push_cast; "
                    f"exact Int.dvd_of_emod_eq_zero h_a{asm})"
                )

            def part(cases: list[str], n: int) -> str:
                if n == 0:
                    return "  · simp [CTX] at hw"
                return (
                    "  · simp only [CTX, List.mem_cons, List.not_mem_nil, or_false] at hw\n"
                    f"    rcases hw with {' | '.join(['rfl'] * n)}\n" + "\n".join(cases)
                )

            hyp_bind = " ".join(f"({a} : {b})" for a, b in hyps)
            ctx_lines = [
                (
                    f"/-- The context of the closing pass: loop counts that equal widths, assumed "
                    f"divisibilities. -/\n"
                    f"def CTX : Ctx := ⟨[], [{wl_text}], [{dv_text}]⟩\n"
                ),
                f"theorem ctxOK (V : LV){' ' if hyps else ''}{hyp_bind} "
                f"(ν : ℕ → ℤ) {hyp_a} {hyp_nu} : CtxOK V CTX ν := by\n"
                f"  refine ⟨fun j hj => by simp [CTX] at hj, fun w hw => ?_, fun w hw => ?_⟩\n"
                + part(wl_cases, len(wl))
                + "\n"
                + part(dv_cases, len(dv))
                + "\n",
            ]
            ctxok = f"(ctxOK V{' ' if hyps else ''}{' '.join(a for a, _ in hyps)})"
        params = ", ".join(
            [f"{n} is ν {PAR + k}" for k, n in enumerate(vs.params)]
            + [f"{c} is V.ρ.atom {2 * k}" for k, c in enumerate(vs.catoms)]
        )
        funcs = ", ".join(
            [f"{n} is V.fa {k}" for k, n in enumerate(vs.funcs)]
            + [
                f"k ↦ e^({sympy.sstr(e)}) at k = {kk} is V.fc {k}"
                for k, (kk, e) in enumerate(vs.cfuncs)
            ]
        )
        decls = [f"-- {c}\ndef {p.name} : Prog :=\n  {self.text.prog(p)}\n" for c, p in self.decls]
        sep = " " if hyp_text else ""
        flok = f"(flOK V{sep}{args_text})"
        pwok = f"(pwOK V{sep}{args_text})"
        lines = [
            "/-",
            f"  DiracULA certificate: {what} of {self.script}.ula",
            "  The program's meaning (Prog.sem) equals the stated value for every value of the",
            "  dimension and width symbols, parameters, functions and output registers.",
            "  Variables: output register i is ν i, gate input register i is ν (IN + i)"
            + (f"; {params}" if params else "")
            + (f"; {funcs}" if funcs else "")
            + ".",
            *(
                [
                    (
                        "  Built-in values (DiracULA.LSym.gfn): for N = V.ρ.dv i, "
                        "u_N = e^(i asin(N^(-1/2))) is apF V (GB + 4 i) and q_N = 1/(u_N + 1/u_N) "
                        "is apF V (GB + 4 i + 2); acos(1 - 2/N) = 2 asin(N^(-1/2)) and "
                        "sqrt(N - 1) = sqrt(N)/(2 q_N)."
                    )
                ]
                if vs.gsyms
                else []
            ),
            "-/",
            "import DiracULA.LGauss"
            if getattr(self, "gauss_any", False)
            else "import DiracULA.Lang",
            "",
            "open DiracULA.Sym DiracULA.LSym DiracULA.Lang",
            "",
            "set_option linter.unusedVariables false",
            "set_option linter.unusedTactic false",
            "set_option linter.unnecessarySeqFocus false",
            "",
            *(d + "\n" for d in dims),
            *decls,
            *extra,
            f"/-- The dimension floors. -/\ndef FL : List ℕ := {lean_nats(list(fl))}\n",
            f"/-- The dimensions that are powers. -/\ndef PW : List (DMon × DMon) := {pw_text}\n",
            f"theorem flOK (V : LV){sep}{hyp_text} : FloorOK FL V.ρ :=",
            f"  {fl_proof}\n",
            f"theorem pwOK (V : LV){sep}{hyp_text} : PowOK PW V.ρ := {pw_proof}\n",
            *ctx_lines,
            *rs_lines,
        ]
        for w, t, st, pr in [(what, thm, stmt, proof), *more]:
            if not t:
                continue
            lines += [
                "set_option maxHeartbeats 0 in",
                "set_option maxRecDepth 100000 in",
                f"/-- {w} -/",
                f"theorem {t} (V : LV) (hρ : V.ρ.OK){sep}{hyp_text} :",
                f"    {st} :=",
                "  "
                + pr.replace("RSOK", rsok)
                .replace("USOK", usok)
                .replace("FLOK", flok)
                .replace("PWOK", pwok)
                .replace("CTXOK", ctxok)
                .replace("⟪ASM⟫", ""),
                "",
                f"#print axioms {t}",
                "",
            ]
        return "\n".join(lines)
