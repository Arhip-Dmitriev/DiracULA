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

"""Adjoints, inverses and powers of operators, functions of operators, partial traces,
partial measurements and channels, over :mod:`diracula.pathsum` values.

An operator whose closed form depends on the registers it meets is a
:class:`~diracula.pathsum.Derived`, built on first application to each layout. Every
property it relies on (unitarity, ``U^2 == I`` and the like) is decided by symbolic
comparison on a basis ket of symbolic value; an undecided property is never assumed.
"""

from __future__ import annotations

import dataclasses
from collections.abc import Callable, Iterator, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from typing import TypeAlias

import sympy  # type: ignore[import-untyped]  # sympy ships no py.typed marker

from diracula import pathsum as P

Expr: TypeAlias = sympy.Expr
Layout: TypeAlias = tuple[tuple[Expr, ...], tuple[Expr, ...]]


class OperatorError(P.PathSumError):
    """An operation on operators with no closed form the engine can derive."""


_REAL: ContextVar[dict[sympy.Symbol, tuple[Expr, Expr]] | None] = ContextVar(
    "real_ranges", default=None
)


@contextmanager
def real_ranged(ranges: dict[sympy.Symbol, tuple[Expr, Expr]]) -> Iterator[None]:
    """A scope in which each real symbol of ``ranges`` lies in its inclusive ``(lo, hi)``."""
    token = _REAL.set({**(_REAL.get() or {}), **ranges})
    try:
        yield
    finally:
        _REAL.reset(token)


def _span_of(x: sympy.Symbol) -> tuple[Expr, Expr] | None:
    return (P._RANGES.get() or {}).get(x) or (_REAL.get() or {}).get(x)


def zero_form(e: Expr) -> Expr:
    """``e`` tidied, or 0 when its powers of i and -1 written as exponentials cancel."""
    e = P.tidy(real_parts(e))
    if e == 0 or e.has(sympy.Sum):
        return e
    phased = sympy.powsimp(P.expand(e.rewrite(sympy.exp)), force=True)
    return sympy.S.Zero if sympy.simplify(phased) == 0 else e


def _probe(
    widths: Sequence[Expr], dims: Sequence[Expr], name: str = "x"
) -> tuple[list[sympy.Dummy], dict[sympy.Symbol, tuple[Expr, Expr]]]:
    xs = [sympy.Dummy(name, integer=True, nonnegative=True) for _ in widths]
    ranges = {
        x: (sympy.S.Zero, sympy.sympify(d) ** w - 1)
        for x, w, d in zip(xs, widths, dims, strict=True)
    }
    return xs, ranges


def _truth(e: Expr) -> bool | None:
    z = zero_form(e)
    if z == 0:
        return True
    if z.is_number and not z.has(sympy.Sum):
        return bool(sympy.simplify(z) == 0)
    return None


def equal_on(
    a: P.Operator, b: P.Operator, widths: Sequence[Expr], dims: Sequence[Expr]
) -> bool | None:
    """Whether ``a == b`` on registers of ``widths`` and ``dims``, as ``||(a - b)|x>||^2 = 0``
    for a basis ket of symbolic value; None when undecided."""
    xs, ranges = _probe(widths, dims)
    with P.ranged(ranges):
        probe = P.basis_kets(xs, widths, dims)
        try:
            left, right = P.apply(a, probe), P.apply(b, probe)
            diff = P.add(left, P.scale(sympy.Integer(-1), right))
            return _truth(P.norm2(P.simplify(diff)))
        except P.PathSumError:
            return None


_UNITARY: dict[tuple[int, Layout], tuple[P.Operator, bool | None]] = {}


def is_unitary(op: P.Operator, widths: Sequence[Expr], dims: Sequence[Expr]) -> bool | None:
    """Whether ``adj(op) op == I`` on that layout, cached per operator and layout."""
    key = (id(op), (tuple(widths), tuple(dims)))
    if key not in _UNITARY:
        _UNITARY[key] = (op, equal_on(P.Compose((adjoint(op), op)), P.Identity(), widths, dims))
    return _UNITARY[key][1]


# --- adjoint -------------------------------------------------------------------------------

_ADJOINTS: dict[int, tuple[P.Gate, P.Gate]] = {}


def _square(g: P.Gate, img: P.State, widths: Sequence[Expr], dims: Sequence[Expr]) -> None:
    if not (
        len(img.widths) == len(widths)
        and all(map(P.same, img.widths, widths))
        and all(map(P.same, img.dims, dims))
    ):
        raise OperatorError(f"{g.name} changes the registers it acts on; it has no adjoint here")


def _kernel_gate(g: P.Gate, name: str, entry: object) -> P.Gate:
    """The gate ``|v> -> sum_x entry(v, x, image) |x>`` over the input registers of ``g``,
    with ``image = g|x>``; built once per layout with a symbolic ``v``."""
    templates: dict[Layout, tuple[list[sympy.Dummy], P.State]] = {}

    def template(
        widths: tuple[Expr, ...], dims: tuple[Expr, ...]
    ) -> tuple[list[sympy.Dummy], P.State]:
        key = (widths, dims)
        if key not in templates:
            vs, vranges = _probe(widths, dims, "v")
            bounds = [
                P.new_bound("x", 0, sympy.sympify(d) ** w - 1)
                for w, d in zip(widths, dims, strict=True)
            ]
            xs = [b.symbol for b in bounds]
            ranges = {x: (sympy.S.Zero, b.hi) for x, b in zip(xs, bounds, strict=True)}
            with P.ranged({**vranges, **ranges}):
                img = P.apply(g, P.basis_kets(xs, widths, dims))
                _square(g, img, widths, dims)
                amp = entry(vs, xs, img, widths, dims)  # type: ignore[operator]
                out = P.simplify(
                    P.State(widths, (P.Term(amp, tuple(bounds), tuple(xs)),), False, dims)
                )
            templates[key] = (vs, out)
        return templates[key]

    def fn(vals: tuple[Expr, ...], widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> P.State:
        vs, out = template(tuple(widths), tuple(dims))
        return P.substitute(out, dict(zip(vs, vals, strict=True)))

    return dataclasses.replace(
        g, name=name, fn=fn, oracle=False, checked=set(), base=g, source=name
    )


def _adjoint_gate(g: P.Gate) -> P.Gate:
    hit = _ADJOINTS.get(id(g))
    if hit is not None and hit[0] is g:
        return hit[1]

    def entry(
        vs: list[sympy.Dummy],
        xs: list[sympy.Dummy],
        img: P.State,
        widths: tuple[Expr, ...],
        dims: tuple[Expr, ...],
    ) -> Expr:
        bra = P.dagger(P.basis_kets(vs, widths, dims))
        return P.conjugate(P.inner(bra, img))

    out = _kernel_gate(g, _dagger_name(g.name), entry)
    _ADJOINTS[id(g)] = (g, out)
    _ADJOINTS[id(out)] = (out, g)
    return out


def _dagger_name(name: str) -> str:
    return name[:-1] if name.endswith("†") else f"{name}†"


def adjoint(op: P.Operator) -> P.Operator:
    """The conjugate transpose of ``op``."""
    if isinstance(op, P.Gate):
        return _adjoint_gate(op)
    if isinstance(op, P.Identity):
        return op
    if isinstance(op, P.Power):
        return P.Power(adjoint(op.op), op.count)
    if isinstance(op, P.Tensor):
        return P.Tensor(tuple(adjoint(f) for f in op.factors))
    if isinstance(op, P.Compose):
        return P.Compose(tuple(adjoint(o) for o in reversed(op.ops)))
    if isinstance(op, P.Outer):
        return P.Outer(P.dagger(op.bra), P.dagger(op.ket))
    if isinstance(op, P.Scaled):
        return P.Scaled(P.conjugate(sympy.sympify(op.factor)), adjoint(op.op))
    if isinstance(op, P.OpSum):
        return P.OpSum(tuple(adjoint(o) for o in op.ops))
    if isinstance(op, P.Derived):
        return P.Derived(_dagger_name(op.name), adjoint(op.like), lambda w, d: adjoint(op.at(w, d)))
    if isinstance(op, P.Family):
        return P.Family(adjoint(op.op), op.bounds)
    raise OperatorError(f"no adjoint of {op!r}")


def adjoint_mixed(m: P.Mixed) -> P.Mixed:
    """``rho^dagger``: ket and bra registers swapped, amplitudes conjugated."""
    k = m.count
    v = m.vec
    terms = [P.Term(P.conjugate(t.amp), t.bound, t.kets[k:] + t.kets[:k]) for t in v.terms]
    vec = P.State(v.widths[k:] + v.widths[:k], tuple(terms), False, v.dims[k:] + v.dims[:k])
    return P.Mixed(P.simplify(vec))


# --- inverse -------------------------------------------------------------------------------


def _nonzero(c: Expr) -> bool:
    c = P.tidy(sympy.sympify(c))
    if c.is_zero is False:
        return True
    a2 = zero_form(P.expand(c * P.conjugate(c)))
    return bool(a2.is_zero is False or (a2.is_number and sympy.simplify(a2) != 0))


def _monomial_inverse(g: P.Gate, widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> P.Gate | None:
    """The gate ``|v> -> sum_x [v = g(x)] / c(x) |x>`` for ``g|x> = c(x) |g(x)>``, or None
    when ``g`` is not of that form."""
    xs, ranges = _probe(widths, dims)
    with P.ranged(ranges):
        img = P.apply(g, P.basis_kets(xs, widths, dims))
    if len(img.terms) != 1 or img.terms[0].bound or not _nonzero(img.terms[0].amp):
        return None

    def entry(
        vs: list[sympy.Dummy],
        ys: list[sympy.Dummy],
        im: P.State,
        widths: tuple[Expr, ...],
        dims: tuple[Expr, ...],
    ) -> Expr:
        t = im.terms[0]
        deltas = sympy.Mul(*(sympy.KroneckerDelta(v, k) for v, k in zip(vs, t.kets, strict=True)))
        return deltas / t.amp

    return _kernel_gate(g, f"{g.name}⁻¹", entry)


def _matrix_inverse(g: P.Gate) -> P.Gate | None:
    """The exact inverse of a gate given by a matrix of concrete size, by adjugate and
    determinant."""
    if g.matrix is None:
        return None
    rows = g.matrix()
    m = sympy.Matrix(rows)
    det = P.tidy(sympy.simplify(m.det()))
    if not _nonzero(det):
        raise OperatorError(f"cannot invert {g.name}: determinant {det} not known to be nonzero")
    inv = (m.adjugate() / det).applyfunc(lambda e: P.tidy(sympy.simplify(e)))
    entries = [[inv[r, c] for c in range(inv.cols)] for r in range(inv.rows)]
    return _matrix_from(g, entries, f"{g.name}⁻¹")


def _inverse_at(
    op: P.Operator, widths: tuple[Expr, ...], dims: tuple[Expr, ...], name: str
) -> P.Operator:
    if is_unitary(op, widths, dims):
        return adjoint(op)
    if isinstance(op, P.Gate):
        cand = _monomial_inverse(op, widths, dims)
        if cand is not None and equal_on(P.Compose((cand, op)), P.Identity(), widths, dims):
            return cand
        exact = _matrix_inverse(op)
        if exact is not None:
            return exact
    raise OperatorError(f"cannot invert {name}: no closed-form inverse")


def inverse(op: P.Operator, name: str = "") -> P.Operator:
    """``op^-1``; resolved on the registers it is applied to where it depends on them."""
    label = name or _name(op)
    if isinstance(op, P.Identity):
        return op
    if isinstance(op, P.Scaled):
        if not _nonzero(op.factor):
            raise OperatorError(f"cannot invert {label}: the factor {op.factor} may be 0")
        return P.Scaled(1 / sympy.sympify(op.factor), inverse(op.op))
    if isinstance(op, P.Compose):
        return P.Compose(tuple(inverse(o) for o in reversed(op.ops)))
    if isinstance(op, P.Tensor):
        return P.Tensor(tuple(inverse(f) for f in op.factors))
    if isinstance(op, P.Power):
        return P.Power(inverse(op.op), op.count)
    return P.Derived(f"{label}⁻¹", op, lambda w, d: _inverse_at(op, w, d, label))


def _name(op: P.Operator) -> str:
    if isinstance(op, (P.Gate, P.Derived)):
        return op.name
    return "the operator"


# --- powers --------------------------------------------------------------------------------

MAX_ORDER = 8
"""The largest concrete m tried for ``U^m == I``."""


def _lower(e: Expr) -> Expr:
    """``e`` with each symbol of the running :func:`~diracula.pathsum.ranged` scope written as
    its lower bound plus a new non-negative symbol."""
    reps = {}
    for x in sympy.sympify(e).free_symbols:
        span = _span_of(x)
        if span is not None and span[0].is_finite:
            reps[x] = span[0] + sympy.Dummy(x.name, integer=True, nonnegative=True)
    return sympy.sympify(e).xreplace(reps)


_JUMPS = (sympy.floor, sympy.ceiling, sympy.Mod, sympy.KroneckerDelta, sympy.Piecewise)


def nonnegative(e: Expr) -> bool:
    """Whether ``e`` is known to be at least 0: by sympy, or for a continuous expression of one
    real symbol by its value at the lower end of the symbol's range and the absence of real
    roots inside it."""
    e = sympy.sympify(e)
    if e.is_nonnegative or _lower(e).is_nonnegative:
        return True
    lb = lower_bound(e)
    if lb is not None and lb >= 0:
        return True
    free = list(e.free_symbols)
    if len(free) != 1 or not free[0].is_real or e.has(*_JUMPS) or e.has(sympy.I):
        return False
    x = free[0]
    lo = (_span_of(x) or (None, None))[0]
    if lo is None:
        lo = sympy.S.Zero if x.is_nonnegative else None
    if lo is None or not lo.is_finite:
        return False
    at = sympy.simplify(e.subs(x, lo))
    if not (at.is_number and at.is_positive):
        return False
    return _roots_outside(e)


def real_parts(e: Expr) -> Expr:
    """``e`` with ``conjugate(b^p)`` read as ``b^p`` for a real ``p`` and a base ``b`` known to be
    at least 0."""

    def plain(c: sympy.Basic) -> bool:
        a = c.args[0]
        if a.is_Pow:
            return bool(a.exp.is_real) and nonnegative(a.base)
        return bool(a.is_real) or (a.is_Add and nonnegative(a) and not a.has(sympy.I))

    return sympy.sympify(e).replace(
        lambda c: isinstance(c, sympy.conjugate) and plain(c), lambda c: c.args[0]
    )


def lower_bound(e: Expr) -> Expr | None:
    """A number at most ``e`` over the running ranges, by monotonicity of sums, products of
    non-negative factors and powers of bases at least 1; None when unknown."""
    e = sympy.sympify(e)
    if e.is_number:
        return e if e.is_real else None
    if e.is_Symbol:
        span = _span_of(e)
        lo = span[0] if span is not None else (sympy.S.Zero if e.is_nonnegative else None)
        return lo if lo is not None and lo.is_finite else None
    if e.is_Add:
        total = sympy.S.Zero
        for a in e.args:
            lb = lower_bound(a)
            if lb is None:
                return None
            total += lb
        return total
    if e.is_Mul and e.args[0].is_number and e.args[0] < 0:
        ub = upper_bound(sympy.Mul(*e.args[1:]))
        return None if ub is None else e.args[0] * ub
    if e.is_Mul:
        lows = [lower_bound(a) for a in e.args]
        if any(lb is None or lb < 0 for lb in lows):
            return None
        return sympy.Mul(*lows)
    if e.is_Pow:
        lb, le = lower_bound(e.base), lower_bound(e.exp)
        if lb is not None and le is not None and lb >= 1 and le >= 0:
            return lb**le
        if positive(e.base) and e.exp.is_real:
            return sympy.S.Zero
    return None


def upper_bound(e: Expr) -> Expr | None:
    """A number at least ``e`` over the running ranges, for sums, constant multiples and
    symbols; None when unknown."""
    e = sympy.sympify(e)
    if e.is_number:
        return e if e.is_real else None
    if e.is_Symbol:
        span = _span_of(e)
        return span[1] if span is not None and span[1].is_finite else None
    if e.is_Add:
        total = sympy.S.Zero
        for a in e.args:
            ub = upper_bound(a)
            if ub is None:
                return None
            total += ub
        return total
    if e.is_Mul and e.args[0].is_number:
        rest = sympy.Mul(*e.args[1:])
        b = upper_bound(rest) if e.args[0] > 0 else lower_bound(rest)
        return None if b is None else e.args[0] * b
    return None


def positive(e: Expr) -> bool:
    """Whether ``e`` is known to be greater than 0, under the running ranges."""
    e = sympy.sympify(e)
    if e.is_positive:
        return True
    if e.is_Mul:
        return all(positive(a) for a in e.args)
    if e.is_Pow and e.exp.is_real and positive(e.base):
        return True
    lb = lower_bound(e)
    return lb is not None and bool(lb > 0)


def known_nonzero(e: Expr) -> bool:
    """Whether ``e`` is known not to be 0, under the running ranges."""
    e = P.tidy(sympy.sympify(e))
    if _nonzero(e):
        return True
    if positive(e) or positive(-e) or positive(sympy.factor(e)) or positive(-sympy.factor(e)):
        return True
    low = sympy.simplify(_lower(e))
    if low.is_zero is False or low.is_positive or low.is_negative:
        return True
    return _roots_outside(e)


def _roots_outside(e: Expr) -> bool:
    """Whether ``e``, of one real symbol, has finitely many real roots, none in that symbol's
    range."""
    free = [x for x in e.free_symbols if x.is_real]
    if len(free) != 1 or len(e.free_symbols) != 1:
        return False
    x = free[0]
    try:
        roots = sympy.solveset(e, x, domain=sympy.S.Reals)
    except (NotImplementedError, ValueError, TypeError):
        return False
    if not isinstance(roots, sympy.FiniteSet):
        return roots is sympy.S.EmptySet
    lo, hi = _span_of(x) or (sympy.S.Zero if x.is_nonnegative else -sympy.oo, sympy.oo)
    for r in roots:
        if x.is_integer and r.is_integer is False:
            continue
        if bool(sympy.simplify(r - lo).is_negative) or bool(sympy.simplify(r - hi).is_positive):
            continue
        return False
    return True


def _gate(name: str, arity: int, image: object, base: P.Operator) -> P.Gate:
    root = base if isinstance(base, P.Gate) else None
    return P.Gate(name, arity, image, base=root, source=name)  # type: ignore[arg-type]


def _monomial(
    op: P.Operator, widths: tuple[Expr, ...], dims: tuple[Expr, ...]
) -> tuple[list[sympy.Dummy], Expr, tuple[Expr, ...]] | None:
    """``(xs, c, g)`` with ``op |xs> = c |g>``, or None."""
    xs, ranges = _probe(widths, dims)
    with P.ranged(ranges):
        try:
            img = P.apply(op, P.basis_kets(xs, widths, dims))
        except P.PathSumError:
            return None
    if len(img.terms) != 1 or img.terms[0].bound or len(img.widths) != len(widths):
        return None
    if not (all(map(P.same, img.widths, widths)) and all(map(P.same, img.dims, dims))):
        return None
    t = img.terms[0]
    return xs, t.amp, t.kets


def _permutation(
    xs: Sequence[sympy.Dummy], g: Sequence[Expr], widths: Sequence[Expr], dims: Sequence[Expr]
) -> list[int] | None:
    """``pi`` with ``g[i] = xs[pi[i]]``, a permutation of registers of equal layout, or None."""
    pi = []
    for i, v in enumerate(g):
        if v not in xs:
            return None
        j = list(xs).index(v)
        if not (P.same(widths[i], widths[j]) and P.same(dims[i], dims[j])):
            return None
        pi.append(j)
    return pi if sorted(pi) == list(range(len(xs))) else None


def _affine(x: sympy.Dummy, v: Expr, levels: Expr) -> tuple[Expr, Expr] | None:
    """``(a, b)`` with ``v = (a x + b) mod levels``, or None."""
    if not (isinstance(v, sympy.Mod) and P.same(v.args[1], levels)):
        return None
    top = P.expand(v.args[0])
    a = top.coeff(x)
    b = P.expand(top - a * x)
    if x in a.free_symbols or x in b.free_symbols or a == 0:
        return None
    return a, b


def _xor_constant(x: sympy.Dummy, v: Expr) -> Expr | None:
    if isinstance(v, P.xor):
        a, b = v.args
        if a == x and x not in b.free_symbols:
            return b
        if b == x and x not in a.free_symbols:
            return a
    return None


def _indicator_sum(k: Expr, m: int, parts: Sequence[P.Operator]) -> P.Operator:
    """``sum_r [k mod m = r] parts[r]``."""
    return P.OpSum(
        tuple(P.Scaled(sympy.KroneckerDelta(sympy.Mod(k, m), r), parts[r]) for r in range(m))
    )


def _power_monomial(
    op: P.Operator,
    k: Expr,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    name: str,
    signed: bool,
) -> P.Operator | None:
    mono = _monomial(op, widths, dims)
    if mono is None:
        return None
    xs, c, g = mono
    arity = len(widths)
    label = f"{name}^{k}"
    if tuple(g) == tuple(xs):
        if signed and not _nonzero(c):
            return None
        cf = sympy.Lambda(tuple(xs), c)

        def diag(vals: tuple[Expr, ...], ws: tuple[Expr, ...], ds: tuple[Expr, ...]) -> P.State:
            return P.State(
                tuple(ws), (P.Term(P.tidy(cf(*vals) ** k), (), tuple(vals)),), False, tuple(ds)
            )

        return _gate(label, arity, diag, op)
    if any(x in c.free_symbols for x in xs) or not _nonzero(c):
        return None
    phase = c**k
    pi = _permutation(xs, g, widths, dims)
    if pi is not None and arity > 1:
        order, cur = 1, list(pi)
        while cur != list(range(arity)):
            cur = [pi[j] for j in cur]
            order += 1
        powers = [list(range(arity))]
        for _ in range(order - 1):
            powers.append([pi[j] for j in powers[-1]])

        def perm(vals: tuple[Expr, ...], ws: tuple[Expr, ...], ds: tuple[Expr, ...]) -> P.State:
            terms = tuple(
                P.Term(
                    phase * sympy.KroneckerDelta(sympy.Mod(k, order), r),
                    (),
                    tuple(vals[j] for j in p),
                )
                for r, p in enumerate(powers)
            )
            return P.State(tuple(ws), terms, False, tuple(ds))

        return _gate(label, arity, perm, op)
    if arity != 1:
        return None
    x, v = xs[0], g[0]
    levels = sympy.sympify(dims[0]) ** widths[0]
    image: Callable[[Expr], Expr]
    aff = _affine(x, v, levels)
    if aff is not None:
        a, b = aff
        if a == 1:
            image = lambda y: sympy.Mod(y + k * b, levels)
        elif signed:
            return None
        else:
            ak = a**k
            image = lambda y: sympy.Mod(ak * y + b * sympy.cancel((ak - 1) / (a - 1)), levels)
    elif (cst := _xor_constant(x, v)) is not None:
        image = lambda y: P.xor(y, cst * sympy.Mod(k, 2))
    else:
        return None

    def mapped(vals: tuple[Expr, ...], ws: tuple[Expr, ...], ds: tuple[Expr, ...]) -> P.State:
        return P.State(tuple(ws), (P.Term(phase, (), (image(vals[0]),)),), False, tuple(ds))

    return _gate(label, 1, mapped, op)


def _low_rank(op: P.Operator) -> tuple[Expr, list[tuple[Expr, P.State, P.State]]] | None:
    """``(alpha, [(c, ket, bra), ...])`` with ``op = alpha I + sum c |ket><bra|``, or None."""
    if isinstance(op, P.Identity):
        return sympy.S.One, []
    if isinstance(op, P.Outer):
        return sympy.S.Zero, [(sympy.S.One, op.ket, op.bra)]
    if isinstance(op, P.Scaled):
        inner = _low_rank(op.op)
        if inner is None:
            return None
        f = sympy.sympify(op.factor)
        return f * inner[0], [(f * c, a, b) for c, a, b in inner[1]]
    if isinstance(op, P.OpSum):
        alpha, terms = sympy.S.Zero, []
        for o in op.ops:
            part = _low_rank(o)
            if part is None:
                return None
            alpha += part[0]
            terms += part[1]
        return alpha, terms
    if isinstance(op, P.Compose):
        parts = [_low_rank(o) for o in op.ops]
        if any(p is None for p in parts):
            return None
        alpha, terms = parts[0]  # type: ignore[misc]
        for beta, rest in parts[1:]:  # type: ignore[misc]
            new = [(beta * c, a, b) for c, a, b in terms] + [(alpha * c, a, b) for c, a, b in rest]
            new += [
                (c1 * c2 * P.inner(b1, a2), a1, b2) for c1, a1, b1 in terms for c2, a2, b2 in rest
            ]
            alpha, terms = alpha * beta, new
        return alpha, terms
    return None


def _distinct(items: Sequence[P.State]) -> list[P.State]:
    out: list[P.State] = []
    for s in items:
        if not any(s == o for o in out):
            out.append(s)
    return out


def _spectral(t: sympy.Matrix, what: str) -> list[tuple[Expr, sympy.Matrix]]:
    """``[(lambda_i, E_i)]`` with ``t = sum lambda_i E_i`` (Sylvester), for distinct eigenvalues
    in radicals; raises otherwise."""
    lam = sympy.Dummy("lambda")
    poly = sympy.Poly(t.charpoly(lam).as_expr(lam), lam)
    if poly.degree() != t.rows:
        raise OperatorError(f"cannot compute {what}: no characteristic polynomial")
    if poly.degree() > 4:
        raise OperatorError(
            f"cannot compute {what}: characteristic polynomial of degree {poly.degree()} "
            "not solvable in radicals"
        )
    roots = sympy.roots(poly, multiple=False)
    if sum(roots.values()) != poly.degree() or any(r.has(sympy.CRootOf) for r in roots):
        raise OperatorError(
            f"cannot compute {what}: characteristic polynomial of degree {poly.degree()} "
            "not solvable in radicals"
        )
    eig = list(roots)
    if any(m > 1 for m in roots.values()):
        raise OperatorError(f"cannot compute {what}: repeated eigenvalues")
    for a in range(len(eig)):
        for b in range(a + 1, len(eig)):
            if not known_nonzero(eig[a] - eig[b]):
                raise OperatorError(f"cannot compute {what}: eigenvalues not known to be distinct")
    one = sympy.eye(t.rows)
    out = []
    for a, la in enumerate(eig):
        e = one
        for b, lb in enumerate(eig):
            if a != b:
                e = e * (t - lb * one) / (la - lb)
        out.append((la, e))
    return out


def _orthonormal(states: Sequence[P.State], what: str) -> list[P.State]:
    """An orthonormal basis of the span of ``states`` (Gram-Schmidt); raises when a residual
    norm is neither known to be 0 nor known not to be."""
    basis: list[P.State] = []
    for s in states:
        r = s
        for q in basis:
            r = P.simplify(P.add(r, P.scale(-P.inner(P.dagger(q), s), q)))
        nn = P.tidy(sympy.simplify(P.norm2(r)))
        if zero_form(nn) == 0:
            continue
        if not known_nonzero(nn):
            raise OperatorError(f"{what}: the norm {nn} is not known to be nonzero")
        basis.append(P.simplify(P.scale(1 / sympy.sqrt(nn), r)))
    return basis


def _rotation_power(m: sympy.Matrix, k: Expr) -> sympy.Matrix | None:
    """``m^k`` for ``m = [[a, -b], [b, a]]``, ``a^2 + b^2 = 1``, ``b`` of known sign, as the
    rotation by ``k acos(a)``."""
    if m.shape != (2, 2):
        return None
    a, b = m[0, 0], m[1, 0]
    if zero_form(m[1, 1] - a) != 0 or zero_form(m[0, 1] + b) != 0:
        return None
    if zero_form(P.expand(a * P.conjugate(a) - 1 + b * P.conjugate(b))) != 0:
        return None
    if zero_form(a - P.conjugate(a)) != 0 or zero_form(b - P.conjugate(b)) != 0:
        return None
    if nonnegative(b):
        phi = sympy.acos(a)
    elif nonnegative(-b):
        phi = -sympy.acos(a)
    else:
        return None
    c, s = sympy.cos(k * phi), sympy.sin(k * phi)
    return sympy.Matrix([[c, -s], [s, c]])


def _matrix_power(m: sympy.Matrix, k: Expr, what: str, signed: bool) -> sympy.Matrix:
    rot = _rotation_power(m, k)
    if rot is not None:
        return rot
    if m.shape == (1, 1):
        if signed and not known_nonzero(m[0, 0]):
            raise OperatorError(f"{what}: the eigenvalue {m[0, 0]} may be 0; assume {k} >= 0")
        return sympy.Matrix([[P.tidy(m[0, 0] ** k)]])
    spec = _spectral(m, what)
    if signed and not all(known_nonzero(la) for la, _ in spec):
        raise OperatorError(f"{what}: an eigenvalue may be 0; assume {k} >= 0")
    out = sympy.zeros(m.rows, m.cols)
    for la, e in spec:
        out += la**k * e
    return out


def _power_low_rank(op: P.Operator, k: Expr, name: str, signed: bool) -> P.Operator | None:
    """``op^k`` for ``op = alpha I + sum c |K><B|``: with every B in the span of the K,
    ``alpha^k (I - Q Q^dagger) + Q M^k Q^dagger`` for an orthonormal basis Q of that span and
    ``M = Q^dagger op Q``; otherwise ``alpha^k I + K h_k(T) C B^dagger`` with ``T = alpha + C G``,
    ``G = B^dagger K`` and ``h_k(l) = (l^k - alpha^k)/(l - alpha)``."""
    lr = _low_rank(op)
    if lr is None or not lr[1]:
        return None
    alpha, terms = lr
    alpha = P.tidy(sympy.sympify(alpha))
    what = f"cannot raise {name} to the symbolic power {k}"
    if signed and not known_nonzero(alpha):
        return None
    kets = _distinct([a for _, a, _ in terms])
    bras = _distinct([b for _, _, b in terms])
    q = _orthonormal(kets, what)

    def residual(b: P.State) -> Expr:
        ket = P.dagger(b)
        r = ket
        for v in q:
            r = P.add(r, P.scale(-P.inner(P.dagger(v), ket), v))
        return zero_form(P.norm2(P.simplify(r)))

    ak = P.tidy(alpha**k)
    parts: list[P.Operator]
    if all(residual(b) == 0 for b in bras):
        m = sympy.Matrix(
            len(q),
            len(q),
            lambda i, j: P.tidy(
                sympy.simplify(real_parts(P.inner(P.dagger(q[i]), P.apply(op, q[j]))))
            ),
        )
        mk = _matrix_power(m, k, what, signed)
        parts = [P.Scaled(ak, P.Identity())]
        for i, a in enumerate(q):
            for j, b in enumerate(q):
                f = P.tidy(sympy.simplify(mk[i, j] - (ak if i == j else 0)))
                if f != 0:
                    parts.append(P.Scaled(f, P.Outer(a, P.dagger(b))))
        return P.OpSum(tuple(parts))
    c = sympy.zeros(len(kets), len(bras))
    for f, a, b in terms:
        i = next(n for n, s in enumerate(kets) if s == a)
        j = next(n for n, s in enumerate(bras) if s == b)
        c[i, j] += f
    g = sympy.Matrix(len(bras), len(kets), lambda j, i: P.inner(bras[j], kets[i]))
    t = (alpha * sympy.eye(len(kets)) + c * g).applyfunc(lambda e: P.tidy(sympy.simplify(e)))
    spec = _spectral(t, what)
    if signed and not all(known_nonzero(la) for la, _ in spec):
        return None
    h = sympy.zeros(len(kets), len(kets))
    for la, e in spec:
        gap = sympy.simplify(la - alpha)
        if gap == 0:
            hk = k * alpha ** (k - 1)
        elif known_nonzero(gap):
            hk = (la**k - alpha**k) / gap
        else:
            raise OperatorError(f"{what}: eigenvalue {la} not known to differ from {alpha}")
        h += hk * e
    x = (h * c).applyfunc(lambda e: P.tidy(sympy.simplify(e)))
    parts = [P.Scaled(ak, P.Identity())]
    for i, a in enumerate(kets):
        for j, b in enumerate(bras):
            if x[i, j] != 0:
                parts.append(P.Scaled(x[i, j], P.Outer(a, b)))
    return P.OpSum(tuple(parts))


def _power_at(
    op: P.Operator,
    k: Expr,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    name: str,
    natural: bool = False,
) -> P.Operator:
    signed = not natural and not nonnegative(k)
    if signed:
        try:
            return _power_signed(op, k, widths, dims, name)
        except OperatorError:
            pass
        try:
            inv = _inverse_at(op, widths, dims, name)
        except OperatorError:
            raise OperatorError(
                f"cannot raise {name} to the symbolic power {k}: "
                f"{name} has no closed-form inverse; assume {k} >= 0"
            ) from None
        up = _power_at(op, k, widths, dims, name, natural=True)
        down = _power_at(inv, -k, widths, dims, f"{name}⁻¹", natural=True)
        ge = sympy.Piecewise((1, k >= 0), (0, True))
        return P.OpSum((P.Scaled(ge, up), P.Scaled(1 - ge, down)))
    return _power_signed(op, k, widths, dims, name, signed)


def _power_signed(
    op: P.Operator,
    k: Expr,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    name: str,
    signed: bool = True,
) -> P.Operator:
    """``op^k`` by the classes whose closed form holds for every integer ``k`` when ``signed``,
    for ``k >= 0`` otherwise; raises when none applies."""
    what = f"cannot raise {name} to the symbolic power {k}"
    out = _power_monomial(op, k, widths, dims, name, signed)
    if out is not None:
        return out
    square = P.Compose((op, op))
    involution = equal_on(square, P.Identity(), widths, dims)
    if involution:
        return P.OpSum(
            (
                P.Scaled((1 + (-1) ** k) / 2, P.Identity()),
                P.Scaled((1 - (-1) ** k) / 2, op),
            )
        )
    if equal_on(square, op, widths, dims):
        if signed:
            raise OperatorError(f"{what}: {name} is a projector; assume {k} >= 0")
        z = sympy.KroneckerDelta(k, 0)
        return P.OpSum((P.Scaled(z, P.Identity()), P.Scaled(1 - z, op)))
    if isinstance(op, P.Compose) and len(op.ops) > 1:
        fs = op.ops
        if all(
            equal_on(P.Compose((fs[a], fs[b])), P.Compose((fs[b], fs[a])), widths, dims)
            for a in range(len(fs))
            for b in range(a + 1, len(fs))
        ):
            return P.Compose(tuple(_power_signed(f, k, widths, dims, _name(f), signed) for f in fs))
    low = _power_low_rank(op, k, name, signed)
    if low is not None:
        return low
    cur: P.Operator = square
    for m in range(3, MAX_ORDER + 1 if involution is not None else 3):
        cur = P.Compose((op, cur))
        if equal_on(cur, P.Identity(), widths, dims):
            parts = [P.Identity(), op] + [P.Compose((op,) * r) for r in range(2, m)]
            return _indicator_sum(k, m, parts)
    raise OperatorError(f"{what}: no closed-form iterate")


def power(op: P.Operator, k: Expr, name: str = "") -> P.Operator:
    """``op^k`` for an integer expression ``k``."""
    k = sympy.sympify(k)
    label = name or _name(op)
    if k.is_Integer:
        if k < 0:
            return power(inverse(op, label), -k, f"{label}⁻¹")
        return P.Compose((op,) * int(k)) if k else P.Identity()
    if not k.is_integer:
        return op_function("pow", op, label, k)
    if isinstance(op, P.Identity):
        return op
    if not nonnegative(k) and nonnegative(-k):
        return power(inverse(op, label), -k, f"{label}⁻¹")
    if isinstance(op, P.Scaled):
        if not nonnegative(k) and not _nonzero(op.factor):
            raise OperatorError(f"cannot raise {label} to the power {k}: the factor may be 0")
        return P.Scaled(sympy.sympify(op.factor) ** k, power(op.op, k))
    if isinstance(op, P.Tensor):
        return P.Tensor(tuple(power(f, k) for f in op.factors))
    if isinstance(op, P.Power):
        return P.Power(power(op.op, k), op.count)
    return P.Derived(f"{label}^{k}", op, lambda w, d: _power_at(op, k, w, d, label), collect=True)


# --- traces --------------------------------------------------------------------------------


def _inside(v: Expr, b: P.Bound) -> bool:
    lo, hi = lower_bound(v - b.lo), lower_bound(b.hi - v)
    return lo is not None and hi is not None and lo >= 0 and hi >= 0


def pin_deltas(s: P.State) -> P.State:
    """``s`` with each ``[j = c]`` on a bound index ``j`` and a value ``c`` free of bound indices
    and known to lie in ``j``'s range substituted, over the running ranges."""
    terms = []
    for t in s.terms:
        changed = True
        while changed:
            changed = False
            for f in sympy.Mul.make_args(t.amp):
                if not isinstance(f, sympy.KroneckerDelta):
                    continue
                for sym, val in (f.args, f.args[::-1]):
                    b = next((x for x in t.bound if x.symbol == sym), None)
                    if b is None or any(x.symbol in val.free_symbols for x in t.bound):
                        continue
                    if _inside(val, b):
                        t = P._subs_term(t, {sym: val})
                        changed = True
                        break
                if changed:
                    break
        terms.append(t)
    return P.simplify(P.State(s.widths, tuple(terms), s.bra, s.dims))


def dimension_ranges(dims: Sequence[Expr | None]) -> dict[sympy.Symbol, tuple[Expr, Expr]]:
    """Each plain-symbol dimension of ``dims`` at least 2, unless its range is already known."""
    known = P._RANGES.get() or {}
    return {
        d: (sympy.Integer(2), sympy.oo)
        for d in dims
        if isinstance(d, sympy.Symbol) and d not in known
    }


def equal_delta(u: Expr, v: Expr) -> Expr:
    """``[u = v]``, with the factors of ``u - v`` known not to be 0 dropped."""
    diff = sympy.factor(P.expand(u - v))
    if diff == 0:
        return sympy.S.One
    if diff.is_Mul:
        rest = [f for f in diff.args if not (f.is_number or known_nonzero(f))]
        if len(rest) < len(diff.args):
            core = sympy.Mul(*rest)
            if core.is_number:
                return sympy.S.Zero
            lhs, rhs = _split_sides(P.expand(core))
            return sympy.KroneckerDelta(lhs, rhs)
    return sympy.KroneckerDelta(u, v)


def _split_sides(e: Expr) -> tuple[Expr, Expr]:
    pos = [a for a in sympy.Add.make_args(e) if not a.could_extract_minus_sign()]
    neg = [-a for a in sympy.Add.make_args(e) if a.could_extract_minus_sign()]
    return sympy.Add(*pos), sympy.Add(*neg)


def as_mixed(x: P.State | P.Mixed) -> P.Mixed:
    """The density matrix of a ket, or ``x`` itself."""
    if isinstance(x, P.Mixed):
        return x
    ket = P.dagger(x) if x.bra else x
    return P.density(ket)


def partial_trace(m: P.Mixed, traced: Sequence[int]) -> P.Mixed:
    """``tr_R rho`` for the registers ``traced``, by closing ``[b = b']`` on their values."""
    k = m.count
    bad = [r for r in traced if not 0 <= r < k]
    if bad:
        raise OperatorError(
            f"register {bad[0]} is out of range; the state has {k} register(s), counted from 0"
        )
    kept = [r for r in range(k) if r not in set(traced)]
    if not kept:
        raise OperatorError("tracing out every register leaves a scalar; write tr(X)")
    v = m.vec
    with P.ranged(dimension_ranges(v.dims)):
        terms = []
        for t in v.terms:
            amp = t.amp
            for r in set(traced):
                amp = amp * equal_delta(t.kets[r], t.kets[k + r])
            kets = tuple(t.kets[r] for r in kept) + tuple(t.kets[k + r] for r in kept)
            terms.append(P.Term(amp, t.bound, kets))
        widths = tuple(v.widths[r] for r in kept)
        dims = tuple(v.dims[r] for r in kept)
        vec = P.State(widths * 2, tuple(terms), False, dims * 2)
        return P.Mixed(P.collect(pin_deltas(P.simplify(vec))))


def trace_of(x: P.State | P.Mixed) -> Expr:
    """``tr rho``; ``<a|a>`` for a ket or bra ``a``."""
    if isinstance(x, P.Mixed):
        with P.ranged(dimension_ranges(x.vec.dims)):
            return P.trace(x)
    ket = P.dagger(x) if x.bra else x
    with P.ranged(dimension_ranges(ket.dims)):
        return P.norm2(ket)


def operator_trace(op: P.Operator, widths: Sequence[Expr], dims: Sequence[Expr]) -> Expr:
    """``sum_x <x|op|x>`` over registers of ``widths`` and ``dims``, as ``<Phi|(op (x) I)|Phi>``
    with ``|Phi> = sum_x |x>|x>``."""
    bounds = [
        P.new_bound("x", 0, sympy.sympify(d) ** w - 1) for w, d in zip(widths, dims, strict=True)
    ]
    xs = tuple(b.symbol for b in bounds)
    phi = P.State(
        tuple(widths) * 2, (P.Term(sympy.S.One, tuple(bounds), xs + xs),), False, tuple(dims) * 2
    )
    with P.ranged(dimension_ranges(dims)):
        image = P.apply_on(op, phi, 0, len(widths))
        return close_sums(P.tidy(P.inner(P.dagger(phi), image)))


def _reduce_mod(e: sympy.Mod) -> Expr:
    a, m = e.args
    if nonnegative(a) and positive(m - a):
        return a
    return e


def _fixed_shift(f: sympy.KroneckerDelta) -> Expr:
    """``[x = (x + c) mod N]`` as ``[c mod N = 0]`` for ``x`` ranged in ``0..N-1``."""
    ranges = P._RANGES.get() or {}
    for x, m in (f.args, f.args[::-1]):
        if isinstance(m, sympy.Mod) and x.is_Symbol:
            top, mod = m.args
            c = P.expand(top - x)
            span = ranges.get(x)
            if (
                x not in c.free_symbols
                and span is not None
                and span[0] == 0
                and P.same(span[1], mod - 1)
            ):
                return sympy.KroneckerDelta(_reduce_mod(sympy.Mod(c, mod)), 0)
    return f


def _sign_power(p: sympy.Pow) -> Expr:
    """``(-1)^(y^k)`` as ``(-1)^y`` for an integer y and k >= 1."""
    ex = p.exp
    if ex.is_Pow and ex.base.is_integer and ex.exp.is_Integer and ex.exp >= 1:
        return sympy.Integer(-1) ** ex.base
    return p


def _gauss(body: Expr, y: sympy.Symbol, lo: Expr, hi: Expr) -> Expr | None:
    """``sum_{y<c} c^(-1/2) e^(2 pi i s y^2/c) = (1 + i^s)(1 + i^(-s c))/2`` for s = +-1, as
    ``sqrt(c)`` times that."""
    if lo != 0:
        return None
    c = P.expand(hi + 1)
    for f in sympy.Mul.make_args(body):
        if isinstance(f, sympy.exp):
            arg = P.expand(f.args[0] / (2 * sympy.pi * sympy.I))
            for s in (1, -1):
                if P.expand(arg - s * y**2 / c) == 0:
                    rest = P.expand(body / f)
                    if y in rest.free_symbols:
                        return None
                    i = sympy.I
                    return rest * sympy.sqrt(c) * (1 + i**s) * (1 + i ** (-s * c)) / 2
    return None


def close_sums(e: Expr) -> Expr:
    """``e`` with each unevaluated sum's body rewritten (signs of powers mod 2, fixed points of
    shifts, Piecewise conditions as deltas) and closed again, or by the quadratic Gauss sum."""
    e = sympy.sympify(e)
    e = e.replace(lambda x: isinstance(x, sympy.Piecewise), _piecewise)
    if not e.has(sympy.Sum):
        return P.tidy(_settle(e))

    def close(s: sympy.Sum) -> Expr:
        body = s.function
        y, lo, hi = s.limits[0]
        with P.ranged({y: (lo, hi)}):
            body = _settle(body)
            gauss = _gauss(body, y, lo, hi)
            if gauss is not None:
                return gauss
            out = P._close(body, [P.Bound(y, lo, hi)], {})
        if len(s.limits) > 1:
            return sympy.Sum(out, *s.limits[1:])
        return out

    return P.tidy(_settle(e.replace(lambda x: isinstance(x, sympy.Sum), close)))


def _root_condition(c: sympy.Basic) -> Expr | None:
    """``[b | a]`` for the condition ``e^(2 pi i a/b) = 1``, a and b integers."""
    if not isinstance(c, sympy.Eq):
        return None
    lhs, rhs = c.args
    if rhs != 1:
        lhs, rhs = rhs, lhs
    if rhs != 1 or not isinstance(lhs, sympy.exp):
        return None
    q = P.expand(lhs.args[0] / (2 * sympy.pi * sympy.I))
    a, b = sympy.fraction(sympy.together(q))
    if not (a.is_integer and b.is_integer):
        return None
    return sympy.KroneckerDelta(_reduce_mod(sympy.Mod(a, b)), 0)


def _piecewise(p: sympy.Piecewise) -> Expr:
    out: Expr = sympy.S.Zero
    rest: Expr = sympy.S.One
    for value, cond in p.args:
        if cond is sympy.true:
            return P.expand(out + rest * value)
        ind = _root_condition(cond)
        if ind is None:
            return P.piecewise_delta(p)
        out += rest * ind * value
        rest *= 1 - ind
    return p


def _settle(e: Expr) -> Expr:
    e = e.replace(lambda x: x.is_Pow and x.base == -1, _sign_power)
    e = e.replace(lambda x: isinstance(x, sympy.KroneckerDelta), _fixed_shift)
    e = e.replace(lambda x: isinstance(x, sympy.Mod), _reduce_mod)
    return e


# --- partial measurement -------------------------------------------------------------------


def permute_mixed(m: P.Mixed, order: Sequence[int]) -> P.Mixed:
    """``rho`` with its registers reordered: register ``i`` of the result is ``order[i]``."""
    k = m.count
    v = m.vec
    full = list(order) + [k + o for o in order]
    terms = tuple(P.Term(t.amp, t.bound, tuple(t.kets[o] for o in full)) for t in v.terms)
    return P.Mixed(
        P.State(tuple(v.widths[o] for o in full), terms, False, tuple(v.dims[o] for o in full))
    )


def conjugate_slice(op: P.Operator, m: P.Mixed, i: int, j: int) -> P.Mixed:
    """``op rho op^dagger`` with ``op`` on registers ``i..j-1``."""
    v = m.vec
    k = m.count
    v1 = P.apply_on(op, v, i, j)
    start = k + len(v1.widths) - len(v.widths)
    v2 = P.conj(P.apply_on(op, P.conj(v1), start + i, start + j))
    out = P.Mixed(P.simplify(v2))
    if len(out.vec.widths) % 2 or out.count != len(v2.widths) // 2:
        raise OperatorError("the basis changes the registers it acts on")
    return out


def _dephase(m: P.Mixed, r: int) -> P.Mixed:
    k = m.count
    v = m.vec
    terms = []
    for t in v.terms:
        amp = t.amp
        for a in range(r):
            amp = amp * equal_delta(t.kets[a], t.kets[k + a])
        terms.append(P.Term(amp, t.bound, t.kets))
    return P.Mixed(P.collect(P.simplify(P.State(v.widths, tuple(terms), False, v.dims))))


def measure_registers(
    x: P.State | P.Mixed, regs: Sequence[int], basis: P.Operator | None = None
) -> tuple[P.Distribution, P.Mixed]:
    """The Born distribution of the registers ``regs`` of ``x``, in the basis ``{B|k>}`` of a gate
    ``B`` on them, read as one value in the order of ``regs``; and the state after it,
    ``sum_k P_k rho P_k`` with ``P_k = B|k><k|B^dagger``."""
    m = as_mixed(x)
    k = m.count
    bad = [r for r in regs if not 0 <= r < k]
    if bad:
        raise OperatorError(
            f"register {bad[0]} is out of range; the state has {k} register(s), counted from 0"
        )
    order = list(regs) + [r for r in range(k) if r not in set(regs)]
    back = [order.index(r) for r in range(k)]
    with P.ranged(dimension_ranges(m.vec.dims)):
        rho = permute_mixed(m, order)
        r = len(regs)
        if basis is not None:
            rho = conjugate_slice(adjoint(basis), rho, 0, r)
            r += rho.count - k
        if rho.count != k:
            raise OperatorError("the basis changes the registers it acts on")
        rest = list(range(r, k))
        reduced = partial_trace(rho, rest) if rest else rho
        dist = P.joined(P.distribution(reduced), reduced.layout())
        post = _dephase(rho, r)
        if basis is not None:
            post = conjugate_slice(basis, post, 0, r)
        post = permute_mixed(post, back)
        return dist, P.Mixed(P.collect(P.simplify(post.vec)))


# --- channels ------------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True, eq=False)
class Channel:
    """``rho -> sum_k K_k rho K_k^dagger`` over the Kraus operators ``kraus``, each a pair of an
    operator and the index bounds it is summed over."""

    name: str
    kraus: tuple[tuple[P.Operator, tuple[P.Bound, ...]], ...]
    checked: dict[Layout, bool | None] = dataclasses.field(default_factory=dict)


@dataclasses.dataclass(frozen=True, eq=False)
class ChannelSeq:
    """``E_1 E_2 ...``, applied right to left."""

    name: str
    parts: tuple[AnyChannel, ...]


@dataclasses.dataclass(frozen=True, eq=False)
class ChannelTensor:
    """``E_1 (x) E_2 (x) ...`` on consecutive registers."""

    name: str
    parts: tuple[AnyChannel, ...]


@dataclasses.dataclass(frozen=True, eq=False)
class ChannelAt:
    """The channel ``build(widths, dims)`` on the registers it is applied to."""

    name: str
    build: object
    cache: dict[Layout, Channel] = dataclasses.field(default_factory=dict)

    def at(self, widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> Channel:
        key = (widths, dims)
        if key not in self.cache:
            self.cache[key] = self.build(widths, dims)  # type: ignore[operator]
        return self.cache[key]


AnyChannel = Channel | ChannelSeq | ChannelTensor | ChannelAt


def _family(op: P.Operator, bounds: tuple[P.Bound, ...]) -> P.Operator:
    return P.Family(op, bounds) if bounds else op


def trace_preserving(e: Channel, widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> bool | None:
    """Whether ``sum_k K_k^dagger K_k == I`` on that layout, cached per layout."""
    key = (widths, dims)
    if key not in e.checked:
        total = P.OpSum(tuple(_family(P.Compose((adjoint(k), k)), b) for k, b in e.kraus))
        with P.ranged(dimension_ranges(dims)):
            e.checked[key] = equal_on(total, P.Identity(), widths, dims)
    return e.checked[key]


def _span(e: AnyChannel) -> P.Operator:
    if isinstance(e, Channel):
        return e.kraus[0][0]
    if isinstance(e, ChannelSeq):
        return _span(e.parts[-1])
    if isinstance(e, ChannelTensor):
        return P.Tensor(tuple(_span(p) for p in e.parts))
    return P.Identity()


def apply_channel(
    e: AnyChannel, m: P.Mixed, i: int = 0, j: int | None = None, warn: list[str] | None = None
) -> P.Mixed:
    """``E(rho)`` on registers ``i..j-1`` of ``rho``; an undecided trace preservation is
    appended to ``warn``."""
    k = m.count
    j = k if j is None else j
    v = m.vec
    widths, dims = tuple(v.widths[i:j]), tuple(v.dims[i:j])
    if isinstance(e, ChannelAt):
        return apply_channel(e.at(widths, dims), m, i, j, warn)
    if isinstance(e, ChannelSeq):
        for part in reversed(e.parts):
            before = m.count
            m = apply_channel(part, m, i, j, warn)
            j += m.count - before
        return m
    if isinstance(e, ChannelTensor):
        layout = P.State(
            v.widths[:k], (P.Term(sympy.S.One, (), (sympy.S.Zero,) * k),), False, v.dims[:k]
        )
        _, segments = P._align([_span(p) for p in e.parts], layout, i, j)
        if len(segments) != len(e.parts):
            raise OperatorError(f"{e.name} does not cover the state's registers")
        for part, (_, a, b) in reversed(list(zip(e.parts, segments, strict=True))):
            m = apply_channel(part, m, a, b, warn)
        return m
    ok = trace_preserving(e, widths, dims)
    if ok is False:
        raise OperatorError(f"channel {e.name} is not trace preserving")
    if ok is None and warn is not None:
        warn.append(
            f"warning: channel {e.name} is not known to be trace preserving; applied as written"
        )
    terms: list[P.Term] = []
    out: P.State | None = None
    with P.ranged(dimension_ranges(v.dims)):
        for op, bounds in e.kraus:
            with P.ranged({b.symbol: (b.lo, b.hi) for b in bounds}):
                piece = conjugate_slice(op, m, i, j).vec
            out = piece if out is None else out
            terms += [P.fresh(P.Term(t.amp, bounds + t.bound, t.kets)) for t in piece.terms]
        assert out is not None
        terms = [P.Term(P.tidy(real_parts(t.amp)), t.bound, t.kets) for t in terms]
        vec = P.State(out.widths, tuple(terms), False, out.dims)
        return P.Mixed(P.collect(pin_deltas(P.simplify(vec))))


def _shift_gate() -> P.Gate:
    def fn(vals: tuple[Expr, ...], widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> P.State:
        n = sympy.sympify(dims[0]) ** widths[0]
        return P.State(
            tuple(widths),
            (P.Term(sympy.S.One, (), (sympy.Mod(vals[0] + 1, n),)),),
            False,
            tuple(dims),
        )

    return P.Gate("X_d", 1, fn, source="|x>_d -> |(x + 1) % d>_d")


def _clock_gate() -> P.Gate:
    def fn(vals: tuple[Expr, ...], widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> P.State:
        n = sympy.sympify(dims[0]) ** widths[0]
        amp = sympy.exp(2 * sympy.pi * sympy.I * vals[0] / n)
        return P.State(tuple(widths), (P.Term(amp, (), (vals[0],)),), False, tuple(dims))

    return P.Gate("Z_d", 1, fn, source="|x>_d -> e^(2*pi*i*x/d) |x>_d")


SHIFT = _shift_gate()
"""The generalised Pauli X on one register of d levels."""
CLOCK = _clock_gate()
"""The generalised Pauli Z on one register of d levels."""


def _levels(widths: tuple[Expr, ...], dims: tuple[Expr, ...], name: str) -> Expr:
    if len(widths) != 1:
        raise OperatorError(f"{name} acts on one register")
    return sympy.sympify(dims[0]) ** widths[0]


def depolarize(p: Expr) -> ChannelAt:
    """``rho -> (1 - p) rho + p I/d``: Kraus ``sqrt(1 - p) I`` and ``sqrt(p)/d X^a Z^b``."""

    def build(widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> Channel:
        d = _levels(widths, dims, "depolarize")
        a, b = P.new_bound("a", 0, d - 1), P.new_bound("b", 0, d - 1)
        pauli = P.Compose((power(SHIFT, a.symbol, "X_d"), power(CLOCK, b.symbol, "Z_d")))
        kraus = (
            (P.Scaled(sympy.sqrt(1 - p), P.Identity()), ()),
            (P.Scaled(sympy.sqrt(p) / d, pauli), (a, b)),
        )
        return Channel(f"depolarize({p})", kraus)

    return ChannelAt(f"depolarize({p})", build)


def dephase(p: Expr) -> ChannelAt:
    """``rho -> (1 - p) rho + p sum_k |k><k| rho |k><k|``: Kraus ``sqrt(1 - p) I`` and
    ``sqrt(p) |k><k|``."""

    def build(widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> Channel:
        _levels(widths, dims, "dephase")
        k = P.new_bound("k", 0, sympy.sympify(dims[0]) ** widths[0] - 1)
        ket = P.basis(k.symbol, widths[0], dims[0])
        kraus = (
            (P.Scaled(sympy.sqrt(1 - p), P.Identity()), ()),
            (P.Scaled(sympy.sqrt(p), P.Outer(ket, P.dagger(ket))), (k,)),
        )
        return Channel(f"dephase({p})", kraus)

    return ChannelAt(f"dephase({p})", build)


def amp_damp(g: Expr) -> ChannelAt:
    """Amplitude damping to ``|0>``: Kraus ``sqrt(1 - g) I + (1 - sqrt(1 - g)) |0><0|`` and
    ``sqrt(g) (1 - [j = 0]) |0><j|``."""

    def build(widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> Channel:
        n = _levels(widths, dims, "amp_damp")
        w, d = widths[0], dims[0]
        zero = P.basis(sympy.S.Zero, w, d)
        a = sympy.sqrt(1 - g)
        keep = P.OpSum((P.Scaled(a, P.Identity()), P.Scaled(1 - a, P.Outer(zero, P.dagger(zero)))))
        j = P.new_bound("j", 0, n - 1)
        jet = P.basis(j.symbol, w, d)
        decay = P.Scaled(
            sympy.sqrt(g) * (1 - sympy.KroneckerDelta(j.symbol, 0)), P.Outer(zero, P.dagger(jet))
        )
        return Channel(f"amp_damp({g})", ((keep, ()), (decay, (j,))))

    return ChannelAt(f"amp_damp({g})", build)


# --- functions of operators ----------------------------------------------------------------

NOTES: list[str] = []
"""Notes on branches taken, read and cleared by the interpreter after each statement."""

MULTIVALUED = {"sqrt", "log", "pow"}


def scalar_function(name: str, t: Expr | None = None) -> object:
    """The scalar function ``name``, principal branch; ``pow`` is ``z^t``."""
    table = {
        "exp": sympy.exp,
        "sqrt": sympy.sqrt,
        "cos": sympy.cos,
        "sin": sympy.sin,
        "tan": sympy.tan,
        "log": sympy.log,
    }
    if name == "pow":
        return lambda z: z**t
    return table[name]


def _label(name: str, arg: str, t: Expr | None) -> str:
    return f"{arg}^{t}" if name == "pow" else f"{name}({arg})"


def _on_cut(name: str, z: Expr) -> bool:
    """Whether the eigenvalue ``z`` lies on the branch cut (the negative reals) of ``name``."""
    if name not in MULTIVALUED:
        return False
    z = sympy.nsimplify(sympy.simplify(z))
    return bool(z.is_real and z.is_negative)


def _check_eigen(name: str, z: Expr, what: str, t: Expr | None) -> None:
    z = sympy.simplify(z)
    if name == "log" and z == 0:
        raise OperatorError(f"cannot compute {what}: eigenvalue 0 of log")
    if name == "pow" and z == 0 and not positive(sympy.sympify(t)):
        raise OperatorError(
            f"cannot compute {what}: eigenvalue 0 of a power {t} not known positive"
        )
    if name == "tan" and zero_form(sympy.cos(z)) == 0:
        raise OperatorError(f"cannot compute {what}: eigenvalue {z} at a pole of tan")


def _note_cut(name: str, eigen: Sequence[Expr], what: str, f: object) -> None:
    for z in eigen:
        if _on_cut(name, z):
            value = str(f(z)).replace("I", "i")  # type: ignore[operator]
            NOTES.append(f"note: {what} takes the principal branch at the eigenvalue {z}: {value}")


def _interpolate(f: object, eigen: Sequence[Expr], basis: Sequence[P.Operator]) -> P.Operator:
    """``sum_j f(eigen[j]) basis[j]``."""
    return P.OpSum(
        tuple(P.Scaled(P.tidy(sympy.simplify(f(z))), b) for z, b in zip(eigen, basis, strict=True))  # type: ignore[operator]
    )


def _commutes(
    a: P.Operator, b: P.Operator, widths: tuple[Expr, ...], dims: tuple[Expr, ...]
) -> bool:
    return bool(equal_on(P.Compose((a, b)), P.Compose((b, a)), widths, dims))


def _identity_like(op: P.Operator) -> bool:
    return isinstance(op, P.Identity) or (isinstance(op, P.Power) and isinstance(op.op, P.Identity))


def _flatten(op: P.Tensor) -> list[P.Operator]:
    out: list[P.Operator] = []
    for f in op.factors:
        out += _flatten(f) if isinstance(f, P.Tensor) else [f]
    return out


def _local_sum(op: P.Operator) -> tuple[Expr, P.Operator, Expr] | None:
    """``(c, A, n)`` for ``c sum_{j<n} I^@j @ A @ I^@(n-1-j)``, or None."""
    c = sympy.S.One
    while isinstance(op, P.Scaled):
        c, op = c * op.factor, op.op
    if not (isinstance(op, P.Family) and len(op.bounds) == 1):
        return None
    b = op.bounds[0]
    inner = op.op
    while isinstance(inner, P.Scaled):
        c, inner = c * inner.factor, inner.op
    flat = _flatten(inner) if isinstance(inner, P.Tensor) else []
    if len(flat) != 3 or b.lo != 0:
        return None
    left, a, right = flat
    n = P.expand(b.hi + 1)
    j = b.symbol
    if not (isinstance(left, P.Power) and _identity_like(left) and P.same(left.count, j)):
        return None
    if not (
        isinstance(right, P.Power) and _identity_like(right) and P.same(right.count, n - 1 - j)
    ):
        return None
    if j in c.free_symbols:
        return None
    return c, a, n


def op_function(name: str, op: P.Operator, label: str = "", t: Expr | None = None) -> P.Operator:
    """``f(op)`` for the scalar function ``name`` (``pow`` with exponent ``t``), by the spectral
    form of ``op`` where the engine can derive it."""
    arg = label or _name(op)
    what = _label(name, arg, t)
    f = scalar_function(name, t)
    if isinstance(op, P.Identity):
        _check_eigen(name, sympy.S.One, what, t)
        return P.Scaled(f(sympy.S.One), op)  # type: ignore[operator]
    if isinstance(op, P.Tensor):
        rest = [k for k, g in enumerate(op.factors) if not _identity_like(g)]
        if len(rest) == 1:
            k = rest[0]
            factors = list(op.factors)
            factors[k] = op_function(name, op.factors[k], "", t)
            return P.Tensor(tuple(factors))
    if name == "exp":
        local = _local_sum(op)
        if local is not None:
            c, a, n = local
            return P.Power(op_function("exp", P.Scaled(c, a)), n)
        c, core = sympy.S.One, op
        while isinstance(core, P.Scaled):
            c, core = c * sympy.sympify(core.factor), core.op
        if isinstance(core, P.OpSum):
            spread = _disjoint_tensors(core.ops)
            if spread is not None:
                return P.Tensor(
                    tuple(
                        op_function("exp", P.Scaled(c, g)) if not _identity_like(g) else g
                        for g in spread
                    )
                )
    if isinstance(op, P.Compose) and len(op.ops) == 3 and op.ops[2] is adjoint(op.ops[0]):
        v, dg = op.ops[0], op.ops[1]
        return P.Derived(what, op, lambda w, d: _factored(name, v, dg, w, d, what, t), collect=True)
    return P.Derived(what, op, lambda w, d: _function_at(name, op, w, d, what, t), collect=True)


def _disjoint_tensors(ops: Sequence[P.Operator]) -> list[P.Operator] | None:
    """The factors ``[A, B, ...]`` of ``A (x) I (x) ... + I (x) B (x) ...``, each term of one
    non-identity factor in its own position, or None."""
    terms = []
    for o in ops:
        if not isinstance(o, P.Tensor):
            return None
        terms.append(o.factors)
    size = len(terms[0])
    if any(len(fs) != size for fs in terms) or len(terms) != size:
        return None
    out: list[P.Operator | None] = [None] * size
    for fs in terms:
        rest = [k for k, g in enumerate(fs) if not _identity_like(g)]
        if len(rest) != 1 or out[rest[0]] is not None:
            return None
        out[rest[0]] = fs[rest[0]]
    return out  # type: ignore[return-value]


def _factored(
    name: str,
    v: P.Operator,
    dg: P.Operator,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    what: str,
    t: Expr | None,
) -> P.Operator:
    if not is_unitary(v, widths, dims):
        return _function_at(name, P.Compose((v, dg, adjoint(v))), widths, dims, what, t)
    return P.Compose((v, _function_at(name, dg, widths, dims, what, t), adjoint(v)))


def _scaled(f: object, c: Expr) -> object:
    return f if c == 1 else (lambda z: f(c * z))  # type: ignore[operator]


def _diagonal_function(
    name: str,
    op: P.Operator,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    what: str,
    t: Expr | None,
    scale: Expr = sympy.S.One,
) -> P.Operator | None:
    mono = _monomial(op, widths, dims)
    if mono is None:
        return None
    xs, c, g = mono
    c = scale * c
    if tuple(g) != tuple(xs):
        return None
    if name == "log" and not known_nonzero(c):
        raise OperatorError(f"cannot compute {what}: an eigenvalue {c} may be 0")
    if name in MULTIVALUED and not positive(c):
        NOTES.append(f"note: {what} takes the principal branch of {name} at each eigenvalue")
    f = scalar_function(name, t)
    cf = sympy.Lambda(tuple(xs), c)
    two = len(widths) == 1 and P.same(sympy.sympify(dims[0]) ** widths[0], 2)
    if two:
        f0 = P.tidy(sympy.simplify(f(cf(0))))  # type: ignore[operator]
        f1 = P.tidy(sympy.simplify(f(cf(1))))  # type: ignore[operator]
        two = known_nonzero(f0)
        ratio = P.tidy(sympy.simplify(f1 / f0)) if two else None

    def diag(vals: tuple[Expr, ...], ws: tuple[Expr, ...], ds: tuple[Expr, ...]) -> P.State:
        amp = P.tidy(f0 * ratio ** vals[0] if two else f(cf(*vals)))  # type: ignore[operator]
        return P.State(tuple(ws), (P.Term(amp, (), tuple(vals)),), False, tuple(ds))

    return _gate(what, len(widths), diag, op)


def _circulant_function(
    name: str,
    op: P.Operator,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    what: str,
    t: Expr | None,
    scale: Expr = sympy.S.One,
) -> P.Operator | None:
    """``f(A) |x> = 1/N sum_k sum_y w^(k (y - x)) f(l_k) |y>`` for ``A`` commuting with the
    shift on one register of N levels, ``l_k = <k|F^dagger A F|k>``, F the Fourier transform."""
    if len(widths) != 1:
        return None
    n = sympy.sympify(dims[0]) ** widths[0]
    if not _commutes(op, SHIFT, widths, dims):
        return None
    k = sympy.Dummy("k", integer=True, nonnegative=True)
    with P.ranged({k: (sympy.S.Zero, n - 1)}):
        y = P.new_bound("y", 0, n - 1)
        omega = sympy.exp(2 * sympy.pi * sympy.I / n)
        fk = P.State(
            tuple(widths),
            (P.Term(omega ** (k * y.symbol) / sympy.sqrt(n), (y,), (y.symbol,)),),
            False,
            tuple(dims),
        )
        lam = scale * close_sums(P.tidy(sympy.simplify(P.inner(P.dagger(fk), P.apply(op, fk)))))
    if name == "log" and not known_nonzero(lam):
        raise OperatorError(f"cannot compute {what}: an eigenvalue {lam} may be 0")
    if name in MULTIVALUED:
        NOTES.append(f"note: {what} takes the principal branch of {name} at each eigenvalue")
    f = scalar_function(name, t)
    fl = P.tidy(f(lam))  # type: ignore[operator]

    def circ(vals: tuple[Expr, ...], ws: tuple[Expr, ...], ds: tuple[Expr, ...]) -> P.State:
        kb, yb = P.new_bound("k", 0, n - 1), P.new_bound("y", 0, n - 1)
        amp = omega ** (kb.symbol * (yb.symbol - vals[0])) * fl.xreplace({k: kb.symbol}) / n
        return P.State(tuple(ws), (P.Term(P.tidy(amp), (kb, yb), (yb.symbol,)),), False, tuple(ds))

    return _gate(what, 1, circ, op)


def _minimal_function(
    name: str,
    op: P.Operator,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    what: str,
    t: Expr | None,
    scale: Expr = sympy.S.One,
    orders: bool = False,
) -> P.Operator | None:
    """``f(c A)`` by interpolation on the roots of ``x^2 - 1``, ``x^2 - x``, ``x^m - 1`` or
    ``x^m - x`` when ``A`` satisfies it."""
    f = _scaled(scalar_function(name, t), scale)
    ident = P.Identity()
    square = P.Compose((op, op))
    involution = equal_on(square, ident, widths, dims)
    idempotent = None if involution else equal_on(square, op, widths, dims)
    if involution is None and idempotent is None:
        return None
    basis: list[P.Operator]
    if involution:
        eigen = [sympy.S.One, sympy.Integer(-1)]
        basis = [
            P.Scaled(sympy.Rational(1, 2), P.OpSum((ident, op))),
            P.Scaled(sympy.Rational(1, 2), P.OpSum((ident, P.Scaled(-1, op)))),
        ]
    elif idempotent:
        eigen = [sympy.S.Zero, sympy.S.One]
        basis = [P.OpSum((ident, P.Scaled(-1, op))), op]
    elif not orders:
        return None
    else:
        powers: list[P.Operator] = [ident, op, square]
        found = None
        for m in range(3, MAX_ORDER + 1):
            powers.append(P.Compose((op, powers[-1])))
            if equal_on(powers[m], ident, widths, dims):
                found = ("unit", m)
                break
            if equal_on(powers[m], op, widths, dims):
                found = ("idem", m)
                break
        if found is None:
            return None
        kind, m = found
        r = m if kind == "unit" else m - 1
        omega = sympy.exp(2 * sympy.pi * sympy.I / r)
        eigen = [P.tidy(omega**j) for j in range(r)]
        start = 0 if kind == "unit" else 1
        basis = [
            P.Scaled(
                sympy.Rational(1, r),
                P.OpSum(
                    tuple(
                        P.Scaled(
                            P.tidy(omega ** (-j * q)),
                            powers[q if q else (0 if kind == "unit" else r)],
                        )
                        for q in range(start, start + r)
                    )
                ),
            )
            for j in range(r)
        ]
        if kind == "idem":
            eigen.append(sympy.S.Zero)
            basis.append(P.OpSum((ident, P.Scaled(-1, powers[r]))))
    for z in eigen:
        _check_eigen(name, scale * z, what, t)
    _note_cut(name, [scale * z for z in eigen], what, scalar_function(name, t))
    return _interpolate(f, eigen, basis)


ROOTS: dict[sympy.Symbol, tuple[sympy.Poly, int]] = {}
"""The eigenvalue symbols ``λ_j``: the ``j``-th root of an irreducible characteristic polynomial."""

WEIGHTS: dict[sympy.Symbol, sympy.Symbol] = {}
"""The symbol ``w_j = 1/q'(λ_j)`` of each eigenvalue symbol ``λ_j``."""


def _plain_radical(r: Expr) -> bool:
    """Whether ``r`` is built from rationals, ``i`` and square roots of rationals."""
    if r.has(sympy.CRootOf):
        return False
    for g in sympy.preorder_traversal(r):
        if (
            isinstance(g, sympy.Pow)
            and not g.exp.is_Integer
            and (
                g.exp not in (sympy.Rational(1, 2), sympy.Rational(-1, 2)) or not g.base.is_Rational
            )
        ):
            return False
    return True


def root_symbols(q: sympy.Poly) -> list[sympy.Symbol]:
    """The eigenvalue symbols of the roots of ``q``, with their weights."""
    out = []
    for j in range(q.degree()):
        lam = sympy.Symbol(f"λ_{j}", complex=True)
        w = sympy.Symbol(f"w_{j}", complex=True)
        ROOTS[lam] = (q, j)
        WEIGHTS[lam] = w
        out.append(lam)
    return out


def matrix_spectrum(m: sympy.Matrix) -> tuple[str, object] | None:
    """``("radical", [(l, idx, alg)])`` with each eigenvalue in square roots over the rationals,
    its index in the minimal polynomial and its multiplicity; ``("roots", q)`` for an
    irreducible characteristic polynomial ``q`` whose roots are not; None otherwise."""
    lam = sympy.Dummy("lambda")
    cp = m.charpoly(lam).as_expr(lam)
    factors = sympy.factor_list(cp, lam)[1]
    eig: list[tuple[Expr, int]] = []
    hard = False
    for q, mult in factors:
        deg = sympy.degree(q, lam)
        rts = sympy.roots(q, lam) if deg <= 4 else {}
        if sum(rts.values()) == deg and all(_plain_radical(r) for r in rts):
            eig += [(r, mult * k) for r, k in rts.items()]
        else:
            hard = True
    if hard:
        if len(factors) == 1 and factors[0][1] == 1:
            return "roots", sympy.Poly(factors[0][0], lam)
        return None
    out = []
    for r, alg in eig:
        n = m - r * sympy.eye(m.rows)
        idx, prev, pw = 1, n.rank(simplify=True), n
        while idx < alg:
            pw = (pw * n).applyfunc(sympy.expand)
            rk = pw.rank(simplify=True)
            if rk == prev:
                break
            idx, prev = idx + 1, rk
        out.append((r, idx, alg))
    return "radical", out


def hermite(f: object, c: Expr, spec: Sequence[tuple[Expr, int]]) -> list[Expr]:
    """The coefficients of the polynomial ``p`` of degree below ``sum m`` with
    ``p^(r)(l) = (d/dx)^r f(c x)`` at ``x = l`` for ``r < m``, each ``(l, m)`` of ``spec``."""
    x = sympy.Dummy("x")
    deg = sum(m for _, m in spec)
    a = [sympy.Dummy(f"a{k}") for k in range(deg)]
    p = sum((a[k] * x**k for k in range(deg)), sympy.Integer(0))
    g = f(c * x)  # type: ignore[operator]
    eqs = []
    for lv, m in spec:
        for r in range(m):
            eqs.append(sympy.Eq(sympy.diff(p, x, r).subs(x, lv), sympy.diff(g, x, r).subs(x, lv)))
    sol = sympy.solve(eqs, a, dict=True)
    if not sol:
        raise OperatorError("no interpolating polynomial")
    return [sympy.radsimp(sympy.expand(sol[0][ak])) for ak in a]


def root_form(f: object, c: Expr, m: sympy.Matrix, q: sympy.Poly) -> sympy.Matrix:
    """``sum_j f(c l_j) w_j prod_{k != j} (m - l_k)`` over the eigenvalue symbols of ``q``."""
    lams = root_symbols(q)
    one = sympy.eye(m.rows)
    out = sympy.zeros(m.rows, m.cols)
    for j, lj in enumerate(lams):
        e = one
        for k, lk in enumerate(lams):
            if k != j:
                e = e * (m - lk * one)
        out += f(c * lj) * WEIGHTS[lj] * e  # type: ignore[operator]
    return out.applyfunc(sympy.expand)


def _matrix_function(
    name: str, g: P.Gate, what: str, t: Expr | None, scale: Expr = sympy.S.One
) -> P.Operator | None:
    """``f(c M)`` for a gate given by a matrix of concrete size: the Hermite interpolation of
    ``f(c x)`` on the eigenvalues of ``M`` in square roots, or the interpolation on the
    eigenvalue symbols of an irreducible characteristic polynomial."""
    if g.matrix is None:
        return None
    m = sympy.Matrix(g.matrix())
    f = scalar_function(name, t)
    spec = matrix_spectrum(m)
    if spec is None:
        raise OperatorError(
            f"cannot compute {what}: a characteristic polynomial with a repeated factor "
            "whose roots are not square roots over the rationals"
        )
    kind, data = spec
    if kind == "roots":
        assert isinstance(data, sympy.Poly)
        if name in MULTIVALUED:
            NOTES.append(f"note: {what} takes the principal branch of {name} at each eigenvalue")
        out = root_form(f, scale, m, data)
        names = ", ".join(f"λ_{j}" for j in range(data.degree()))
        x = sympy.Symbol("x")
        NOTES.append(
            f"note: {names} are the roots of q = {sympy.sstr(data.as_expr().subs(data.gen, x))}, "
            "w_j = 1/q'(λ_j)"
        )
    else:
        assert isinstance(data, list)
        for z, _, _ in data:
            _check_eigen(name, scale * z, what, t)
        _note_cut(name, [scale * z for z, _, _ in data], what, f)
        coeffs = hermite(f, scale, [(z, idx) for z, idx, _ in data])
        out = sympy.zeros(m.rows, m.cols)
        power = sympy.eye(m.rows)
        for k, ak in enumerate(coeffs):
            if k:
                power = (m * power).applyfunc(sympy.expand)
            out += ak * power
        out = out.applyfunc(lambda e: P.tidy(sympy.simplify(e)))
    entries = [[out[r, c] for c in range(out.cols)] for r in range(out.rows)]
    return _matrix_from(g, entries, what)


def _matrix_from(g: P.Gate, entries: list[list[Expr]], name: str) -> P.Gate:
    """The gate on the registers of ``g`` with the matrix ``entries``."""

    def fn(vals: tuple[Expr, ...], widths: tuple[Expr, ...], dims: tuple[Expr, ...]) -> P.State:
        sizes = [int(sympy.sympify(d) ** w) for w, d in zip(widths, dims, strict=True)]
        col = sympy.Integer(0)
        for v, n in zip(vals, sizes, strict=True):
            col = col * n + v
        terms = []
        for r, row in enumerate(entries):
            amp = (
                row[int(col)]
                if col.is_Integer
                else sympy.Add(
                    *(e * sympy.KroneckerDelta(col, c) for c, e in enumerate(row) if e != 0)
                )
            )
            if amp != 0:
                digits, rest = [], r
                for n in reversed(sizes):
                    rest, dgt = divmod(rest, n)
                    digits.append(sympy.Integer(dgt))
                terms.append(P.Term(amp, (), tuple(reversed(digits))))
        if not terms:
            terms.append(P.Term(sympy.S.Zero, (), tuple(sympy.S.Zero for _ in sizes)))
        return P.State(tuple(widths), tuple(terms), False, tuple(dims))

    return dataclasses.replace(
        g,
        name=name,
        fn=fn,
        oracle=False,
        checked=set(),
        base=g.base or g,
        source=name,
        matrix=lambda: entries,
    )


def _function_at(
    name: str,
    op: P.Operator,
    widths: tuple[Expr, ...],
    dims: tuple[Expr, ...],
    what: str,
    t: Expr | None,
) -> P.Operator:
    c = sympy.S.One
    core = op
    while isinstance(core, P.Scaled):
        c, core = c * sympy.sympify(core.factor), core.op
    out = _diagonal_function(name, core, widths, dims, what, t, c)
    if out is None:
        out = _minimal_function(name, core, widths, dims, what, t, c)
    if out is None:
        out = _circulant_function(name, core, widths, dims, what, t, c)
    if out is None:
        out = _minimal_function(name, core, widths, dims, what, t, c, orders=True)
    if out is None and isinstance(core, P.Gate):
        out = _matrix_function(name, core, what, t, c)
    if out is None and name == "exp" and isinstance(core, P.OpSum) and len(core.ops) > 1:
        fs = [P.Scaled(c, g) for g in core.ops]
        if all(
            _commutes(fs[a], fs[b], widths, dims)
            for a in range(len(fs))
            for b in range(a + 1, len(fs))
        ):
            return P.Compose(
                tuple(_function_at("exp", g, widths, dims, f"exp({_name(g)})", None) for g in fs)
            )
        raise OperatorError(f"cannot compute {what}: A + B with non-commuting terms")
    if out is None:
        raise OperatorError(f"cannot compute {what}: no spectral form known for {_name(op)}")
    return out
