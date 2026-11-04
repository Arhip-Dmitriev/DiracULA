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

"""Replacements installed into sympy on import.

``Mod.eval`` on an integer product with a ``Mod`` factor: ``Mod(b, m)`` with q | m becomes b,
integer coefficients reduce mod q, anything else stays unevaluated; other inputs go to sympy's
own ``eval``. ``powsimp`` gets ``exp`` exponents expanded into sums, retries an input it
asserts on with powers of ``I`` written as exponentials, and returns the input unchanged if that
fails too.
"""

from __future__ import annotations

from typing import Any

import sympy  # type: ignore[import-untyped]  # sympy ships no py.typed marker

_ORIGINAL = sympy.Mod.eval.__func__
_POWSIMP = sympy.powsimp


def _i_as_exp(expr: sympy.Basic) -> sympy.Basic:
    return expr.replace(
        lambda x: x.is_Pow and x.base is sympy.I,
        lambda x: sympy.exp(sympy.I * sympy.pi * x.exp / 2),
    )


def _expanded_exp(x: sympy.Basic) -> sympy.Basic:
    e = sympy.expand(x.exp)
    return sympy.exp(e) if e.is_Add else x


def _exp_sums(expr: Any) -> Any:
    """``exp`` exponents that expand into sums, expanded."""
    if not isinstance(expr, sympy.Basic):
        return expr
    return expr.replace(
        lambda x: isinstance(x, sympy.exp) and not x.exp.is_Add and x.exp.has(sympy.Add),
        _expanded_exp,
    )


def _powsimp(expr: Any, *args: Any, **kwargs: Any) -> Any:
    expr = _exp_sums(expr)
    try:
        return _POWSIMP(expr, *args, **kwargs)
    except AssertionError:
        try:
            return _POWSIMP(_i_as_exp(sympy.sympify(expr)), *args, **kwargs)
        except AssertionError:
            return expr


def _divides(q: sympy.Expr, m: sympy.Expr) -> bool:
    if q.is_Integer and m.is_Integer:
        return int(m) % int(q) == 0
    return bool(q == m)


def _eval(cls: type, p: sympy.Expr, q: sympy.Expr) -> sympy.Expr | None:
    if not (
        isinstance(p, sympy.Mul)
        and q.is_integer
        and q != 0
        and any(isinstance(a, sympy.Mod) for a in p.args)
        and all(a.is_integer for a in p.args)
    ):
        return _ORIGINAL(cls, p, q)
    args = []
    for a in p.args:
        if isinstance(a, sympy.Mod) and _divides(q, a.args[1]):
            args.append(a.args[0])
        elif a.is_Integer and q.is_Integer:
            args.append(sympy.Integer(int(a) % int(q)))
        else:
            args.append(a)
    if any(a == 0 for a in args):
        return sympy.S.Zero
    if args == list(p.args):
        return None
    return cls(sympy.Mul(*args), q)


sympy.Mod.eval = classmethod(_eval)
sympy.powsimp = _powsimp
sympy.core.cache.clear_cache()
