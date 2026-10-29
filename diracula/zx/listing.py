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

"""The graph listing of a diagram (:func:`render_graph`), the rule of a phase vector in the
index symbol ``k`` (:func:`rule_turns`) and the session notation modes."""

from __future__ import annotations

import enum
from collections.abc import Callable, Mapping, Sequence
from typing import TypeAlias

import sympy as sp  # type: ignore[import-untyped]  # sympy ships no py.typed marker

from diracula.zx.bangbox import BangBox, BangBoxError, Mult
from diracula.zx.dimension import Dim, DimensionError
from diracula.zx.generators import GeneratorError
from diracula.zx.graph import Diagram, Direction, GraphError, PortRef, Wire
from diracula.zx.phase import INDEX, Phase, PhaseError, PhaseVector
from diracula.zx.scalar import Scalar, ScalarError


class ListingError(Exception):
    """A call outside the listing's domain."""


_FOREIGN = (
    BangBoxError,
    DimensionError,
    GeneratorError,
    GraphError,
    PhaseError,
    ScalarError,
)


class NotationMode(enum.Enum):
    """The session notation mode: which renderings :func:`render` emits."""

    DIRAC = "dirac"
    ZX = "zx"
    BOTH = "both"
    RAW = "raw"


DEFAULT_MODE = NotationMode.DIRAC
"""The notation mode a session starts in."""


def rule_turns(phase: PhaseVector) -> sp.Expr:
    """The rule of ``phase`` written in the index symbol ``k``."""
    assert phase.rule is not None
    return phase.rule.to_sympy_turns().xreplace({INDEX: sp.Symbol("k", integer=True)})


_LISTING_INDENT = "  "


def _listing_count(n: int, noun: str) -> str:
    return f"{n} {noun}" if n == 1 else f"{n} {noun}s"


def _listing_expr(value: object) -> str:
    """``sstr`` of a sympy expression (or ``str`` of anything else), ``**`` shown as ``^``."""
    to_sympy = getattr(value, "to_sympy", None)
    text = sp.sstr(to_sympy()) if callable(to_sympy) else str(value)
    return str(text).replace("**", "^")


def _listing_node(node_id: object) -> str:
    """``n3`` for an int id, ``n'x'`` (the repr) for anything else."""
    if isinstance(node_id, int) and not isinstance(node_id, bool):
        return f"n{int(node_id)}"
    return f"n{node_id!r}"


def _listing_ref(ref: PortRef) -> str:
    side = "out" if ref.direction is Direction.OUTPUT else "in"
    return f"{_listing_node(ref.node_id)}.{side}{ref.index}"


def _listing_ref_key(ref: PortRef) -> tuple[int, int, str, str, int]:
    """``sort_key`` order for int node ids, then any other id by its repr."""
    node_id = ref.node_id
    if isinstance(node_id, int) and not isinstance(node_id, bool):
        return (0, int(node_id), "", ref.direction.value, ref.index)
    return (1, 0, repr(node_id), ref.direction.value, ref.index)


def _listing_wire_key(
    wire: Wire,
) -> tuple[tuple[int, int, str, str, int], tuple[int, int, str, str, int]]:
    a, b = sorted((_listing_ref_key(wire.a), _listing_ref_key(wire.b)))
    return (a, b)


def _listing_wire(wire: Wire) -> str:
    a, b = sorted((wire.a, wire.b), key=_listing_ref_key)
    return f"{_listing_ref(a)} -- {_listing_ref(b)}"


def _listing_refs(refs: Sequence[PortRef]) -> str:
    return "[" + ", ".join(_listing_ref(r) for r in refs) + "]"


def _listing_phase(phase: PhaseVector | None) -> str:
    """``  phase[d]: {1: 1/3} turns``, ``  phase[d]: 0`` for a zero vector, empty for None."""
    if phase is None:
        return ""
    if phase.is_zero:
        return f"  phase[{_listing_expr(phase.dim)}]: 0"
    parts = [
        f"{index}: {_listing_expr(sp.sstr(p.to_sympy_turns()))}"
        for index, p in sorted(phase.entries().items())
    ]
    if phase.rule is not None:
        parts.append(f"k: {_listing_expr(sp.sstr(rule_turns(phase)))}")
    entries = ", ".join(parts)
    return f"  phase[{_listing_expr(phase.dim)}]: {{{entries}}} turns"


def _listing_header(kind: str, nodes: int, wires: int, inputs: int, outputs: int) -> str:
    return (
        f"{kind}: {_listing_count(nodes, 'node')}, {_listing_count(wires, 'wire')}, "
        f"{_listing_count(inputs, 'input')} -> {_listing_count(outputs, 'output')}"
    )


def _listing_parameters(parameters: Mapping[str, int]) -> str:
    if not parameters:
        return "parameters: none"
    return "parameters: " + ", ".join(f"{k} = {v}" for k, v in sorted(parameters.items()))


_ROLE_SYMBOLS: dict[str, Callable[[str], sp.Symbol]] = {
    "dimension": lambda name: Dim.symbol(name).to_sympy(),
    "multiplicity": lambda name: Mult.symbol(name).to_sympy(),
    "exponent": lambda name: sp.Symbol(name, integer=True, nonnegative=True),
    "phase": lambda name: Phase.symbol(name).to_sympy_turns(),
    "scalar": lambda name: Scalar.symbol(name).to_sympy(),
}


def _role_of(symbol: sp.Symbol) -> str | None:
    for role, make in _ROLE_SYMBOLS.items():
        try:
            if make(str(symbol.name)) == symbol:
                return role
        except (*_FOREIGN, TypeError, ValueError):
            return None
    return None


def _inferred_roles(
    dims: Sequence[Dim], mults: Sequence[Mult], phases: Sequence[Phase]
) -> dict[str, sp.Symbol]:
    """Symbol per name as a listing reader infers it: dimension, multiplicity, exponent,
    phase, first wins."""
    dim_symbols = [s for dim in dims for s in dim.to_sympy().free_symbols]
    groups = [
        [s for s in dim_symbols if s.is_positive],
        [s for mult in mults for s in mult.to_sympy().free_symbols],
        [s for s in dim_symbols if not s.is_positive],
        [s for phase in phases for s in phase.to_sympy_turns().free_symbols],
    ]
    table: dict[str, sp.Symbol] = {}
    for group in groups:
        for symbol in sorted(group, key=lambda s: str(s.name)):
            table.setdefault(str(symbol.name), symbol)
    return table


def _listing_roles(diagram: Diagram) -> str | None:
    """``roles: NAME = ROLE, ...`` for each scalar or phase symbol a listing reader would
    infer differently, or None when there is none."""
    dims: list[Dim] = []
    phases: list[Phase] = []
    for node in diagram.nodes.values():
        dims.extend(port.dim for port in (*node.inputs, *node.outputs))
        if node.phase is not None:
            dims.append(node.phase.dim)
            phases.extend(node.phase.entries().values())
            if node.phase.rule is not None:
                phases.append(node.phase.rule.at(1))
    mults = [box.multiplicity for box in diagram.bang_boxes.values()]
    wrong: dict[str, sp.Symbol] = {}
    for table, symbols, default in (
        (
            _inferred_roles(dims, mults, []),
            {s for p in phases for s in p.to_sympy_turns().free_symbols},
            "phase",
        ),
        (
            _inferred_roles(dims, mults, phases),
            diagram.scalar.to_sympy().free_symbols,
            "scalar",
        ),
    ):
        for symbol in symbols:
            if not isinstance(symbol, sp.Symbol):
                continue
            name = str(symbol.name)
            inferred = table.get(name)
            if inferred is None:
                try:
                    inferred = _ROLE_SYMBOLS[default](name)
                except (*_FOREIGN, TypeError, ValueError):
                    continue
            if inferred != symbol and _role_of(symbol) is not None:
                wrong.setdefault(name, symbol)
    if not wrong:
        return None
    return "roles: " + ", ".join(f"{n} = {_role_of(s)}" for n, s in sorted(wrong.items()))


_ForestEntry: TypeAlias = tuple[int, int, object, str | None]


def _listing_forest(ids: Sequence[int], parent_of: Mapping[int, object]) -> list[_ForestEntry]:
    """Depth-first ``(id, depth, parent, flag)`` order, children ascending by id. Roots: no
    parent, or a missing one (flag ``missing``); each parent cycle is cut at its smallest id
    (flag ``cycle``). Iterative."""
    known = set(ids)
    children: dict[int, list[int]] = {i: [] for i in ids}
    for i in sorted(ids):
        parent = parent_of.get(i)
        if parent is not None and parent in known:
            children[parent].append(i)
    order: list[_ForestEntry] = []
    seen: set[int] = set()

    def walk(root: int, flag: str | None) -> None:
        stack = [(root, 0)]
        while stack:
            i, depth = stack.pop()
            if i in seen:
                continue
            seen.add(i)
            order.append((i, depth, parent_of.get(i), flag if i == root else None))
            stack.extend((c, depth + 1) for c in reversed(children[i]) if c not in seen)

    for i in sorted(ids):
        parent = parent_of.get(i)
        if parent is None:
            walk(i, None)
        elif parent not in known:
            walk(i, "missing")
    for i in sorted(ids):
        if i in seen:
            continue
        position: dict[int, int] = {}
        path: list[int] = []
        current = i
        while current not in position:
            position[current] = len(path)
            path.append(current)
            current = parent_of[current]  # type: ignore[assignment]
        walk(min(path[position[current] :]), "cycle")
    return order


def _listing_depths(order: Sequence[_ForestEntry]) -> dict[int, int]:
    return {i: depth for i, depth, _, _ in order}


def render_graph(diagram: Diagram) -> str:
    """The graph listing of ``diagram``: header, scalar, parameters, nodes, wires, boundary,
    bang-box forest. Never fails on a :class:`Diagram`, valid or not."""
    if not isinstance(diagram, Diagram):
        raise ListingError(f"render_graph requires a Diagram, got {type(diagram).__name__}")
    boxes: dict[int, BangBox] = {int(b): box for b, box in diagram.bang_boxes.items()}
    order = _listing_forest(sorted(boxes), {i: box.parent for i, box in boxes.items()})
    depth = _listing_depths(order)
    port_boxes: dict[PortRef, list[int]] = {}
    node_boxes: dict[int, list[int]] = {}
    for i, box in boxes.items():
        for ref in box.port_scope:
            port_boxes.setdefault(ref, []).append(i)
        for nid in box.node_scope:
            node_boxes.setdefault(int(nid), []).append(i)

    def box_order(ids: list[int]) -> list[int]:
        return sorted(ids, key=lambda i: (depth.get(i, 0), i))

    lines = [
        _listing_header(
            "graph",
            len(diagram.nodes),
            len(diagram.wires),
            len(diagram.boundary_inputs),
            len(diagram.boundary_outputs),
        ),
        f"scalar: {_listing_expr(diagram.scalar)}",
        _listing_parameters(diagram.parameters),
    ]
    roles = _listing_roles(diagram)
    if roles is not None:
        lines.append(roles)
    lines.append("nodes:" if diagram.nodes else "nodes: none")
    for nid in sorted(diagram.nodes, key=int):
        node = diagram.nodes[nid]
        sides = []
        for label, ports, direction in (
            ("in", node.inputs, Direction.INPUT),
            ("out", node.outputs, Direction.OUTPUT),
        ):
            texts = []
            for index, port in enumerate(ports):
                ref = PortRef(nid, direction, index)
                marks = "".join(f"!{b}" for b in box_order(port_boxes.get(ref, [])))
                texts.append(_listing_expr(port.dim) + marks)
            sides.append(f"{label}: [{', '.join(texts)}]")
        line = f"{_LISTING_INDENT}n{int(nid)}  {node.generator_type.name}  " + "  ".join(sides)
        line += _listing_phase(node.phase)
        chain = box_order(node_boxes.get(int(nid), []))
        if chain:
            line += "  boxes: " + " > ".join(f"!{b}" for b in chain)
        lines.append(line)
    lines.append("wires:" if diagram.wires else "wires: none")
    for wire in sorted(diagram.wires, key=_listing_wire_key):
        lines.append(_LISTING_INDENT + _listing_wire(wire))
    lines.append(f"inputs: {_listing_refs(diagram.boundary_inputs)}")
    lines.append(f"outputs: {_listing_refs(diagram.boundary_outputs)}")
    lines.append("bang boxes:" if boxes else "bang boxes: none")
    for i, level, parent, flag in order:
        box = boxes[i]
        if box.node_scope:
            scope = "nodes: " + ", ".join(_listing_node(n) for n in sorted(box.node_scope))
        else:
            scope = "ports: " + ", ".join(
                _listing_ref(r) for r in sorted(box.port_scope, key=_listing_ref_key)
            )
        line = f"{_LISTING_INDENT * (level + 1)}!{i}  x {_listing_expr(box.multiplicity)}  {scope}"
        if flag is not None:
            line += f"  parent: !{parent} ({flag})"
        lines.append(line)
    return _listing_join([lines[0], *(_LISTING_INDENT + line for line in lines[1:])])


def _listing_join(lines: Sequence[str]) -> str:
    return "\n".join(line.rstrip() for line in lines)
