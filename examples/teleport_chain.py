"""Teleporting a qudit along n hops is the identity, for every n and d and every Bell outcome
(u, v) with its Pauli correction.

Run:  python examples/teleport_chain.py
"""

from diracula import Program

ula = Program()
ula.var("n", "d", "u", "v")
ula("|B>_d = 1/sqrt(d) sum(k in 0..d){ |k>_d @ |k>_d }")
ula("|Buv>_d = 1/sqrt(d) sum(k in 0..d){ e^(2*pi*i*v*k/d) |(k + u) % d>_d @ |k>_d }")

# One hop: a fresh Bell pair, the Bell measurement reading (u, v), then the correction.
ula("gate HOP = |a>_d -> d sum(c in 0..d){ ((<Buv| @ <c|_d)(|a>_d @ |B>)) |c>_d }")
ula("gate FIX = |c>_d -> e^(2*pi*i*v*c/d) |(c + u) % d>_d")

ula("|psi>_d = 1/sqrt(d) sum(k in 0..d){ e^(2*pi*i*k^2/d) |k>_d }")
ula.show(ula.FIX | (ula.HOP | ula.psi))

ula.chain = ula.psi
ula("for j in 0..n { |chain> = FIX HOP |chain> }")
ula.show(ula.chain)
assert (ula.psi.dag() | ula.chain).sympy() == 1
assert (ula.chain.dag() | ula.chain).sympy() == 1
print("n hops of teleportation are the identity, for every n and d")
