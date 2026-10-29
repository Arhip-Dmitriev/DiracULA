"""X^a Z^b passed through H^@n becomes Z^a X^b, for every n and all n-bit strings a, b:
H^@n X^a Z^b H^@n = Z^a X^b.

Run:  python examples/pauli_through_hadamard.py
"""

from diracula import Program

ula = Program()
n = ula.var("n", "x", "a", "b")[0]
ula("gate XA = |y> -> |y xor a>")
ula("gate ZB = |y> -> (-1)^dot(y, b) |y>")
ula("gate XB = |y> -> |y xor b>")
ula("gate ZA = |y> -> (-1)^dot(y, a) |y>")

ula.zeros = ula.ket(0) ** n
ula.w = ula["0 |zeros> + |x>"]  # an arbitrary basis state

hn = ula.H**n
ula.lhs = hn | (ula.XA | (ula.ZB | (hn | ula.w)))
ula.rhs = ula.ZA | (ula.XB | ula.w)
ula.show(ula.rhs)
assert (ula.rhs.dag() | ula.lhs).sympy() == 1
assert (ula.rhs.dag() | ula.rhs).sympy() == 1
print("H^@n X^a Z^b H^@n = Z^a X^b, for every n")
