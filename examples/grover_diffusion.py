"""The Grover diffusion operator, for every n:
H^@n (2|0><0| - I) H^@n = 2|s><s| - I,  |s> = H^@n |0>^@n.

Run:  python examples/grover_diffusion.py
"""

from diracula import Program

ula = Program()
n = ula.var("n", "x")[0]
ula.zeros = ula.ket(0) ** n
ula.s = ula.H**n | ula.zeros
ula.w = ula["0 |zeros> + |x>"]  # an arbitrary basis state

reflect_zero = 2 * (ula.zeros | ula.zeros.dag()) - ula.I
reflect_s = 2 * (ula.s | ula.s.dag()) - ula.I
ula.lhs = ula.H**n | (reflect_zero | (ula.H**n | ula.w))
ula.rhs = reflect_s | ula.w
ula.show(ula.rhs)
assert (ula.lhs.dag() | ula.rhs).sympy() == 1
assert (ula.lhs.dag() | ula.lhs).sympy() == 1
assert (ula.rhs.dag() | ula.rhs).sympy() == 1
print("H^@n (2|0><0| - I) H^@n = 2|s><s| - I, for every n")
