"""The cyclic shift of n qudits, composed with itself n times, is the identity, for every n
and d. On a value x < d^n - 1 the shift is x -> d x mod (d^n - 1); d^n - 1 is fixed.

Run:  python examples/cyclic_shift.py
"""

from diracula import Program

ula = Program()
ula.var("n", "d", "x")
ula("var M = d^n - 1")
ula("func rot(y) = ifelse(y < M, (y*d) % M, y)")
ula("gate ROT = |y> -> |rot(y)>")

ula("|zeros>_d = |0>_d^@n")
ula("|s>_d = 0 |zeros> + |x>")
ula("|x0>_d = 0 |zeros> + |x>")
ula.show(ula.ROT | ula.s)

ula("for j in 0..n { |s> = ROT |s> }")
ula.show(ula.s)
assert (ula.x0.dag() | ula.s).sympy() == 1
print("ROT^n = I, for every n and d")
