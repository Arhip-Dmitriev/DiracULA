"""Deutsch-Jozsa over Z_d^n, n and d symbolic: one oracle query separates a constant f from a
balanced f.

Run:  python examples/deutsch_jozsa_qudits.py
"""

from diracula import Program

ula = Program()
n, d, c = ula.var("n", "d", "c")
ula("gate F = |x>_d -> 1/sqrt(d) sum(y in 0..d){ e^(2*pi*i*x*y/d) |y>_d }")
ula("gate Fd = |x>_d -> 1/sqrt(d) sum(y in 0..d){ e^(-2*pi*i*x*y/d) |y>_d }")
ula("gate U_const = |x>|y>_d -> |x>|(y + c) % d>_d")  # f(x) = c
ula("gate U_bal = |x>|y>_d -> |x>|(y + x) % d>_d")  # f(x) = x mod d, balanced

start = ula.ket(0, "d") ** n @ ula.ket(1, "d")
first = ula.F**n @ ula.Fd
last = ula.Fd**n @ ula.I
target = (ula.ket(0, "d") ** n @ (ula.Fd | ula.ket(1, "d"))).dag()

ula.out_const = last | (ula.U_const | (first | start))
ula.out_bal = last | (ula.U_bal | (first | start))
ula.show(ula.out_const, ula.out_bal)

a_const = (target | ula.out_const).sympy()
a_bal = (target | ula.out_bal).sympy()
print(f"constant: <0...0|out> = {a_const}")
print(f"balanced: <0...0|out> = {a_bal}")
assert abs(a_const) == 1
assert a_bal == 0
