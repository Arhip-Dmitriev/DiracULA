"""Phase estimation with n qudits of dimension d, n and d symbolic: for an eigenphase m/d^n the
controlled-U^(d^j) stages followed by the inverse QFT give |m> exactly (m read mod d^n).

Run:  python examples/phase_estimation.py
"""

from diracula import Program

ula = Program()
n = ula.var("n", "d", "m")[0]
ula("var Q = d^n")
ula("gate F = |x>_d -> 1/sqrt(d) sum(y in 0..d){ e^(2*pi*i*x*y/d) |y>_d }")
ula("gate IQFT = |x>_d -> 1/sqrt(Q) sum(k in 0..Q){ e^(-2*pi*i*x*k/Q) |k>_d }")
ula("gate U = |y> -> e^(2*pi*i*m*y/Q) |y>")  # U|1> = e^(2 pi i m/Q) |1>
# U^(d^j) controlled by digit j of the counting register
ula("gate CU = |x>|y> -> e^(2*pi*i*m*y*d^j*(floor(x/d^j) % d)/Q) |x>|y>")

ula.show(ula.U | ula.ket(1))
ula.p = (ula.F**n | ula.ket(0, "d") ** n) @ ula.ket(1)
ula("for j in 0..n { |p> = CU |p> }")
ula.show(ula.p)
ula.p = (ula.IQFT @ ula.I) | ula.p
ula.show(ula.p)

ula("|zeros>_d = |0>_d^@n")
ula.want = ula["0 |zeros> + |m % Q>"] @ ula.ket(1)
assert (ula.want.dag() | ula.p).sympy() == 1
assert (ula.p.dag() | ula.p).sympy() == 1
print("phase estimation returns the eigenphase digits exactly, for every n and d")
