"""The QFT adder (Draper) on n qudits of dimension d implements |x> -> |x + 1 mod d^n>, for
every n and d: a phase on each Fourier digit, between the QFT and its inverse.

Run:  python examples/qft_adder.py
"""

from diracula import Program

ula = Program()
ula.var("n", "d", "x")
ula("var Q = d^n")
ula("gate QFT = |x>_d -> 1/sqrt(Q) sum(k in 0..Q){ e^(2*pi*i*x*k/Q) |k>_d }")
ula("gate IQFT = |x>_d -> 1/sqrt(Q) sum(k in 0..Q){ e^(-2*pi*i*x*k/Q) |k>_d }")
ula("gate P = |k> -> e^(2*pi*i*d^j*(floor(k/d^j) % d)/Q) |k>")  # phase on digit j

ula("|zeros>_d = |0>_d^@n")
ula("|a>_d = 0 |zeros> + |x>")
ula.a = ula.QFT | ula.a
ula("for j in 0..n { |a> = P |a> }")
ula.show(ula.a)
ula.a = ula.IQFT | ula.a
ula.show(ula.a)

ula("|want>_d = 0 |zeros> + |(x + 1) % Q>")
assert (ula.want.dag() | ula.a).sympy() == 1
assert (ula.a.dag() | ula.a).sympy() == 1
print("QFT adder: |x> -> |x + 1 mod d^n>, for every n and d")
