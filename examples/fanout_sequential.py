"""n CNOTs from one control applied one after another equal the fanout gate that applies all of
them in one layer, for every n.

Run:  python examples/fanout_sequential.py
"""

from diracula import Program

ula = Program()
n, t = ula.var("n", "t")
ula("gate CX = |c>|y> -> |c>|y xor c*2^j>")  # CNOT onto bit j of the target register
ula("gate FAN = |c>|y> -> |c>|y xor c*(2^n - 1)>")  # every target bit at once

ula.zeros = ula.ket(0) ** n
ula.start = (ula.H | ula.ket(0)) @ ula["0 |zeros> + |t>"]  # control |+>, targets |t>

ula.seq = ula.start
ula("for j in 0..n { |seq> = CX |seq> }")
ula.par = ula.FAN | ula.start
ula.show(ula.seq, ula.par)
assert (ula.par.dag() | ula.seq).sympy() == 1
assert (ula.seq.dag() | ula.seq).sympy() == 1
print("sequential fanout = one-layer fanout, for every n")
