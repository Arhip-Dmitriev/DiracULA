"""The repetition-code encoder maps a logical qubit a|0> + b|1> to a|0...0> + b|1...1>, for a
symbolic code distance n + 1: CNOTs from the logical qubit onto n ancillas in |0>.

Run:  python examples/repetition_code.py
"""

from diracula import Program

ula = Program()
n = ula.var("n")
a, b = ula.var("a", "b", type="complex")
ula("gate CX = |c>|y> -> |c>|y xor c*2^j>")  # CNOT onto ancilla j

ula.enc = (a * ula.ket(0) + b * ula.ket(1)) @ ula.ket(0) ** n
ula("for j in 0..n { |enc> = CX |enc> }")
ula.show(ula.enc)

ula.want = a * ula.ket(0) @ ula.ket(0) ** n + b * ula.ket(1) @ ula.ket(1) ** n
norm = (ula.want.dag() | ula.want).sympy()
assert (ula.want.dag() | ula.enc).sympy() == norm
assert (ula.enc.dag() | ula.enc).sympy() == norm
print("the encoder maps a|0> + b|1> to a|0...0> + b|1...1>, for every distance")
