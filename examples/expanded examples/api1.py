from diracula import Program, ula

ula("var n")
ula.psi = ula.H**ula.n | ula.ket(0) ** ula.n
print(ula.psi)
ula["|phi>"] = ula["|psi> - 2 |0><0|psi>"]
print(ula.phi)
print(ula.phi.latex())
y = ula.measure | ula.psi
print(y)
p = Program()
p("|b> = CNOT (H @ I) |0>|0>")
print(p.b)
print(p.measure | p.b)
p("var t: real")
p("gate RY = [[cos(t/2), -sin(t/2)], [sin(t/2), cos(t/2)]]")
print(p["RY |0>"])
print(p["<0|RY|0>"])
q = Program()
q.s = q.ket(1) + q.ket(0)
print(q.s)
print(q["<s|s>"])
q("gate CZ = |a>|b> -> (-1)^(a*b) |a>|b>")
print(q["CZ (|+> @ |+>)"])
print(q.CZ)
print(float(q["<s|s>"]) if hasattr(q["<s|s>"], "__float__") else "no float")
print(repr(q["<s|s>"]))
