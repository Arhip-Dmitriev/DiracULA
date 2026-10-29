"""A guided tour of the ula Python embedding, ending in Deutsch-Jozsa for a symbolic n.

Run:  python examples/learn_ula.py
"""

from diracula import Program

# ---- 1. A program -------------------------------------------------------------------------
# A Program is one interpreter. `from diracula import ula` gives a shared default one.
ula = Program()

# Calling the program runs .ula statements and returns what show/print printed.
print(ula("var a = 3\nshow(a)"))

# ---- 2. Variables -------------------------------------------------------------------------
# ula.var declares symbols (default type nat) and returns them as Values.
n = ula.var("n")
t = ula.var("t", type="real")
ula.show(n, t)
ula("assume n > 0")

# Attribute assignment names a value in the program; Python numbers become exact numbers.
ula.b = ula.a**2 + 1  # ** on scalars is power
ula.show(ula.b)  # show prints; render returns the text

# A Value has no ==; .sympy() gives the sympy expression, int()/float() a number.
assert ula.b.sympy() == 10
assert int(ula.b) == 10

# ---- 3. Language syntax inside Python -----------------------------------------------------
# ula["..."] evaluates one .ula expression; ula["|name>"] = ... assigns in .ula syntax.
print(ula["sqrt(8)"], ula["gcd(12, 18)"], ula["sum(k in 0..=4){ k }"])
ula["|phi>"] = ula["normalise(|0> + |1>)"]
ula.show(ula.phi)

# Python values can be spliced into statements with f-strings.
for k in range(3):
    ula(f"var c{k} = {k} ^ 2")
ula.show(ula.c0, ula.c1, ula.c2)

# ---- 4. Kets, bras and the operators ------------------------------------------------------
#   |   juxtaposition: apply, inner/outer product, tensor of kets
#   @   tensor product
#   **  tensor power of states and operators
#   .dag()  conjugate transpose
ula.p = ula.ket(0) + ula.ket(1)  # |0> + |1>
ula.v = ula.ket(2, 3)  # |2>_3
ula.show(ula.p, ula.v)
print(ula.bra(0) | ula.ket("+"))  # <0|+>
print(ula.ket("+").dag() | ula.ket("-"))  # <+|->
ula.zeros = ula.ket(0) ** n  # |0>^@n, n symbolic
ula.show(ula.zeros)

# ---- 5. Gates -----------------------------------------------------------------------------
# Built-in gates are attributes: H X Y Z S T CNOT SWAP I.
ula.c = ula.H | ula.ket(0)
ula.show(ula.c)

# Python's | groups from the left, the .ula language from the right:
#   CNOT (H @ I) |0>|0>  becomes  CNOT | (H @ I) | (|0> @ |0>)
ula.bell = ula.CNOT | (ula.H @ ula.I) | (ula.ket(0) @ ula.ket(0))
ula.show(ula.bell)

# New gates and functions are defined with .ula statements, then used as attributes.
ula("func f(x) = bit(x, 0)")
ula("gate U_f = |x>|y> -> |x>|y xor f(x)>")
ula("gate QFT = |x>_d -> 1/sqrt(d) sum(y in 0..d){ e^(2*pi*i*x*y/d) |y>_d }")
ula.var("d")
ula.show(ula.QFT | ula.ket(0, "d"))

# ---- 6. Output ----------------------------------------------------------------------------
print(ula.c)  # unicode
print(ula.c.ascii())
print(ula.c.latex())  # also rendered by Jupyter
print(ula.c.vector())  # numpy amplitudes of a concrete state
print(sorted(ula.names()))  # every user-defined name

# ---- 7. Measurement -----------------------------------------------------------------------
# ula.measure | state (or ula.measure(state)) returns the Born distribution and leaves the
# named state as the mixture of its outcomes.
ula.coin = ula.H | ula.ket(0)
print(ula.measure | ula.coin)
ula.show(ula.coin)
# Functions of the outcome go through the language syntax.
# In Python @ binds tighter than |, so (H |0>) @ |1> needs its parentheses.
ula.two = (ula.H | ula.ket(0)) @ ula.ket(1)
print(ula["floor(measure|two> / 2)"])

# ---- 8. Deutsch-Jozsa for n qubits, n symbolic --------------------------------------------
# f : {0,1}^n -> {0,1} is promised constant or balanced. One query of
#   U_f |x>|y> = |x>|y xor f(x)>
# inside H^@n ... H^@n decides which: the first register reads all zeros iff f is constant.
oracles = {"zero": "0", "one": "1", "bal": "bit(x, 0)"}

start = ula.ket(0) ** n @ ula.ket(1)
target = ula.bra(0) ** n @ ula.bra("-")
first = ula.H**n @ ula.H
last = ula.H**n @ ula.I
amps = {}

for name, body in oracles.items():
    ula(f"func f_{name}(x) = {body}")
    ula(f"gate O_{name} = |x>|y> -> |x>|y xor f_{name}(x)>")
    oracle = getattr(ula, f"O_{name}")

    # Building the circuit from Python Values.
    ula[f"|out_{name}>"] = last | oracle | first | start
    out = getattr(ula, f"out_{name}")
    ula.show(out)

    # Proof for every n: the amplitude of |0...0>|-> is +-1 if f is constant, 0 if balanced.
    amp = amps[name] = (target | out).sympy()
    kind = "constant" if abs(amp) == 1 else "balanced" if amp == 0 else "undecided"
    print(f"f_{name}: <0...0,-|out> = {amp}  ->  {kind}")

    # Measuring: the outcome of the n+1 qubits is 2x + y; floor(./2) keeps x.
    x = ula[f"floor(measure|out_{name}> / 2)"]
    print(f"f_{name}: first register reads {x}")

assert amps == {"zero": 1, "one": -1, "bal": 0}
print("Deutsch-Jozsa: one query separates constant from balanced, for every n")
