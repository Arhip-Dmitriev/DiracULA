# DiracULA

**Develop quantum algorithms without fixing the size or dimensionality of the machine.** Write an
algorithm once, in Dirac notation, for `n` qudits of dimension `d`, and get its states,
measurement statistics and identities as closed forms that hold for every `n` and every `d` at
once.

[![PyPI](https://img.shields.io/pypi/v/DiracULA.svg)](https://pypi.org/project/DiracULA/)
[![Python 3.12+](https://img.shields.io/badge/python-3.12%2B-blue.svg)](https://www.python.org/downloads/)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/LICENSE)
[![Results certified in Lean 4](https://img.shields.io/badge/certificates-Lean%204-purple.svg)](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/LEAN.txt)
[![Status: beta](https://img.shields.io/badge/status-beta-orange.svg)](https://github.com/Arhip-Dmitriev/DiracULA#status)

DiracULA, the Dirac Universal Language for Algorithm, is a programming language for quantum
algorithms whose register size and qudit dimension are symbols. Its values are symbolic path
sums: applying a gate is substitution, and measurement is a Born distribution derived in closed
form. Nothing is ever enumerated, sampled or simulated, so every result has the same shape for
every size.

## Example: Deutsch–Jozsa for every `n`

[`examples/deutsch_jozsa.ula`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/examples/deutsch_jozsa.ula),
a balanced oracle on an `n`-qubit register, with `n` never given a value:

```text
var n
gate U_f = |x>|y> -> |x>|y xor bit(x, 0)>
|psi> = |0>^@n @ |1>
show(|psi>)
(H^@n @ H)|psi>
show(|psi>)
U_f|psi>
show(|psi>)
(H^@n @ I)|psi>
show(|psi>)
var z = floor(measure|psi>/2)
show(z)
show(|psi>)
```

```console
$ diracula --unicode examples/deutsch_jozsa.ula
|ψ⟩ = |0⟩^⊗n ⊗ |1⟩
|ψ⟩ = 2^(-n/2 - 1/2) Σ_{y=0}^{1} Σ_{x=0}^{2^n - 1} (-1)^y |x⟩ ⊗ |y⟩
|ψ⟩ = 2^(-n/2 - 1/2) Σ_{y=0}^{1} Σ_{x=0}^{2^n - 1} (-1)^y |x⟩ ⊗ |(y ⊕ bit(x, 0))⟩
|ψ⟩ = 2^(-n - 1/2) Σ_{y=0}^{1} Σ_{x=0}^{2^n - 1} Σ_{x'=0}^{2^n - 1} (-1)^(y + x⊙x') |x'⟩ ⊗ |(y ⊕ bit(x, 0))⟩
z = [(1, 1)]
|ψ⟩⟨ψ| = 1/2 Σ_{k1=0}^{1} |1⟩⟨1| ⊗ |k1⟩⟨k1|
```

The measurement is a Born distribution derived symbolically: outcome `1` with probability `1`,
so the oracle is balanced, for every register size. The post-measurement state is the mixed
state on the last line. Any state can also be drawn as a ZX diagram (`--zx`), where the
register is a bang box of multiplicity `n - 1` rather than `n` copies:

<p align="center">
  <img src="https://raw.githubusercontent.com/Arhip-Dmitriev/DiracULA/main/docs/images/deutsch_jozsa_zx.png" alt="ZX diagram of the Deutsch–Jozsa state before measurement, with the register as a bang box of multiplicity n - 1" width="640">
</p>

## What it does

- **Symbolic size.** Register count, qudit dimension and loop bounds can stay symbols.
  `|0>^@n` is one term, not `n` kets, and a concrete value is substituted into the closed form
  at the end at no cost in its size.
- **Exact arithmetic.** Amplitudes are exact expressions over rationals, roots of unity and the
  size symbols; no global factor is ever dropped.
- **Closed-form measurement.** `measure` returns the Born distribution over every outcome as one
  expression, together with the post-measurement state, mixed where it has to be.
- **Certified results.** `certify` writes a Lean 4 file proving that the value the program
  computes equals the printed closed form, for every value of its size symbols.
- **A whole language.** Variables, gates defined by their action on basis kets, sums, matrix
  comprehensions, measurement, control flow, assumptions and assertions, and f-strings; run as
  scripts or interactively, and embeddable in Python and Jupyter.

## Install

Python ≥ 3.12. The runtime dependencies are `numpy`, `sympy` and the
[ArchytasZX](https://github.com/Arhip-Dmitriev/ArchytasZX) ZX engine. With `matplotlib`
installed, output is typeset and ZX diagrams are drawn as images in terminals that show them;
without it, both fall back to Unicode text.

```bash
pip install DiracULA             # or 'DiracULA[viz]' to add matplotlib
diracula                         # interactive shell
diracula script.ula              # run a program
```

## Quickstart

### The `.ula` language

```text
var n
gate F = |x>_d -> 1/sqrt(d) sum(y in 0..d){ e^(2*pi*i*x*y/d) |y>_d }
|psi> = H^@n |0>^@n
var z = measure|psi>
show(z, |psi>)
print(f"z = {z}")
```

Output styles are `--render` (default, typeset images), `--unicode`, `--ascii` and `--latex`;
several style flags print every output in each style, and `--order` groups the output by style
at the end. `--zx`, `--both` and `--raw` switch between Dirac notation and ZX diagrams, and
`--images DIR` saves every rendered image as a PNG.

[`examples/learn_ula.ula`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/examples/learn_ula.ula)
is a guided tour of the whole language, ending in Deutsch–Jozsa for every `n`; the complete
reference is [`docs/LANGUAGE.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/LANGUAGE.txt).

### From Python

```python
from diracula import ula                 # a shared Program; diracula.Program() for a fresh one

ula("var n")
ula.psi = ula.H ** ula.n | ula.ket(0) ** ula.n      # |psi> = H^@n |0>^@n
ula["|phi>"] = ula["|psi> - 2 |0><0|psi>"]
ula.phi       # |φ⟩ = 2^(-n/2) Σ_{x=0}^{2^n - 1} |x⟩ - 2^(1 - n/2) |0⟩^⊗n
ula.phi.latex()                          # also rendered by Jupyter

y = ula.measure | ula.psi
y             # [(k, 2^(-n)) : k ∈ {0,…,2^n - 1}]
```

[`examples/learn_ula.py`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/examples/learn_ula.py)
is the same tour from Python.

### Certifying a result

```text
var n
|psi> = H^@n |0>^@n
certify psi
```

```console
$ diracula --certify out/ program.ula
lean: wrote out/program_psi.lean (0 axioms: none)
```

The file states the program's meaning, built from its syntax, and proves it equal to the printed
closed form for every `n`, using a verified normaliser of symbolic sums. `#print axioms` lists
only Lean's standard axioms. Assumptions made with `assume` become hypotheses of the theorem.

## Documentation

The full reference documentation is in [`docs/`](https://github.com/Arhip-Dmitriev/DiracULA/tree/main/docs):

| Document | Contents |
|---|---|
| [`INDEX.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/INDEX.txt) | Index of the documentation, conventions and reading order |
| [`OVERVIEW.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/OVERVIEW.txt) | What the language is, its guarantees and its limits |
| [`INSTALL.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/INSTALL.txt) | Installation, the Lean library, configuration and environment variables |
| [`LANGUAGE.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/LANGUAGE.txt) | The `.ula` language reference |
| [`SHELL.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/SHELL.txt) | The `diracula` command: flags, views, styles, meta-commands, exit codes |
| [`PYTHON_API.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/PYTHON_API.txt) | The Python embedding |
| [`ZX_VIEW.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/ZX_VIEW.txt) | How states become ZX diagrams and how they are drawn |
| [`LEAN.txt`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/docs/LEAN.txt) | Certificates: the Lean semantics of programs and the symbolic-sum normaliser |

## How it relates to ArchytasZX

DiracULA computes on its own symbolic path-sum core. It uses
[ArchytasZX](https://github.com/Arhip-Dmitriev/ArchytasZX), a qufinite ZXW diagram-rewriting
engine, for three things: drawing states as ZX diagrams, the Lean library against which
certificates are checked, and the engine commands available in the shell after `:`. A ZX
diagram is only a view of a DiracULA state; no result is computed through it.

## Status

In **beta and under active development**: the language and the API are unstable and change
between releases. Known limits:

- An `assert` whose condition does not reduce to a truth value counts as undecided, and fails.
- Programs using `rand`, a branch on a value that is not concrete, `normalise`, floating-point
  format specs or states assigned from Python cannot be certified; nor can results that need an
  identity the normaliser does not prove yet.
- An amplitude outside the ZX scalar and phase grammar, such as `cos(t)` of a real symbol, has no
  ZX view.

## Development

```bash
git clone https://github.com/Arhip-Dmitriev/DiracULA.git
cd DiracULA
python -m venv .venv && source .venv/bin/activate
pip install -e '.[dev]'

ruff format . && ruff check . && mypy diracula
```

## Citation

If you use DiracULA in academic work, please cite it via
[`CITATION.cff`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/CITATION.cff), or:

```bibtex
@software{dmitriev_diracula,
  author  = {Dmitriev, Arkhip Alekseyevich},
  title   = {{DiracULA}: Dirac Universal Language for Algorithm},
  year    = {2026},
  url     = {https://github.com/Arhip-Dmitriev/DiracULA},
  license = {Apache-2.0}
}
```

## Contributing

Bug reports, wrong closed forms and questions about the mathematics are the most useful
contributions; a program whose printed result is wrong for some size is the most valuable
report of all. See
[`CONTRIBUTING.md`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/CONTRIBUTING.md).

## References

<details>
<summary>Full reference list</summary>

**Dirac notation and quantum foundations**
- Dirac, *A new notation for quantum mechanics*, Math. Proc. Camb. Phil. Soc. 35 (1939) —
  [doi:10.1017/S0305004100021162](https://doi.org/10.1017/S0305004100021162)
- Born, *Zur Quantenmechanik der Stoßvorgänge*, Z. Phys. 37 (1926), the Born rule —
  [doi:10.1007/BF01397477](https://doi.org/10.1007/BF01397477)
- Nielsen & Chuang, *Quantum Computation and Quantum Information* (2010), density matrices,
  measurement, the quantum Fourier transform —
  [doi:10.1017/CBO9780511976667](https://doi.org/10.1017/CBO9780511976667)
- Gottesman, *Fault-tolerant quantum computation with higher-dimensional systems* (1999), qudits —
  [arXiv:quant-ph/9802007](https://arxiv.org/abs/quant-ph/9802007)

**Path sums and exact symbolic sums**
- Amy, *Towards large-scale functional verification of universal quantum circuits*, EPTCS 287
  (2019) — [arXiv:1805.06908](https://arxiv.org/abs/1805.06908)
- Vilmart, *The structure of sum-over-paths, its consequences, and completeness for Clifford*,
  FoSSaCS 2021 — [arXiv:2003.05678](https://arxiv.org/abs/2003.05678)
- Berndt, Evans & Williams, *Gauss and Jacobi Sums* (1998), quadratic Gauss sums and their sign
- Richardson, *Some undecidable problems involving elementary functions of a real variable*,
  J. Symb. Logic 33 (1968) — [doi:10.2307/2271358](https://doi.org/10.2307/2271358)

**ZX view**
- Wang, *Qufinite ZX-calculus: a unified framework of qudit ZX-calculi* —
  [arXiv:2104.06429](https://arxiv.org/abs/2104.06429)
- Carette & Lemonnier, *Large-scale quantum diagrammatic reasoning tools, !-boxes vs. scalable
  notations* — [arXiv:2204.11702](https://arxiv.org/abs/2204.11702)

**Lean formalisation**
- de Moura & Ullrich, *The Lean 4 theorem prover and programming language*, CADE-28 (2021) —
  [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37)
- The mathlib Community, *The Lean mathematical library*, CPP 2020 —
  [arXiv:1910.09336](https://arxiv.org/abs/1910.09336)

**Algorithms in the examples**
- Deutsch & Jozsa, *Rapid solution of problems by quantum computation*, Proc. R. Soc. A 439 (1992) —
  [doi:10.1098/rspa.1992.0167](https://doi.org/10.1098/rspa.1992.0167)
- Grover, *A fast quantum mechanical algorithm for database search*, STOC 1996 —
  [arXiv:quant-ph/9605043](https://arxiv.org/abs/quant-ph/9605043)
- Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum
  computer*, SIAM J. Comput. 26 (1997) — [arXiv:quant-ph/9508027](https://arxiv.org/abs/quant-ph/9508027)
- Coppersmith, *An approximate Fourier transform useful in quantum factoring* (1994) —
  [arXiv:quant-ph/0201067](https://arxiv.org/abs/quant-ph/0201067)

**Software**
- Meurer et al., *SymPy*, PeerJ Comput. Sci. 3 (2017) — [doi:10.7717/peerj-cs.103](https://doi.org/10.7717/peerj-cs.103)
- Harris et al., *Array programming with NumPy*, Nature 585 (2020) —
  [doi:10.1038/s41586-020-2649-2](https://doi.org/10.1038/s41586-020-2649-2)

**Verification of quantum programs and related tools**
- Chareton, Bardin, Bobot, Perrelle & Valiron, *An automated deductive verification framework for
  circuit-building quantum programs* (QBricks), ESOP 2021 — [arXiv:2003.05841](https://arxiv.org/abs/2003.05841)
- Hietala, Rand, Hung, Li & Hicks, *Proving quantum programs correct* (SQIR), ITP 2021 —
  [arXiv:2010.01240](https://arxiv.org/abs/2010.01240)
- Xu, Barthe & Zhou, *Automating equational proofs in Dirac notation* (DiracDec), POPL 2025 —
  [arXiv:2411.11617](https://arxiv.org/abs/2411.11617)
- Xu, Zhou & Barthe, *D-Hammer: efficient equational reasoning for labelled Dirac notation*,
  CAV 2025 — [arXiv:2505.08633](https://arxiv.org/abs/2505.08633)
- Chareton, Bardin, Lee, Valiron, Vilmart & Xu, *Formal methods for quantum programs: a survey* —
  [arXiv:2109.06493](https://arxiv.org/abs/2109.06493)

</details>

## License

Apache License 2.0 — see
[`LICENSE`](https://github.com/Arhip-Dmitriev/DiracULA/blob/main/LICENSE).

<!--
Copyright 2026 Arkhip A. Dmitriev
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->
