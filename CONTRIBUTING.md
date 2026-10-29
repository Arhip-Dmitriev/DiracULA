# Contributing to DiracULA

DiracULA is a research prototype under active development. The language and the API are
unstable and the internals move quickly, so the most useful contributions right now are bug
reports, wrong results, and questions/concerns about the mathematics.

**Please send bug reports rather than code.** Unsolicited patches are hard to take at this
stage. A precise report of something the language gets wrong is worth far more than a pull
request, and will be acted on faster.

## Reporting a wrong result

A printed closed form that is wrong for some value of its size symbols is the most serious
kind of defect this project can have, and the most valuable thing to report. The best report
is a short `.ula` program together with the value of `n` or `d` at which the printed result
disagrees with a hand calculation:

```text
var n
|psi> = H^@n |0>^@n
show(|psi>)          # expected ..., got ... at n = 3
```

Please include the full output, the command line you used, and the DiracULA version.

## Conventions

- **Nothing is simulated.** Results come from symbolic rewriting of path sums and closed-form
  summation; no state is expanded into an amplitude vector to produce a result.
- **Amplitudes are never silently discarded.** Every global factor is kept exactly.
- **DiracULA is self-contained.** It imports no other project's code.
- **Determinism.** Printed output must not depend on hash order or the wall clock.
- Docstrings are brief and describe either *what* a function is or *how* it works.
- Every source file carries the Apache 2.0 header.

## License

By contributing you agree that your contributions are licensed under the Apache License 2.0,
the same terms that cover the project.

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
