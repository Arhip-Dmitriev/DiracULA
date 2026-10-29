# Copyright 2026 Arkhip A. Dmitriev
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""DiracULA: the Dirac Universal Language for Algorithm, with symbolic qudit count and dimension."""

from typing import Any


def __getattr__(name: str) -> Any:
    """``Program`` and ``ula`` (a shared default Program) from :mod:`diracula.embed`."""
    if name not in ("Program", "Value", "ula"):
        raise AttributeError(f"module 'diracula' has no attribute {name!r}")
    from diracula import embed

    if name == "ula":
        if "ula" not in globals():
            globals()["ula"] = embed.Program()
        return globals()["ula"]
    return getattr(embed, name)
