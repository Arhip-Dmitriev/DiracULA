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

"""Unit tests for :mod:`diracula.shell`: run_line, scripts, the IO loop and main."""

from __future__ import annotations

import io
from pathlib import Path

import pytest

from diracula import shell as S
from diracula.shell import Shell, main

REPO = Path(__file__).resolve().parent.parent


def listing(text: str) -> bool:
    return any(ln.lstrip().startswith("graph:") for ln in text.splitlines())


class FakeStdin(io.StringIO):
    """A StringIO whose readline raises queued exceptions before reading."""

    def __init__(self, text: str, raises: list[BaseException], tty: bool = False) -> None:
        super().__init__(text)
        self.raises = list(raises)
        self.tty = tty

    def readline(self, size: int | None = -1) -> str:  # type: ignore[override]
        if self.raises:
            raise self.raises.pop(0)
        return super().readline()

    def isatty(self) -> bool:
        return self.tty


class BrokenStdout(io.StringIO):
    def write(self, text: str) -> int:
        raise OSError("closed")


# -- construction --------------------------------------------------------------------------


# -- run_line ------------------------------------------------------------------------------


# -- scripts -------------------------------------------------------------------------------


# -- loop ----------------------------------------------------------------------------------


# -- main ----------------------------------------------------------------------------------


class TestVerboseMode:
    def test_echoes_the_last_statement(self) -> None:
        shell = Shell(display="ascii", verbose=True)
        assert shell.run_line("var n") == "val n : nat"
        assert shell.run_line("var a = 1; var b = 2") == "val b : nat = 2"
        assert shell.run_line("|p> = X|0>") == "val |p> : ket = |1>"
        assert shell.run_line("<p|p>") == "- : nat = 1"
        assert shell.run_line("seed 1") == ""

    def test_toggle(self) -> None:
        shell = Shell(display="ascii")
        assert shell.run_line("var n") == ""
        assert shell.run_line(":verbose_on") == "verbose: on"
        assert shell.run_line("var m") == "val m : nat"
        assert shell.run_line(":verbose_off") == "verbose: off"
        assert shell.run_line("var k") == ""

    def test_show_still_prints_with_the_echo_off(self) -> None:
        shell = Shell(display="ascii", verbose=True)
        assert shell.run_line("show(1 + 1)") == "1 + 1 = 2"

    def test_mode_drives_the_echo(self) -> None:
        shell = Shell(display="ascii", verbose=True)
        shell.run_line(":zx")
        out = shell.run_line("|p> = |1>").splitlines()
        assert out[0] == "val |p> : ket =" and out[1].startswith("  graph:")

    def test_colour_codes(self) -> None:
        shell = Shell(display="ascii", verbose=True, color=True)
        assert shell.run_line("var n") == "\x1b[1mval\x1b[0m n : \x1b[36mnat\x1b[0m"

    def test_bar_shape(self) -> None:
        bar = Shell().bar(60)
        assert len(bar) == 60 and bar.startswith("─( ") and "< command 1 >" in bar
        assert bar.endswith(f"{{ {S._place()} }}─")

    def test_tty_prints_the_bar_before_each_prompt(self) -> None:
        stdout = io.StringIO()
        Shell(verbose=True, display="ascii").loop(FakeStdin("var n\n", [], tty=True), stdout)
        text = stdout.getvalue()
        assert text.count("< command 1 >") == 1 and text.count("< command 2 >") == 1
        assert "val n : nat\n" in text


class TestPrompt:
    def test_counts_lines(self) -> None:
        shell = Shell(display="ascii")
        name = S._place()
        assert shell.prompt() == f"{name}(1): "
        shell.run_line("var n")
        shell.run_line("")
        assert shell.prompt() == f"{name}(2): "
        assert shell.prompt(True) == f"{'.' * len(name)}(2): "

    def test_place(self, tmp_path, monkeypatch) -> None:  # type: ignore[no-untyped-def]
        monkeypatch.chdir(tmp_path)
        assert S._place() == tmp_path.name
        monkeypatch.setenv("HOME", str(tmp_path))
        assert S._place() == "home"


class TestElse:
    def test_else_on_the_next_line(self) -> None:
        shell = Shell(display="ascii")
        lines = ["var t = 0", "if t == 1 { print(1) }", "else { print(2) }"]
        assert shell.run_script(lines) == ["", "", "2"]

    def test_blank_lines_before_else_in_a_script(self) -> None:
        shell = Shell(display="ascii")
        assert shell.run_script("if 1 == 0 { print(1) }\n\n# c\nelse { print(2) }") == ["", "2"]

    def test_a_closed_if_runs_at_the_next_other_line(self) -> None:
        shell = Shell(display="ascii")
        assert shell.run_line("if 1 == 1 { print(1) }") == ""
        assert shell.run_line("print(2)") == "1\n2"

    def test_a_blank_line_runs_a_closed_if(self) -> None:
        shell = Shell(display="ascii")
        assert shell.run_line("if 1 == 1 { print(1) }") == ""
        assert shell.run_line("") == "1"

    def test_a_closed_if_runs_at_the_end_of_a_script(self) -> None:
        assert Shell(display="ascii").run_script(["if 1 == 1 { print(1) }"]) == ["", "1"]

    def test_header_brace_on_the_next_line(self) -> None:
        assert Shell(display="ascii").run_script(["if 1 == 1", "{ print(1) }"]) == ["", "", "1"]


class TestConfig:
    def test_show_set_and_reset(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(S.T, "CONFIG", S.T.Config())
        shell = Shell(display="ascii")
        assert shell.run_line(":config").startswith("size = 1\ncolor = auto\nfile: ")
        assert shell.run_line(":config size 1.5").startswith("size = 1.5\n")
        assert shell.run_line(":config color #ff8800").splitlines()[1] == "color = #ff8800"
        assert shell.run_line(":config size huge").startswith("error: size must be a number")
        assert shell.run_line(":config shade red").startswith("error: unknown setting")
        assert shell.run_line(":config reset").startswith("size = 1\ncolor = auto")
        assert shell.errors == 2

    def test_save_and_load(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(S.T, "CONFIG", S.T.Config())
        monkeypatch.setenv("XDG_CONFIG_HOME", str(tmp_path))
        shell = Shell(display="ascii")
        shell.run_line(":config size 2")
        assert shell.run_line(":config save") == f"saved {tmp_path}/diracula/config.toml"
        loaded = S.T.load_config()
        assert loaded.size == 2.0 and loaded.color == "auto"

    def test_bad_file(self, tmp_path: Path) -> None:
        path = tmp_path / "config.toml"
        path.write_text("size = -1\n", encoding="utf-8")
        with pytest.raises(ValueError):
            S.T.load_config(str(path))
        assert S.T.load_config(str(tmp_path / "none.toml")) == S.T.Config()


class TestStyles:
    def test_several_styles_print_each_in_order(self) -> None:
        shell = Shell(styles=("unicode", "latex", "ascii"))
        out = shell.run_line("|s> = H|0>; show(|s>)").splitlines()
        assert out[0].startswith("|s⟩ =") and out[1].startswith("$|s\\rangle")
        assert out[2].startswith("|s> =")

    def test_shared_text_once(self) -> None:
        shell = Shell(styles=("unicode", "ascii"))
        assert shell.run_line('print("hi")') == "hi"

    def test_order_holds_until_error_and_finish(self) -> None:
        shell = Shell(styles=("unicode", "ascii"), order=True)
        assert shell.run_line("|s> = |1>; show(|s>)") == ""
        assert shell.run_line('print("x")') == ""
        flushed = shell.run_line("show(|q>)").splitlines()
        assert flushed == [
            "── unicode ──",
            "|s⟩ = |1⟩",
            "x",
            "── ascii ──",
            "|s> = |1>",
            "x",
            "error: 'q' is not defined; declare it with var",
        ]
        shell.run_line("show(|s>)")
        assert shell.finish().splitlines() == [
            "── unicode ──",
            "|s⟩ = |1⟩",
            "── ascii ──",
            "|s> = |1>",
        ]
        assert shell.finish() == ""

    def test_style_word(self) -> None:
        shell = Shell(display="ascii")
        assert shell.run_line(":style latex render") == "style: latex render"
        assert shell.interpreter.styles == ("latex", "plot")
        assert shell.run_line(":style fancy").startswith("error: unknown style")

    def test_errors_are_red_with_colour(self) -> None:
        shell = Shell(display="ascii", color=True)
        assert shell.run_line("show(|q>)").startswith("\x1b[31merror:")
        assert Shell(display="ascii").run_line("show(|q>)").startswith("error:")

    def test_partial_output_before_an_error(self) -> None:
        shell = Shell(display="ascii")
        out = shell.run_line("|s> = |1>; show(|s>); show(|q>)").splitlines()
        assert out[0] == "|s> = |1>" and out[1].startswith("error:")


class TestFlags:
    @pytest.mark.parametrize("flag", ["-v", "-h"])
    def test_short_flags_are_gone(self, flag: str, capsys: pytest.CaptureFixture[str]) -> None:
        assert main([flag, "-c", "var n"]) == 2

    def test_latex_and_order_flags(self, capsys: pytest.CaptureFixture[str]) -> None:
        assert main(["--latex", "--ascii", "--order", "-c", "|s> = |1>", "-c", "show(|s>)"]) == 0
        assert capsys.readouterr().out.splitlines() == [
            "── latex ──",
            "$|s\\rangle = |1\\rangle$",
            "── ascii ──",
            "|s> = |1>",
        ]

    def test_verbose_long_flag(self, capsys: pytest.CaptureFixture[str]) -> None:
        assert main(["--verbose", "--ascii", "-c", "var x = 3"]) == 0
        assert "val x : nat = 3" in capsys.readouterr().out
