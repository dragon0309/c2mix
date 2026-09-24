"""Component C: driving clang-18 and opt-18 (spec §5.3).

The flags live here, in the core, and no target can change them — that is what makes
every target go through the same frontend (§4.1). The pipeline is

    clang -S -emit-llvm  (one call per source file)
    llvm-link -S
    opt -passes=mem2reg

`-disable-O0-optnone` is what lets mem2reg run at all (LF1) and `-fwrapv` is what keeps
`nsw` out of the result (LF2); both are checked by A3.0.
"""
from __future__ import annotations

import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

CFLAGS = ("-O0", "-Xclang", "-disable-O0-optnone", "-fwrapv", "-fno-strict-aliasing", "-g")
NATIVE_FLAGS = ("-fwrapv", "-fno-strict-aliasing")


class ToolchainError(Exception):
    pass


@dataclass
class Result:
    argv: list[str]
    returncode: int
    stdout: str
    stderr: str


@dataclass
class Toolchain:
    clang: str = "clang-18"
    opt: str = "opt-18"
    llvm_as: str = "llvm-as-18"
    llvm_diff: str = "llvm-diff-18"
    llvm_link: str = "llvm-link-18"

    @classmethod
    def from_config(cls, cfg) -> "Toolchain":
        t = (cfg.data.get("toolchain") or {}) if cfg else {}
        return cls(**{f: t[f] for f in ("clang", "opt", "llvm_as", "llvm_diff", "llvm_link")
                      if f in t})

    def missing(self) -> list[str]:
        return [t for t in (self.clang, self.opt, self.llvm_as, self.llvm_diff, self.llvm_link)
                if shutil.which(t) is None]

    def version(self) -> str:
        return self.run([self.clang, "--version"]).stdout.splitlines()[0].strip()

    # ------------------------------------------------------------------ running
    def run(self, argv: list[str], check: bool = True) -> Result:
        p = subprocess.run(argv, capture_output=True, text=True)
        r = Result(argv, p.returncode, p.stdout, p.stderr)
        if check and p.returncode != 0:
            raise ToolchainError(f"{' '.join(argv)}\n{p.stderr.strip()}")
        return r

    # ------------------------------------------------------------------ steps
    def compile_unit(self, src: Path, out: Path, includes: tuple[Path, ...] = ()) -> Path:
        argv = [self.clang, *CFLAGS]
        for inc in includes:
            argv += ["-I", str(inc)]
        argv += ["-S", "-emit-llvm", str(src), "-o", str(out)]
        self.run(argv)
        return out

    def link(self, units: list[Path], out: Path) -> Path:
        if len(units) == 1:
            out.write_text(units[0].read_text())
            return out
        self.run([self.llvm_link, "-S", *map(str, units), "-o", str(out)])
        return out

    def mem2reg(self, ll: Path, out: Path) -> Path:
        self.run([self.opt, "-passes=mem2reg", "-S", str(ll), "-o", str(out)])
        return out

    def strip_debug(self, ll: Path, out: Path) -> Path:
        self.run([self.opt, "-strip-debug", "-S", str(ll), "-o", str(out)])
        return out

    def assemble(self, ll: Path, out: Path) -> Result:
        """llvm-as: does the LLVM parser accept what we printed (A3.2)?"""
        return self.run([self.llvm_as, str(ll), "-o", str(out)], check=False)

    def diff(self, a: Path, b: Path) -> Result:
        """llvm-diff: empty output means the two modules agree (A3.2)."""
        return self.run([self.llvm_diff, str(a), str(b)], check=False)

    # ------------------------------------------------------------------ pipeline
    def build_ir(self, sources: list[Path], out_dir: Path,
                 includes: tuple[Path, ...] = ()) -> Path:
        """Sources -> program.m2r.ll (§5.3). One clang call per file: clang refuses
        several inputs together with -o."""
        out_dir.mkdir(parents=True, exist_ok=True)
        units = []
        for i, src in enumerate(sources):
            unit = out_dir / f"{i:02d}_{Path(src).stem}.ll"
            units.append(self.compile_unit(Path(src), unit, includes))
        linked = self.link(units, out_dir / "program.ll")
        return self.mem2reg(linked, out_dir / "program.m2r.ll")

    def build_native(self, ll: Path, extra: list[Path], out: Path,
                     includes: tuple[Path, ...] = (), opt: str = "-O0") -> Path:
        """G2's native binary, built from the *same* program.m2r.ll the executor reads.
        G2 also builds it at -O2 to see whether the program depends on UB."""
        argv = [self.clang, opt, *NATIVE_FLAGS]
        for inc in includes:
            argv += ["-I", str(inc)]
        argv += [str(ll), *map(str, extra), "-o", str(out)]
        self.run(argv)
        return out
