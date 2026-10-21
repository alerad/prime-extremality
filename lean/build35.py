#!/usr/bin/env python3
"""Compile RntPaper (and the extracted QProduct sources) with Lean v4.35 against the
built ~/research/leancert checkout, in dependency order and in parallel.

No Lake: LEAN_PATH comes from leancert's `lake env`; local modules are compiled into
$OUT (default .lake/check35). Modules outside the local roots (Mathlib, LeanCert,
PrimeNumberTheoremAnd) must already be built and on LEAN_PATH.

usage: ./build35.py [Module ...]      (default: RntPaper and its local closure)
Up-to-date modules (olean newer than source and local deps) are skipped; FORCE=1 rebuilds.
env:   LEANCERT, QPRODUCT, PNT_BUILD, OUT, JOBS
"""
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait

HERE = os.path.dirname(os.path.abspath(__file__))
HOME = os.path.expanduser("~")
LEANCERT = os.environ.get("LEANCERT", f"{HOME}/research/leancert")
QPRODUCT = os.environ.get("QPRODUCT", f"{HOME}/research/formalizations/leancert-qproduct")
OUT = os.environ.get("OUT", f"{HERE}/.lake/check35")
JOBS = int(os.environ.get("JOBS", os.cpu_count() or 4))
LEAN = f"{HOME}/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
ROOTS = {"RntPaper": HERE, "QProduct": QPRODUCT}


def src(mod):
    top = mod.split(".")[0]
    if top not in ROOTS:
        return None
    path = os.path.join(ROOTS[top], *mod.split(".")) + ".lean"
    return path if os.path.exists(path) else None


def imports(path):
    text = open(path, encoding="utf-8").read()
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    out = []
    for line in text.splitlines():
        if not line.strip():
            continue
        m = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", line)
        if m:
            out.append(m.group(1))
        elif not line.strip().startswith(("module", "prelude")):
            break
    return out


def closure(targets):
    deps, todo = {}, list(targets)
    while todo:
        m = todo.pop()
        if m in deps:
            continue
        p = src(m)
        if p is None:
            continue
        deps[m] = [d for d in imports(p) if src(d)]
        todo += deps[m]
    return deps


def main():
    targets = sys.argv[1:] or ["RntPaper"]
    lc = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEANCERT,
                        capture_output=True, text=True,
                        env={**os.environ, "PATH": f"{HOME}/.elan/bin:" + os.environ["PATH"]}).stdout.strip()
    extra = os.environ.get("PNT_BUILD", "")
    env = {**os.environ, "LEAN_PATH": ":".join(x for x in [lc, OUT, extra] if x)}
    deps = closure(targets)
    done, failed, running = set(), set(), {}
    status = 0
    with ThreadPoolExecutor(JOBS) as ex:
        while len(done) + len(failed) < len(deps):
            progress = False
            for m, ds in deps.items():
                if m in done or m in failed or m in running:
                    continue
                if any(d in failed for d in ds):
                    failed.add(m); print(f"-- skip {m} (dependency failed)", flush=True); continue
                if all(d in done for d in ds):
                    rel = m.replace(".", "/")
                    ol = f"{OUT}/{rel}.olean"
                    if os.path.exists(ol) and not os.environ.get("FORCE"):
                        t = os.path.getmtime(ol)
                        if t >= os.path.getmtime(src(m)) and all(
                                t >= os.path.getmtime(f"{OUT}/{d.replace('.', '/')}.olean") for d in ds):
                            done.add(m)
                            progress = True
                            continue
                    os.makedirs(os.path.dirname(f"{OUT}/{rel}"), exist_ok=True)
                    cmd = [LEAN, "-o", f"{OUT}/{rel}.olean", "-i", f"{OUT}/{rel}.ilean", src(m)]
                    running[m] = ex.submit(subprocess.run, cmd, env=env, capture_output=True, text=True,
                                              cwd=ROOTS[m.split(".")[0]])
            if not running:
                if progress:
                    continue
                break
            fin, _ = wait(running.values(), return_when=FIRST_COMPLETED)
            for m, fut in list(running.items()):
                if fut in fin:
                    r = fut.result()
                    del running[m]
                    msg = (r.stdout + r.stderr).strip()
                    if r.returncode == 0:
                        done.add(m)
                        warn = sum(1 for l in msg.splitlines() if ": warning:" in l)
                        print(f"ok   {m}" + (f"  ({warn} warnings)" if warn else ""), flush=True)
                        if os.environ.get("VERBOSE") and msg:
                            print(msg, flush=True)
                    else:
                        failed.add(m); status = 1
                        print(f"FAIL {m}\n{msg[:6000]}", flush=True)
    sys.exit(status)


if __name__ == "__main__":
    main()
