#!/usr/bin/env python3
"""Differential fuzzer: random arithmetic/control-flow programs run with and without the JIT.

usage: jitfuzz.py [TY] [N] [SEED]

Programs whose output differs are kept in $JITFUZZ_OUT (default: a fresh temp dir);
set KEEP=1 to keep every program.
"""

import random, subprocess, sys, os, tempfile

TY = sys.argv[1] if len(sys.argv) > 1 else 'ty'
N = int(sys.argv[2]) if len(sys.argv) > 2 else 50
SEED0 = int(sys.argv[3]) if len(sys.argv) > 3 else 1
OUT = os.environ.get('JITFUZZ_OUT') or tempfile.mkdtemp(prefix='jitfuzz.')
os.makedirs(OUT, exist_ok=True)

OPS = ['+', '-', '*', '/', '%', '&', '|', '^']
CMPS = ['<', '>', '<=', '>=', '==', '!=']


def expr(r, names, depth):
    if depth <= 0 or r.random() < 0.3:
        k = r.random()
        if k < 0.55:
            return r.choice(names)
        if k < 0.85:
            return str(r.choice([0, 1, 2, 3, 7, 5, 100, 1000, 127, 128, 255]))
        return r.choice(['0.5', '2.0', '1.5', '3.25'])
    k = r.random()
    if k < 0.04:
        return f"(0 - {expr(r, names, depth - 1)})"
    if k < 0.07:
        return f"id({expr(r, names, depth - 1)})"
    if k < 0.08:
        return f"(-{r.choice(names)})"
    if k < 0.09:
        return f"[{expr(r, names, depth - 1)}, 7][0]"
    if k < 0.11:
        return f"({expr(r, names, depth - 1)} {r.choice(['<<', '>>'])} {r.choice(['1', '3', '63', '64', '65', r.choice(names)])})"
    if k < 0.18:
        return f"(({expr(r, names, depth - 1)} {r.choice(CMPS)} {expr(r, names, depth - 1)}) ? {expr(r, names, depth - 1)} : {expr(r, names, depth - 1)})"
    op = r.choice(OPS[:5] if r.random() < 0.8 else OPS)
    return f"({expr(r, names, depth - 1)} {op} {expr(r, names, depth - 1)})"


def stmt(r, names, depth, out, indent):
    pad = ' ' * indent
    k = r.random()
    if k < 0.45:
        v = r.choice(names)
        out.append(f"{pad}{v} = {expr(r, names, 3)}")
    elif k < 0.6:
        v = r.choice(names)
        out.append(f"{pad}{v} {r.choice(['+=', '-=', '*='])} {expr(r, names, 2)}")
    elif k < 0.75 and depth > 0:
        out.append(f"{pad}if {expr(r, names, 2)} {r.choice(CMPS)} {expr(r, names, 2)} {r.choice(['&&', '||'])} {expr(r, names, 1)} {r.choice(CMPS)} {expr(r, names, 1)} {{")
        for _ in range(r.randint(1, 3)):
            stmt(r, names, depth - 1, out, indent + 4)
        out.append(f"{pad}}} else {{")
        for _ in range(r.randint(1, 2)):
            stmt(r, names, depth - 1, out, indent + 4)
        out.append(f"{pad}}}")
    elif k < 0.85 and depth > 0:
        out.append(f"{pad}for i in ..{r.randint(1, 5)} {{")
        for _ in range(r.randint(1, 3)):
            stmt(r, names + ['i'], depth - 1, out, indent + 4)
        out.append(f"{pad}}}")
    else:
        out.append(f"{pad}acc.push({expr(r, names, 3)})")


def program(seed):
    r = random.Random(seed)
    lines = [
        "class V {",
        "    x: Int",
        "    init(x: Int) { self.x = x }",
        "    __str__() -> String { \"V({x})\" }",
        "}",
        "fn +(a: V, b: V) -> V { V(a.x + b.x) }",
        "fn -(a: V, b: V) -> V { V(a.x - b.x) }",
        "fn *(a: V, b: V) -> V { V(a.x * b.x) }",
        "fn +(a: V, b: Int) -> V { V(a.x + b) }",
        "fn *(a: Int, b: V) -> V { V(a * b.x) }",
        "fn id(v: _) -> _ { v }",
        "fn <(a: V, b: V) -> Bool { a.x < b.x }",
        "fn ==(a: V, b: V) -> Bool { a.x == b.x }",
        "",
    ]
    nfn = r.randint(2, 5)
    for f in range(nfn):
        names = ['a', 'b', 'c', 'x', 'y']
        lines.append(f"fn f{f}(a: _, b: _, c: _) -> _ {{")
        lines.append("    let acc: Array[_] = []")
        lines.append("    let x: _ = a")
        lines.append("    let y: _ = 0")
        body = []
        for _ in range(r.randint(3, 9)):
            stmt(r, names, 2, body, 4)
        lines += body
        lines.append("    acc.push(x)")
        lines.append("    acc.push(y)")
        lines.append("    acc")
        lines.append("}")
        lines.append("")
    pools = [
        "[0, 1, 2, 3, 5, 7, 11, -3, -8, 100, 255, 1000]",
        "[0, 1, 2, 3, 5, 7, 11, -3, -8, 100, 0.5, -2.25]",
        "[1, 2, 3, 0.5, V(2), V(-1), 7]",
        "[1, 2, nil, \"s\", 3, 4.5]",
        "[0.5, -2.25, 0.0, 3.0, 1e300, -0.0, 7.75, 100.0]",
        "[0.5, -2.25, 3.0, 7.75, 100.0, 1.0, 2.0]",
    ]
    lines.append(f"let pool: Array[_] = {pools[r.randint(0, 5) if r.random() < 0.7 else 0]}")
    lines.append("let n = 0")
    lines.append("for round in ..60 {")
    lines.append("    for k in ..4 {")
    lines.append("        let a: _ = pool[(round * 7 + k) % #pool]")
    lines.append("        let b: _ = pool[(round * 3 + k * 5 + 1) % #pool]")
    lines.append("        let c: _ = pool[(round + k * 11 + 2) % #pool]")
    for f in range(nfn):
        lines.append(f"        try {{ print(f{f}(a, b, c)) }} catch e {{ print(\"err {{type(e)}}\") }}")
    lines.append("    }")
    lines.append("}")
    return "\n".join(lines) + "\n"


bad = 0
for seed in range(SEED0, SEED0 + N):
    src = program(seed)
    path = f"{OUT}/p{seed}.ty"
    with open(path, "w") as f:
        f.write(src)
    try:
        a = subprocess.run([TY, "-j", path], capture_output=True, text=True, timeout=60)
        b = subprocess.run([TY, path], capture_output=True, text=True, timeout=60)
    except subprocess.TimeoutExpired:
        print(f"seed {seed}: timeout")
        bad += 1
        continue
    if a.returncode != 0 and "CompileError" in a.stderr:
        os.remove(path)
        continue
    if a.stdout != b.stdout or a.returncode != b.returncode:
        bad += 1
        al, bl = a.stdout.splitlines(), b.stdout.splitlines()
        first = next((i for i in range(min(len(al), len(bl))) if al[i] != bl[i]), min(len(al), len(bl)))
        print(f"seed {seed}: MISMATCH rc {a.returncode}/{b.returncode} at line {first}: "
              f"interp={al[first] if first < len(al) else '<eof>'!r} jit={bl[first] if first < len(bl) else '<eof>'!r}"
              f" {b.stderr.strip()[:200]!r}")
    elif not os.environ.get('KEEP'):
        os.remove(path)
print(f"{bad} mismatches in {N} programs")
if bad or os.environ.get('KEEP'):
    print(f"programs kept in {OUT}")
elif not os.environ.get('JITFUZZ_OUT'):
    os.rmdir(OUT)
sys.exit(1 if bad else 0)
