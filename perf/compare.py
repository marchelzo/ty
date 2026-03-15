#!/usr/bin/env python3
"""
Head-to-head comparison: ty vs Python.

Runs both suites (or reads cached results) and prints a side-by-side table.

Usage:
    python3 perf/compare.py              # run both, compare
    python3 perf/compare.py -f nbody     # filter to one benchmark
    python3 perf/compare.py --cached     # use last saved results (no re-run)
    python3 perf/compare.py -n 7         # 7 rounds each
"""

import argparse
import json
import math
import os
import subprocess
import sys
import time

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.dirname(SCRIPT_DIR)

TY_RESULTS = os.path.join(SCRIPT_DIR, 'results.json')
PY_RESULTS = os.path.join(SCRIPT_DIR, 'results_py.json')

# Name mapping: ty benchmark names -> python benchmark names
# (ty uses camelCase in results, python uses snake_case display names)
TY_TO_DISPLAY = {
    'chaosGame':    'chaos',
    'fannkuchBench':'fannkuch',
    'floatOps':     'float',
    'genTree':      'generators',
    'nbody':        'nbody',
    'nqueens':      'nqueens',
    'raytrace':     'raytrace',
    'recursion':    'recursion',
    'richardsBench':'richards',
    'spectralNorm': 'spectral_norm',
}

# ---------------------------------------------------------------------------
#  ANSI helpers
# ---------------------------------------------------------------------------

def c(text, code):
    return f'\033[{code}m{text}\033[0m'

def bold(text):
    return c(text, '1')

def dim(text):
    return c(text, '2')

def colored(text, color):
    codes = {
        'bright green': '92', 'green': '32',
        'yellow': '33', 'red': '31',
        'bright cyan': '96', 'cyan': '36',
        'bright green bold': '92;1',
        'red bold': '31;1', 'magenta': '35',
    }
    return c(text, codes.get(color, '0'))

# ---------------------------------------------------------------------------
#  Formatting
# ---------------------------------------------------------------------------

def fmt_time(secs):
    if secs >= 1.0:
        return f'{secs:.3f}s'
    elif secs >= 0.001:
        return f'{secs * 1000:.2f}ms'
    else:
        return f'{secs * 1_000_000:.1f}us'

def fmt_ratio(ratio):
    if ratio >= 1.0:
        return f'{ratio:.2f}x'
    else:
        return f'{1.0/ratio:.2f}x'

# ---------------------------------------------------------------------------
#  Running suites
# ---------------------------------------------------------------------------

def run_ty(filt=None, rounds=5, warmup=3):
    ty_bin = os.path.join(ROOT_DIR, 'ty')
    if not os.path.isfile(ty_bin):
        # try build
        print(dim('ty binary not found, building...'))
        subprocess.run(['make', '-C', ROOT_DIR], check=True,
                       capture_output=True)

    cmd = [ty_bin, os.path.join(SCRIPT_DIR, 'run.ty'),
           '-n', str(rounds), f'--warmup={warmup}']
    if filt:
        cmd.append(filt)

    print(dim(f'Running ty benchmarks...'))
    subprocess.run(cmd, check=True, cwd=ROOT_DIR)

    with open(TY_RESULTS) as f:
        return json.load(f)

def run_python(filt=None, rounds=5, warmup=3):
    cmd = [sys.executable, os.path.join(SCRIPT_DIR, 'run_py.py'),
           '-n', str(rounds), f'--warmup={warmup}']
    if filt:
        cmd.append(filt)

    print(dim(f'Running Python benchmarks...'))
    subprocess.run(cmd, check=True, cwd=ROOT_DIR)

    with open(PY_RESULTS) as f:
        return json.load(f)

# ---------------------------------------------------------------------------
#  Comparison table
# ---------------------------------------------------------------------------

def print_table(ty_results, py_results):
    # Build lookup maps
    ty_map = {}
    for r in ty_results:
        display = TY_TO_DISPLAY.get(r['name'], r['name'])
        ty_map[display] = r

    py_map = {r['name']: r for r in py_results}

    all_names = sorted(set(ty_map.keys()) | set(py_map.keys()))

    if not all_names:
        print('No benchmark results to compare.')
        return

    name_w = max(len(n) for n in all_names) + 2
    header_name = 'Benchmark'

    # Header
    print()
    print(colored(bold(f'  ty vs Python  —  head-to-head comparison'), 'bright cyan'))
    print()

    hdr = (f'  {bold(f"{header_name:{name_w}}")}'
           f'  {"ty":>10}  {"Python":>10}  {"Ratio":>10}  {"Winner":>8}')
    print(hdr)
    print(f'  {"─" * (name_w + 46)}')

    ty_wins = 0
    py_wins = 0
    ratios = []

    for name in all_names:
        ty_r = ty_map.get(name)
        py_r = py_map.get(name)

        label = bold(f'{name:{name_w}}')

        if ty_r is None:
            print(f'  {label}  {dim("—"):>10}  {fmt_time(py_r["median"]):>10}  {dim("—"):>10}  {dim("—"):>8}')
            continue
        if py_r is None:
            print(f'  {label}  {fmt_time(ty_r["median"]):>10}  {dim("—"):>10}  {dim("—"):>10}  {dim("—"):>8}')
            continue

        ty_med = ty_r['median']
        py_med = py_r['median']

        ratio = py_med / ty_med  # >1 means ty is faster
        ratios.append(ratio)

        ty_str = fmt_time(ty_med)
        py_str = fmt_time(py_med)

        if ratio > 1.05:
            winner = colored(bold('ty'), 'bright green')
            ratio_str = colored(bold(fmt_ratio(ratio)), 'bright green')
            ty_wins += 1
        elif ratio < 0.95:
            winner = colored(bold('Python'), 'red')
            ratio_str = colored(bold(fmt_ratio(ratio)), 'red')
            py_wins += 1
        else:
            winner = dim('tie')
            ratio_str = dim('~1.00x')

        # Color the times: winner gets green, loser gets default
        if ratio > 1.0:
            ty_str = colored(ty_str, 'bright green')
        else:
            py_str = colored(py_str, 'bright green')

        print(f'  {label}  {ty_str:>20}  {py_str:>20}  {ratio_str:>20}  {winner:>18}')

    print(f'  {"─" * (name_w + 46)}')

    # Summary
    if ratios:
        geo_mean = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
        arith_mean = sum(ratios) / len(ratios)
        # Total times
        ty_total = sum(ty_map[n]['median'] for n in all_names if n in ty_map and n in py_map)
        py_total = sum(py_map[n]['median'] for n in all_names if n in ty_map and n in py_map)

        # Best/worst from ty's perspective
        best_for_ty = max(ratios)  # highest ratio = ty's biggest win
        worst_for_ty = min(ratios)  # lowest ratio = ty's worst showing

        def describe_ratio(r):
            if r >= 1.0:
                return colored(f'ty {r:.2f}x faster', 'bright green')
            else:
                return colored(f'Python {1.0/r:.2f}x faster', 'red')

        print()
        print(f'  {bold("Total time:"):24} ty {colored(fmt_time(ty_total), "cyan"):>18}   Python {colored(fmt_time(py_total), "magenta"):>18}')
        if geo_mean >= 1.0:
            geo_str = colored(bold(f'ty {geo_mean:.2f}x faster'), 'bright cyan')
        else:
            geo_str = colored(bold(f'Python {1.0/geo_mean:.2f}x faster'), 'red')
        print(f'  {bold("Geometric mean:"):24} {geo_str}')
        print(f'  {bold("Best:"):24} {describe_ratio(best_for_ty)}')
        print(f'  {bold("Worst:"):24} {describe_ratio(worst_for_ty)}')
        print(f'  {bold("Wins:"):24} ty {ty_wins}  /  Python {py_wins}  /  tied {len(ratios) - ty_wins - py_wins}')
    print()

# ---------------------------------------------------------------------------
#  Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description='ty vs Python benchmark comparison')
    parser.add_argument('filter', nargs='?', default=None, help='Benchmark name filter')
    parser.add_argument('-n', '--rounds', type=int, default=5, help='Timed rounds (default: 5)')
    parser.add_argument('--warmup', type=int, default=3, help='Warmup iterations (default: 3)')
    parser.add_argument('--cached', action='store_true', help='Use last saved results (skip re-run)')
    parser.add_argument('--ty-only', action='store_true', help='Only re-run ty (use cached Python)')
    parser.add_argument('--py-only', action='store_true', help='Only re-run Python (use cached ty)')
    args = parser.parse_args()

    ty_results = None
    py_results = None

    if args.cached:
        try:
            with open(TY_RESULTS) as f:
                ty_results = json.load(f)
        except FileNotFoundError:
            print('No cached ty results found. Run without --cached first.')
            sys.exit(1)
        try:
            with open(PY_RESULTS) as f:
                py_results = json.load(f)
        except FileNotFoundError:
            print('No cached Python results found. Run without --cached first.')
            sys.exit(1)
    else:
        if not args.py_only:
            ty_results = run_ty(args.filter, args.rounds, args.warmup)
        else:
            try:
                with open(TY_RESULTS) as f:
                    ty_results = json.load(f)
            except FileNotFoundError:
                print('No cached ty results. Run without --py-only first.')
                sys.exit(1)

        if not args.ty_only:
            py_results = run_python(args.filter, args.rounds, args.warmup)
        else:
            try:
                with open(PY_RESULTS) as f:
                    py_results = json.load(f)
            except FileNotFoundError:
                print('No cached Python results. Run without --ty-only first.')
                sys.exit(1)

    print_table(ty_results, py_results)

if __name__ == '__main__':
    main()
