#!/usr/bin/env python3
"""Python benchmark runner — mirrors perf/run.ty for apples-to-apples comparison."""

import argparse
import importlib
import json
import math
import os
import sys
import time

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RESULTS_FILE = os.path.join(SCRIPT_DIR, 'results_py.json')
BEST_FILE = os.path.join(SCRIPT_DIR, 'best_py.json')

# ---------------------------------------------------------------------------
#  Statistics
# ---------------------------------------------------------------------------

def median(xs):
    s = sorted(xs)
    n = len(s)
    if n % 2 == 0:
        return (s[n // 2 - 1] + s[n // 2]) / 2.0
    return s[n // 2]

def stddev(xs):
    m = sum(xs) / len(xs)
    variance = sum((x - m) ** 2 for x in xs) / len(xs)
    return math.sqrt(variance)

# ---------------------------------------------------------------------------
#  Result
# ---------------------------------------------------------------------------

class Result:
    def __init__(self, name, times, iters=1):
        self.name = name
        self.times = times
        self.iters = iters

    @property
    def per_iter_times(self):
        return [t / self.iters for t in self.times]

    @property
    def med(self):
        return median(self.per_iter_times)

    @property
    def sd(self):
        return stddev(self.per_iter_times)

    @property
    def best(self):
        return min(self.times) / self.iters

    @property
    def worst(self):
        return max(self.times) / self.iters

    def to_dict(self):
        return {
            'name': self.name,
            'times': self.per_iter_times,
            'iters': self.iters,
            'mean': sum(self.per_iter_times) / len(self.per_iter_times),
            'median': self.med,
            'min': self.best,
            'max': self.worst,
            'stddev': self.sd,
        }

# ---------------------------------------------------------------------------
#  Calibration & runner
# ---------------------------------------------------------------------------

def calibrate(f, target=0.5):
    iters = 1
    while True:
        t0 = time.perf_counter()
        f(iters)
        elapsed = time.perf_counter() - t0
        if elapsed >= target:
            return iters
        if elapsed < 0.01:
            iters *= 10
        else:
            iters = max(iters + 1, math.ceil(iters * target / elapsed))

def run_one(name, f, warmup=3, rounds=5, target=0.5):
    for _ in range(warmup):
        f(1)

    iters = calibrate(f, target)

    times = []
    for _ in range(rounds):
        t0 = time.perf_counter()
        f(iters)
        times.append(time.perf_counter() - t0)

    return Result(name, times, iters)

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

def fmt_delta(ratio):
    pct = (ratio - 1.0) * 100.0
    if abs(pct) < 0.5:
        return 'same'
    elif pct > 0:
        return f'+{pct:.1f}%'
    else:
        return f'{pct:.1f}%'

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
        'bright cyan': '96', 'bright green bold': '92;1',
        'red bold': '31;1',
    }
    return c(text, codes.get(color, '0'))

# ---------------------------------------------------------------------------
#  Persistence
# ---------------------------------------------------------------------------

def save_results(path, results):
    with open(path, 'w') as f:
        json.dump([r.to_dict() for r in results], f)

def load_results(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return None

def load_best(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}

def update_best(path, results):
    best = load_best(path)
    updated = False
    for r in results:
        old = best.get(r.name)
        if old is not None:
            if r.med < old['median']:
                best[r.name] = r.to_dict()
                updated = True
        else:
            best[r.name] = r.to_dict()
            updated = True
    if updated:
        with open(path, 'w') as f:
            json.dump(best, f)
    return best

# ---------------------------------------------------------------------------
#  Benchmark discovery
# ---------------------------------------------------------------------------

# Map: display name -> (module_name, function_name)
BENCHMARKS = [
    ('chaos',         'chaos',         'chaos_game'),
    ('fannkuch',      'fannkuch',      'fannkuch_bench'),
    ('float',         'float_bench',   'float_ops'),
    ('generators',    'generators',    'gen_tree'),
    ('nbody',         'nbody',         'nbody'),
    ('nqueens',       'nqueens',       'nqueens'),
    ('raytrace',      'raytrace',      'raytrace'),
    ('recursion',     'recursion',     'recursion'),
    ('richards',      'richards',      'richards_bench'),
    ('spectral_norm', 'spectral_norm', 'spectral_norm'),
]

def load_benchmarks(filt=None):
    bench_dir = os.path.join(SCRIPT_DIR, 'benchmarks_py')
    sys.path.insert(0, bench_dir)

    loaded = []
    for display_name, mod_name, func_name in BENCHMARKS:
        if filt and filt not in display_name:
            continue
        mod = importlib.import_module(mod_name)
        fn = getattr(mod, func_name)
        loaded.append((display_name, fn))

    return loaded

# ---------------------------------------------------------------------------
#  Main
# ---------------------------------------------------------------------------

def print_comparison(title, ref_map, results, name_width):
    print()
    print(colored(bold(title), 'bright cyan'))
    print()
    for r in results:
        label = bold(f'{r.name:{name_width}}')
        old = ref_map.get(r.name)
        if old is not None:
            old_med = old['median']
            ratio = r.med / old_med
            delta = fmt_delta(ratio)
            if ratio < 0.95:
                clr = 'bright green bold'
            elif ratio > 1.05:
                clr = 'red bold'
            else:
                clr = None
            delta_str = colored(delta, clr) if clr else dim(delta)
            print(f'  {label} {fmt_time(old_med):>10} -> {fmt_time(r.med):>10}  {delta_str}')
        else:
            print(f'  {label} {dim("no previous data")}')

def main():
    parser = argparse.ArgumentParser(description='Python performance suite')
    parser.add_argument('filter', nargs='?', default=None, help='Benchmark name filter')
    parser.add_argument('-c', '--compare', action='store_true', help='Compare with previous and best results')
    parser.add_argument('-S', '--no-save', action='store_true', help="Don't save results")
    parser.add_argument('--warmup', type=int, default=3, help='Warmup iterations (default: 3)')
    parser.add_argument('-n', '--rounds', type=int, default=5, help='Timed rounds (default: 5)')
    parser.add_argument('--json', action='store_true', help='Output results as JSON (for compare.py)')
    args = parser.parse_args()

    benchmarks = load_benchmarks(args.filter)

    if not benchmarks:
        print(f'No benchmarks matched filter: {args.filter!r}')
        all_names = ', '.join(n for n, _, _ in BENCHMARKS)
        print(f'Available: {all_names}')
        sys.exit(1)

    if not args.json:
        print(colored(bold('Python performance suite'), 'bright cyan'))
        print(dim(f'{len(benchmarks)} benchmark(s) · {args.rounds} rounds · {args.warmup} warmup'))
        print(f'{dim("Python " + sys.version.split()[0])}')
        print()

    best = load_best(BEST_FILE)
    results = []
    name_width = max(len(name) for name, _ in benchmarks) + 2

    for name, fn in benchmarks:
        if not args.json:
            label = bold(f'{name:{name_width}}')
            print(f'{label} {dim("calibrating...")}', end='', flush=True)

        r = run_one(name, fn, warmup=args.warmup, rounds=args.rounds)
        results.append(r)

        if not args.json:
            print(f'\r\033[K', end='')
            time_str = fmt_time(r.med)
            sd_str = fmt_time(r.sd)

            b = best.get(r.name)
            if b is not None:
                best_med = b['median']
                ratio = r.med / best_med
                if ratio <= 1.02:
                    clr = 'bright green'
                elif ratio < 1.10:
                    clr = 'green'
                elif ratio < 1.25:
                    clr = 'yellow'
                else:
                    clr = 'red'
            else:
                clr = 'bright green'

            label = bold(f'{name:{name_width}}')
            print(f'{label} {colored(bold(f"{time_str:>10}"), clr)}/iter {dim(f"± {sd_str:<8} ({r.iters} iters × {args.rounds} rounds)")}')

    if args.json:
        print(json.dumps([r.to_dict() for r in results]))
        return

    if args.compare:
        prev = load_results(RESULTS_FILE)
        if prev is not None:
            prev_map = {e['name']: e for e in prev}
            print_comparison('Comparison with previous run:', prev_map, results, name_width)
        else:
            print(dim('\nNo previous results to compare against.'))

    print()
    total = sum(r.med for r in results)
    print(f'{bold("Total:")} {fmt_time(total)}')

    if not args.no_save:
        save_results(RESULTS_FILE, results)
        print(dim(f'Results saved to {RESULTS_FILE}'))

    if best:
        print_comparison('Comparison with all-time best:', best, results, name_width)
    update_best(BEST_FILE, results)

if __name__ == '__main__':
    main()
