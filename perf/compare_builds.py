import argparse
import json
import os
from pathlib import Path
import random
import statistics
import subprocess
import tempfile
import time

PERF = Path(__file__).resolve().parent


def tree_lib(binary):
    for folder in binary.parents:
        if (folder / 'lib' / 'prelude.ty').is_file():
            return folder / 'lib'
    raise SystemExit(f'no lib/prelude.ty above {binary}; pass --baseline-lib/--candidate-lib')


def overlay(lib, folder):
    folder.mkdir()
    for entry in lib.iterdir():
        (folder / entry.name).symlink_to(entry)
    (folder / 'lib.ty').unlink(missing_ok=True)
    (folder / 'lib.ty').symlink_to(PERF / 'lib.ty')
    return folder


def invoke(binary, library, program, *args):
    env = dict(os.environ, TY_LIBRARY_PATH=str(library))
    result = subprocess.run(
        [binary, str(program), *map(str, args)],
        env=env, capture_output=True, text=True, check=True,
    )
    return json.loads(result.stdout)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('baseline', type=Path)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('names', nargs='*')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=9)
    parser.add_argument('--target', type=float, default=0.2)
    parser.add_argument('--cpu', type=int)
    parser.add_argument('--baseline-lib', type=Path)
    parser.add_argument('--candidate-lib', type=Path)
    opts = parser.parse_args()

    if opts.cpu is not None:
        os.sched_setaffinity(0, {opts.cpu})

    bins = [opts.baseline.resolve(), opts.candidate.resolve()]
    libs = [
        (lib or tree_lib(binary)).resolve()
        for binary, lib in zip(bins, [opts.baseline_lib, opts.candidate_lib])
    ]

    with tempfile.TemporaryDirectory(prefix='ty-compare-') as directory:
        paths = [overlay(lib, Path(directory) / name) for lib, name in zip(libs, ['baseline', 'candidate'])]
        compare(opts, [str(b) for b in bins], [str(l) for l in libs], paths)


def compare(opts, bins, libs, paths):
    programs = sorted((PERF / 'benchmarks').glob('*.ty'))
    if opts.names:
        programs = [p for p in programs if p.stem in opts.names]

    rng = random.Random(915073)
    results = {'binaries': bins, 'libraries': libs, 'cpu': opts.cpu, 'benchmarks': {}}

    for program in programs:
        iters = invoke(bins[0], paths[0], program, '--ty-perf-calibrate', opts.target)
        samples = [[], []]
        elapsed = [[], []]
        for _ in range(opts.rounds):
            order = [0, 1]
            rng.shuffle(order)
            for index in order:
                start = time.perf_counter()
                result = invoke(bins[index], paths[index], program, '--ty-perf-bench', iters, 5, 3)
                elapsed[index].append(time.perf_counter() - start)
                samples[index].append(statistics.median(result['times']) / iters)

        medians = [statistics.median(s) for s in samples]
        delta = 100 * (medians[1] / medians[0] - 1)
        results['benchmarks'][program.stem] = {
            'iterations': iters, 'samples': samples, 'elapsed': elapsed,
            'medians': medians, 'change_percent': delta,
        }
        opts.output.write_text(json.dumps(results, indent=2) + '\n')
        print(f'{program.stem:22} {medians[0] * 1000:10.3f} {medians[1] * 1000:10.3f} ms {delta:+7.2f}%', flush=True)


if __name__ == '__main__':
    main()
