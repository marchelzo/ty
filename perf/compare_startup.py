import argparse
import json
import os
from pathlib import Path
import random
import statistics
import subprocess
import tempfile
import time


def tree_lib(binary):
    for folder in binary.parents:
        if (folder / 'lib' / 'prelude.ty').is_file():
            return folder / 'lib'
    raise SystemExit(f'no lib/prelude.ty above {binary}; pass --baseline-lib/--candidate-lib')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('baseline', type=Path)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('names', nargs='*')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=60)
    parser.add_argument('--cpu', type=int)
    parser.add_argument('--baseline-lib', type=Path)
    parser.add_argument('--candidate-lib', type=Path)
    opts = parser.parse_args()

    if opts.cpu is not None:
        os.sched_setaffinity(0, {opts.cpu})

    paths = [opts.baseline.resolve(), opts.candidate.resolve()]
    bins = [str(b) for b in paths]
    libs = [
        str((lib or tree_lib(binary)).resolve())
        for binary, lib in zip(paths, [opts.baseline_lib, opts.candidate_lib])
    ]
    results = {'binaries': bins, 'libraries': libs, 'cpu': opts.cpu, 'metrics': {}}
    rng = random.Random(89047)

    with tempfile.TemporaryDirectory(prefix='ty-startup-') as directory:
        folder = Path(directory)
        source = folder / 'frontend.ty'
        source.write_text('\n'.join(
            f'fn sample-{i}(x: Int) -> Int {{ (x + {i}) / 7 }}'
            for i in range(1500)
        ) + '\n')
        large = folder / 'large.ty'
        large.write_text('\n'.join(f'let value-{i} = {i}' for i in range(16000)) + '\n')
        usage = folder / 'usage.txt'
        scenarios = [
            ('startup', ['-e', '0'], {}),
            ('startup-unchecked', ['-q', '-e', '0'], {}),
            ('startup-uncached', ['-e', '0'], {'TY_TYPES2_CACHE': '0'}),
            ('import-pretty', ['-c', '-e', 'import pretty'], {}),
            ('import-ink', ['-c', '-e', 'import ink'], {}),
            ('import-jit', ['-c', '-e', 'import jit'], {}),
            ('frontend-cached', ['-c', str(source)], {}),
            ('frontend-uncached', ['-c', str(source)], {'TY_TYPES2_CACHE': '0'}),
            ('frontend-unchecked', ['-qc', str(source)], {}),
            ('frontend-large', ['-c', str(large)], {}),
        ]
        if opts.names:
            scenarios = [s for s in scenarios if s[0] in opts.names]

        for name, args, extra in scenarios:
            envs = [dict(os.environ, TY_LIBRARY_PATH=lib, **extra) for lib in libs]
            data = [[], []]
            for iteration in range(opts.rounds + 5):
                order = [0, 1]
                rng.shuffle(order)
                for index in order:
                    start = time.perf_counter_ns()
                    subprocess.run(
                        ['/usr/bin/time', '-f', '%M %U %S', '-o', str(usage), bins[index], *args],
                        env=envs[index], capture_output=True, text=True, check=True,
                    )
                    elapsed = (time.perf_counter_ns() - start) / 1e6
                    rss, user, system = usage.read_text().split()
                    if iteration >= 5:
                        data[index].append({
                            'ms': elapsed, 'rss_kib': int(rss),
                            'user_s': float(user), 'system_s': float(system),
                        })

            medians = [statistics.median(x['ms'] for x in xs) for xs in data]
            rss = [statistics.median(x['rss_kib'] for x in xs) for xs in data]
            delta = 100 * (medians[1] / medians[0] - 1)
            memdelta = 100 * (rss[1] / rss[0] - 1)
            results['metrics'][name] = {
                'samples': data, 'medians_ms': medians, 'median_rss_kib': rss,
                'change_percent': delta, 'rss_change_percent': memdelta,
            }
            opts.output.write_text(json.dumps(results, indent=2) + '\n')
            print(
                f'{name:22} {medians[0]:9.3f} {medians[1]:9.3f} ms {delta:+7.2f}%'
                f'  RSS {memdelta:+7.2f}%', flush=True,
            )


if __name__ == '__main__':
    main()
