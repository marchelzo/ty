import os
import pathlib
import shutil
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[3]
OWNER = 65534
USER = 65533


def git(*args):
    subprocess.run(['git', *map(str, args)], check=True, capture_output=True)


def identity(real, effective):
    def apply():
        os.setreuid(real, effective)
    return apply


def main():
    if os.name != 'posix' or os.geteuid() != 0:
        print('Repository ownership tests require effective UID 0.', file=sys.stderr)
        return 77

    with tempfile.TemporaryDirectory(prefix='ty-git-ownership-') as directory:
        root = pathlib.Path(directory)
        root.chmod(0o755)
        repo = root / 'repo'
        git('init', '--initial-branch=main', repo)
        git('-C', repo, '-c', 'user.name=Ty', '-c', 'user.email=ty@example.invalid',
            'commit', '--allow-empty', '-m', 'Initial')
        git('clone', '--bare', repo, root / 'bare.git')
        git('-C', repo, 'worktree', 'add', '-b', 'other', root / 'worktree')
        (repo / 'sub').mkdir()
        (root / 'worktree' / 'sub').mkdir()

        for path in root.rglob('*'):
            os.chown(path, OWNER, -1)

        runtime = root / 'runtime'
        shutil.copytree(ROOT / 'lib', runtime / 'lib')
        shutil.copy2(ROOT / 'ty', runtime / 'ty')
        fixture = runtime / 'ownership.ty'
        shutil.copy2(ROOT / 'tests/fixtures/git/ownership.ty', fixture)
        env = {
            **os.environ,
            'TY_GIT_OWNERSHIP_ROOT': directory,
            'TY_LIBRARY_PATH': str(runtime / 'lib'),
        }
        env.pop('SUDO_UID', None)
        for real, effective in [(0, 0), (USER, 0), (0, USER)]:
            print(f'Real UID {real}, effective UID {effective}', flush=True)
            subprocess.run(
                [str(runtime / 'ty'), *sys.argv[1:], '--test', str(fixture)],
                cwd=runtime,
                env=env,
                preexec_fn=identity(real, effective),
                check=True,
                timeout=30,
            )
    return 0


if __name__ == '__main__':
    sys.exit(main())
