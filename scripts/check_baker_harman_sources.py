"""Check local source consistency, optionally comparing a separate upstream checkout."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def imports(source):
    """Read Lean's header, including nested comments and public/meta/import all.

    Return module names and their spans so relocation changes only imports.
    The vendored module names use ordinary (unquoted) Lean identifiers.
    """
    pos = 0

    def skip_trivia():
        nonlocal pos
        while pos < len(source):
            if source[pos].isspace():
                pos += 1
            elif source.startswith('--', pos):
                end = source.find('\n', pos)
                pos = len(source) if end < 0 else end + 1
            elif source.startswith('/-', pos):
                pos += 2
                depth = 1
                while depth:
                    if pos == len(source):
                        raise ValueError('Unterminated header comment')
                    if source.startswith('/-', pos):
                        depth += 1
                        pos += 2
                    elif source.startswith('-/', pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
            else:
                break

    def word(value):
        nonlocal pos
        skip_trivia()
        match = re.match(re.escape(value) + r'\b', source[pos:])
        if match:
            pos += len(value)
        return bool(match)

    word('module')
    word('prelude')
    while True:
        word('public')
        word('meta')
        if not word('import'):
            # `public section` and `meta section` begin the module body.
            return
        word('all')
        skip_trivia()
        match = re.match(r'[^\W\d]\w*(?:\.[^\W\d]\w*)*', source[pos:])
        if not match:
            raise ValueError('Unsupported or missing imported module name')
        start = pos
        pos += len(match[0])
        if pos < len(source) and not (source[pos].isspace() or
                                     source.startswith(('--', '/-'), pos)):
            raise ValueError('Unsupported imported module name')
        yield match[0], start, pos


def restore_imports(data, rewrite):
    source = data.decode()
    for module, start, end in reversed(list(imports(source))):
        if module.startswith(rewrite['to']):
            source = source[:start] + rewrite['from'] + module[len(rewrite['to']):] + source[end:]
    return source.encode()


def upstream_path(name):
    """The extraction's fixed module relocation, independent of manifest paths."""
    if name == 'BakerHarmanAnalytics/LatticeHyperplaneBasis.lean':
        return 'lean/OAI/Combinatorics/Progressions/Lattices/LatticeHyperplaneBasis.lean'
    if not re.fullmatch(r'BakerHarmanAnalytics/[A-Za-z_][A-Za-z_0-9]*\.lean', name):
        raise ValueError(f'Unsupported local module path: {name}')
    return 'lean/OAI/NumberTheory/EgyptianFractions/' + name.split('/')[1]


def verify(root, upstream_checkout=None):
    manifest = json.loads((root / 'UPSTREAM.json').read_text())
    revision = manifest['revision']
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise ValueError('Upstream revision must be a full 40-character commit hash')
    if manifest['repository'] != 'https://github.com/openai/math':
        raise ValueError('Unexpected upstream repository')
    if manifest['source_root'] != 'lean' or manifest['import_rewrite'] != {
            'from': 'OAI.NumberTheory.EgyptianFractions.', 'to': 'BakerHarmanAnalytics.'}:
        raise ValueError('Unexpected import relocation')
    expected = manifest['files']
    actual = {str(p.relative_to(root)) for p in root.rglob('*.lean')
              if '.lake' not in p.relative_to(root).parts}
    if actual != set(expected):
        raise ValueError(f'Source set mismatch: missing={set(expected) - actual}, extra={actual - set(expected)}')
    if set(manifest['upstream_files']) != set(expected):
        raise ValueError('Upstream source set mismatch')
    if set(manifest['config_files']) != {'lakefile.toml'}:
        raise ValueError('Expected a hash for lakefile.toml')
    for name in expected:
        if manifest['upstream_files'][name]['path'] != upstream_path(name):
            raise ValueError(f'Upstream path mismatch: {name}')
    for name, digest in (expected | manifest['config_files']).items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f'Local hash mismatch: {name}')

    if upstream_checkout is not None:
        # Read committed blobs, independently of the checkout's working tree and
        # the hashes recorded in our local manifest.
        revision = subprocess.check_output(
            ['git', '-C', str(upstream_checkout), 'rev-parse', '--verify',
             revision + '^{commit}'], text=True).strip()
    for name in expected:
        original = restore_imports((root / name).read_bytes(), manifest['import_rewrite'])
        upstream = manifest['upstream_files'][name]
        if hashlib.sha256(original).hexdigest() != upstream['sha256']:
            raise ValueError(f'Import-relocation hash mismatch: {name}')
        if upstream_checkout is not None:
            blob = subprocess.check_output(
                ['git', '-C', str(upstream_checkout), 'show', revision + ':' + upstream_path(name)])
            if original != blob:
                raise ValueError(f'Upstream content mismatch: {name}')

    visited = set()

    def visit(module):
        if module == 'Mathlib' or module.startswith('Mathlib.'):
            return
        name = module.replace('.', '/') + '.lean'
        if name in visited:
            return
        if name not in expected:
            raise ValueError(f'Unrecorded dependency: {module}')
        visited.add(name)
        for dependency, _, _ in imports((root / name).read_text()):
            visit(dependency)

    for entrypoint in manifest['entrypoints']:
        visit(entrypoint)
    if visited != set(expected):
        raise ValueError(f'Files outside the dependency closure: {set(expected) - visited}')
    print(f'Checked local consistency of {len(expected)} analytic sources, lakefile.toml, '
          'import relocation, and exact dependency closure against UPSTREAM.json.')
    if upstream_checkout is not None:
        print(f'Also matched restored source bytes to upstream Git commit {revision}.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream-checkout', type=Path,
                        help='separate openai/math Git checkout containing the recorded commit')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1] / 'vendor' / 'baker-harman-analytics'
    try:
        verify(root, args.upstream_checkout)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error


if __name__ == '__main__':
    main()
