"""Verify the pinned analytic sources, import relocation, and dependency closure."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1] / 'vendor' / 'baker-harman-analytics'
manifest = json.loads((root / 'UPSTREAM.json').read_text())
expected = manifest['files']
actual = {str(p.relative_to(root)) for p in root.rglob('*.lean') if '.lake' not in p.parts}
if actual != set(expected):
    raise SystemExit(f'Source set mismatch: missing={set(expected) - actual}, extra={actual - set(expected)}')

rewrite = manifest['import_rewrite']
for name, digest in expected.items():
    data = (root / name).read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise SystemExit(f'Source hash mismatch: {name}')
    original = data.decode().replace('import ' + rewrite['to'], 'import ' + rewrite['from']).encode()
    if hashlib.sha256(original).hexdigest() != manifest['upstream_files'][name]['sha256']:
        raise SystemExit(f'Changes beyond import relocation: {name}')

visited = set()


def visit(module):
    if module == 'Mathlib' or module.startswith('Mathlib.'):
        return
    name = module.replace('.', '/') + '.lean'
    if name in visited:
        return
    if name not in expected:
        raise SystemExit(f'Unrecorded dependency: {module}')
    visited.add(name)
    for dependency in re.findall(r'^import\s+(\S+)', (root / name).read_text(), re.MULTILINE):
        visit(dependency)


for entrypoint in manifest['entrypoints']:
    visit(entrypoint)
if visited != set(expected):
    raise SystemExit(f'Files outside the dependency closure: {set(expected) - visited}')
print(f'Verified {len(expected)} analytic sources, import-only relocation, and exact dependency closure.')
