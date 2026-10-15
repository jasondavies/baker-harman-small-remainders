"""Regression checks for the source audit; run with unittest discovery."""

from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_baker_harman_sources import imports, restore_imports, verify


class SourceAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'vendor'
        (self.root / 'BakerHarmanAnalytics').mkdir(parents=True)
        (self.root / 'BakerHarmanAnalytics/Main.lean').write_text('import BakerHarmanAnalytics.Dependency\ndef exampleValue := 1\n')
        (self.root / 'BakerHarmanAnalytics/Dependency.lean').write_text('import Mathlib\n')
        (self.root / 'lakefile.toml').write_text('name = "fixture"\n')
        self.manifest = {
            'entrypoints': ['BakerHarmanAnalytics.Main'],
            'revision': '0' * 40,
            'repository': 'https://github.com/openai/math',
            'source_root': 'lean',
            'files': {},
            'upstream_files': {},
            'config_files': {'lakefile.toml': self.digest((self.root / 'lakefile.toml').read_bytes())},
            'import_rewrite': {'from': 'OAI.NumberTheory.EgyptianFractions.', 'to': 'BakerHarmanAnalytics.'},
        }
        self.rehash()

    @staticmethod
    def digest(data):
        return hashlib.sha256(data).hexdigest()

    def rehash(self):
        for path in self.root.rglob('*.lean'):
            name = str(path.relative_to(self.root))
            data = path.read_bytes()
            self.manifest['files'][name] = self.digest(data)
            original = restore_imports(data, self.manifest['import_rewrite'])
            self.manifest['upstream_files'][name] = {
                'path': name.replace('BakerHarmanAnalytics/', 'lean/OAI/NumberTheory/EgyptianFractions/'), 'sha256': self.digest(original)}
        (self.root / 'UPSTREAM.json').write_text(json.dumps(self.manifest))

    def check(self, upstream=None):
        with redirect_stdout(io.StringIO()):
            verify(self.root, upstream)

    def test_import_modifiers_and_comments(self):
        source = '''/- Outer /- nested -/ comment -/
module
prelude
public /- comment -/ meta import BakerHarmanAnalytics.One
meta import all
  BakerHarmanAnalytics.Two
import Mathlib -- comment
public section
-- import Ignored.Comment
 def example := "import Ignored.String"
'''
        self.assertEqual([m for m, _, _ in imports(source)],
                         ['BakerHarmanAnalytics.One', 'BakerHarmanAnalytics.Two', 'Mathlib'])
        restored = restore_imports(source.encode(), self.manifest['import_rewrite']).decode()
        self.assertIn('meta import OAI.NumberTheory.EgyptianFractions.One', restored)
        self.assertIn('  OAI.NumberTheory.EgyptianFractions.Two', restored)
        self.assertIn('"import Ignored.String"', restored)

    def test_unterminated_comment_fails(self):
        with self.assertRaisesRegex(ValueError, 'Unterminated'):
            list(imports('/- unterminated'))

    def test_config_drift_fails(self):
        (self.root / 'lakefile.toml').write_text('name = "changed"\n')
        with self.assertRaisesRegex(ValueError, 'Local hash mismatch: lakefile.toml'):
            self.check()

    def test_modified_import_is_in_dependency_closure(self):
        (self.root / 'BakerHarmanAnalytics/Main.lean').write_text('module\npublic meta import BakerHarmanAnalytics.Missing\n')
        self.rehash()
        with self.assertRaisesRegex(ValueError, 'Unrecorded dependency: BakerHarmanAnalytics.Missing'):
            self.check()

    def test_unused_recorded_source_fails(self):
        (self.root / 'BakerHarmanAnalytics/Unused.lean').write_text('import Mathlib\n')
        self.rehash()
        with self.assertRaisesRegex(ValueError, 'Files outside the dependency closure'):
            self.check()

    def make_upstream(self):
        upstream = self.base / 'upstream'
        upstream.mkdir()
        for name, entry in self.manifest['upstream_files'].items():
            target = upstream / entry['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(restore_imports((self.root / name).read_bytes(),
                                              self.manifest['import_rewrite']))
        def git(*args):
            return subprocess.check_output(['git', '-C', str(upstream), *args],
                                           stderr=subprocess.DEVNULL, text=True)
        git('init', '-q')
        git('add', '.')
        git('-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.invalid',
            'commit', '-qm', 'Fixture')
        self.manifest['revision'] = git('rev-parse', 'HEAD').strip()
        self.rehash()
        return upstream

    def test_upstream_rejects_edit_even_after_both_hashes_change(self):
        upstream = self.make_upstream()
        self.check(upstream)
        path = self.root / 'BakerHarmanAnalytics/Main.lean'
        path.write_text(path.read_text().replace(':= 1', ':= 2'))
        self.rehash()
        self.check()  # Local consistency alone cannot establish provenance.
        with self.assertRaisesRegex(ValueError, 'Upstream content mismatch'):
            self.check(upstream)

    def test_source_edit_without_rehash_fails(self):
        (self.root / 'BakerHarmanAnalytics/Main.lean').write_text('def changed := 2\n')
        with self.assertRaisesRegex(ValueError, 'Local hash mismatch'):
            self.check()

    def test_unrecorded_file_fails(self):
        (self.root / 'BakerHarmanAnalytics/Extra.lean').write_text('def extra := 1\n')
        with self.assertRaisesRegex(ValueError, 'Source set mismatch'):
            self.check()

    def test_path_swap_fails_even_with_matching_hashes_and_upstream_blobs(self):
        upstream = self.make_upstream()
        first, second = 'BakerHarmanAnalytics/Main.lean', 'BakerHarmanAnalytics/Dependency.lean'
        a, b = self.root / first, self.root / second
        before_a, before_b = a.read_bytes(), b.read_bytes()
        a.write_bytes(before_b)
        b.write_bytes(before_a)
        for key in ('files', 'upstream_files'):
            entries = self.manifest[key]
            entries[first], entries[second] = entries[second], entries[first]
        (self.root / 'UPSTREAM.json').write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(ValueError, 'Upstream path mismatch'):
            self.check(upstream)

    def test_symbolic_revision_fails(self):
        upstream = self.make_upstream()
        self.manifest['revision'] = 'HEAD'
        (self.root / 'UPSTREAM.json').write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(ValueError, 'full 40-character commit hash'):
            self.check(upstream)

    def test_lattice_path_exception(self):
        from check_baker_harman_sources import upstream_path
        self.assertEqual(upstream_path('BakerHarmanAnalytics/LatticeHyperplaneBasis.lean'),
                         'lean/OAI/Combinatorics/Progressions/Lattices/LatticeHyperplaneBasis.lean')


if __name__ == '__main__':
    unittest.main()
