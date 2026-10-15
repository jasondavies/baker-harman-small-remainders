"""Mutation tests for audit coverage, axiom rejection, and sorry rejection.

Run with unittest discovery after `lake build`.
"""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest


class AxiomAuditTests(unittest.TestCase):
    def check_fixture(self, namespace, code, imported=True):
        root = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            # Lean resolves a module root from one search directory. Overlay both
            # built libraries without writing into the real source or build trees.
            for library in (root, root / 'vendor/baker-harman-analytics'):
                shutil.copytree(library / '.lake/build/lib/lean', temp,
                                dirs_exist_ok=True, copy_function=os.symlink)
            analytics = temp / 'vendor/baker-harman-analytics/BakerHarmanAnalytics'
            analytics.mkdir(parents=True)
            source_dir = temp / 'BakerHarman' if namespace == 'BakerHarman' else analytics
            fixture = source_dir / 'AuditCanary.lean'
            fixture.write_text(code)
            module = namespace + '.AuditCanary'
            if imported:
                # Compile with the same logical module name as the source's coverage entry.
                source_root = source_dir.parent
                subprocess.run(['lake', 'env', 'lean', '--root=' + str(source_root),
                                '-o', str(temp / namespace / 'AuditCanary.olean'), str(fixture)],
                               cwd=root, check=True, capture_output=True, text=True)
            audit = temp / 'scripts/CheckAxioms.lean'
            audit.parent.mkdir()
            audit.write_text((f'import {module}\n' if imported else '') +
                             (root / 'scripts/CheckAxioms.lean').read_text())
            lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                                cwd=root, text=True).strip()
            return subprocess.run(
                ['lake', 'env', 'env', 'LEAN_PATH=' + str(temp) + ':' + lean_path,
                 'lean', str(audit)], cwd=root, capture_output=True, text=True)

    def assert_rejected(self, result, message):
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(message, result.stdout + result.stderr)

    def test_root_axiom_in_library_module_is_rejected(self):
        result = self.check_fixture('BakerHarman', 'axiom auditOutsideNamespace : False\n')
        self.assert_rejected(result, 'Unexpected axiom auditOutsideNamespace')

    def test_sorry_in_library_module_is_rejected(self):
        result = self.check_fixture('BakerHarman', 'theorem auditSorry : False := by sorry\n')
        self.assert_rejected(result, 'Unexpected axiom sorryAx')

    def test_root_axiom_in_analytics_module_is_rejected(self):
        result = self.check_fixture('BakerHarmanAnalytics', 'axiom analyticsCanary : False\n')
        self.assert_rejected(result, 'Unexpected axiom analyticsCanary')

    def test_unimported_library_module_is_rejected(self):
        result = self.check_fixture('BakerHarman', 'def unused := 1\n', imported=False)
        self.assert_rejected(result, 'Source module is not imported by the audit: BakerHarman.AuditCanary')

    def test_unimported_analytics_module_is_rejected(self):
        result = self.check_fixture('BakerHarmanAnalytics', 'def unused := 1\n', imported=False)
        self.assert_rejected(result, 'Source module is not imported by the audit: BakerHarmanAnalytics.AuditCanary')


if __name__ == '__main__':
    unittest.main()
