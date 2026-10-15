"""Ensure the axiom audit catches declarations outside the library namespace.

Run with unittest discovery after `lake build`.
"""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest


class AxiomAuditTests(unittest.TestCase):
    def test_root_axiom_in_library_module_is_rejected(self):
        root = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            # Lean resolves a module root from one search directory, so overlay
            # the built library with symlinks before adding the test module.
            shutil.copytree(root / '.lake/build/lib/lean', temp,
                            dirs_exist_ok=True, copy_function=os.symlink)
            fixture = temp / 'BakerHarman/AuditCanary.lean'
            fixture.write_text('axiom auditOutsideNamespace : False\n')
            subprocess.run(['lake', 'env', 'lean', '--root=' + str(temp),
                            '-o', str(fixture.with_suffix('.olean')), str(fixture)],
                           cwd=root, check=True, capture_output=True, text=True)
            audit = temp / 'CheckAxioms.lean'
            audit.write_text('import BakerHarman.AuditCanary\n' +
                             (root / 'scripts/CheckAxioms.lean').read_text())
            lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                                cwd=root, text=True).strip()
            result = subprocess.run(
                ['lake', 'env', 'env', 'LEAN_PATH=' + str(temp) + ':' + lean_path,
                 'lean', str(audit)], cwd=root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unexpected axiom auditOutsideNamespace', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
