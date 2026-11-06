#!/usr/bin/env python3
"""Check umbrella validation and restoration without invoking Lake."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


UMBRELLAS = (
    "ToMathlib.lean", "VCVio.lean", "VCVioCslib.lean", "LatticeCrypto.lean", "Extern.lean",
    "HashSig.lean", "Examples.lean", "VCVioWidgets.lean", "VCVioTest.lean", "Interop.lean",
)


class CheckImportsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="vcvio-import-check-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(Path(__file__).with_name("check-imports.sh"), scripts / "check-imports.sh")
        for name in UMBRELLAS:
            (self.root / name).write_text(f"original {name}\n")

    def run_check(self, generator="exit 0\n"):
        update = self.root / "scripts/update-lib.sh"
        update.write_text("#!/usr/bin/env bash\nset -eu\n" + generator)
        update.chmod(0o755)
        return subprocess.run(
            ["/bin/bash", "scripts/check-imports.sh"], cwd=self.root,
            text=True, capture_output=True, timeout=10,
        )

    def assert_originals(self):
        for name in UMBRELLAS:
            self.assertEqual((self.root / name).read_text(), f"original {name}\n")

    def test_current_umbrellas_pass_unchanged(self):
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_originals()

    def test_stale_umbrella_fails_and_restores(self):
        result = self.run_check("printf 'generated\\n' > ToMathlib.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ToMathlib.lean is out of date", result.stderr)
        self.assert_originals()

    def test_missing_umbrella_fails_before_generator(self):
        (self.root / "ToMathlib.lean").unlink()
        result = self.run_check("touch generator-ran\nprintf 'generated\\n' > ToMathlib.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("required umbrella ToMathlib.lean is missing", result.stderr)
        self.assertFalse((self.root / "generator-ran").exists())
        self.assertFalse((self.root / "ToMathlib.lean").exists())

    def test_generator_failure_restores_partial_changes(self):
        result = self.run_check("printf 'partial\\n' > VCVio.lean\nexit 7\n")
        self.assertEqual(result.returncode, 7)
        self.assert_originals()

    def test_local_edits_are_restored_not_replaced_with_git(self):
        dirty = "user's uncommitted umbrella\n"
        (self.root / "VCVio.lean").write_text(dirty)
        result = self.run_check("printf 'generated\\n' > VCVio.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.root / "VCVio.lean").read_text(), dirty)

    def source_file(self, path):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text("module\n")

    def run_real_generator(self):
        source = Path(__file__).with_name("update-lib.sh")
        shutil.copyfile(source, self.root / "scripts/update-lib.sh")
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        return subprocess.run(["bash", "scripts/update-lib.sh"], cwd=self.root,
                              text=True, capture_output=True, timeout=10)

    def test_generator_lists_modules_in_byte_order(self):
        for path in ("VCVio/Zeta.lean", "VCVio/Alpha/Beta.lean", "VCVio/Alpha.lean",
                     "VCVio/AlphaBeta.lean"):
            self.source_file(path)
        result = self.run_real_generator()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            (self.root / "VCVio.lean").read_text(),
            "module  -- shake: keep-all --deprecated_module: ignore\n\n"
            "public import VCVio.Alpha\n"
            "public import VCVio.Alpha.Beta\n"
            "public import VCVio.AlphaBeta\n"
            "public import VCVio.Zeta\n")

    def test_generator_keeps_interop_outside_module_scopes(self):
        self.source_file("Interop/Hax/Adc.lean")
        result = self.run_real_generator()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / "Interop.lean").read_text(), "import Interop.Hax.Adc\n")

    def test_generator_skips_ignored_files(self):
        self.source_file("VCVio/Kept.lean")
        self.source_file("VCVio/Ignored.lean")
        (self.root / ".gitignore").write_text("VCVio/Ignored.lean\n")
        result = self.run_real_generator()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("Ignored", (self.root / "VCVio.lean").read_text())

    def test_generator_skips_deleted_tracked_files(self):
        self.source_file("VCVio/Kept.lean")
        self.source_file("VCVio/Deleted.lean")
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        subprocess.run(["git", "add", "VCVio"], cwd=self.root, check=True)
        (self.root / "VCVio/Deleted.lean").unlink()
        result = self.run_real_generator()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("Deleted", (self.root / "VCVio.lean").read_text())


if __name__ == "__main__":
    unittest.main()
