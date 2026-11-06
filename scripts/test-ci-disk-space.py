#!/usr/bin/env python3
"""Check cleanup boundaries without removing any installed SDK or invoking real sudo."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest


SCRIPT = Path(__file__).with_name("free-ci-disk-space.sh")


class DiskSpaceTests(unittest.TestCase):
    def run_script(self, overrides=None, removal_status=0, removal_seconds=0, await_removal=False):
        with tempfile.TemporaryDirectory(prefix="vcvio-ci-space-test-") as temporary:
            directory = Path(temporary)
            log = directory / "commands.jsonl"
            for name in ("df", "sudo"):
                stub = directory / name
                stub.write_text(
                    "#!/usr/bin/env python3\n"
                    "import json, os, sys, time\n"
                    "from pathlib import Path\n"
                    "with open(os.environ['CI_DISK_TEST_LOG'], 'a') as log:\n"
                    "    log.write(json.dumps([Path(sys.argv[0]).name, *sys.argv[1:]]) + '\\n')\n"
                    "if Path(sys.argv[0]).name == 'sudo':\n"
                    "    time.sleep(float(os.environ['CI_DISK_TEST_REMOVAL_SECONDS']))\n"
                    "    sys.exit(int(os.environ['CI_DISK_TEST_REMOVAL_STATUS']))\n"
                )
                stub.chmod(0o755)
            environment = os.environ | {
                "GITHUB_ACTIONS": "true",
                "RUNNER_ENVIRONMENT": "github-hosted",
                "RUNNER_OS": "Linux",
                "PATH": str(directory) + os.pathsep + os.environ["PATH"],
                "CI_DISK_TEST_LOG": str(log),
                "CI_DISK_TEST_REMOVAL_STATUS": str(removal_status),
                "CI_DISK_TEST_REMOVAL_SECONDS": str(removal_seconds),
            }
            environment.update(overrides or {})
            started = time.monotonic()
            result = subprocess.run(
                ["bash", str(SCRIPT)], env=environment, text=True, capture_output=True,
                check=False,
            )
            self.elapsed = time.monotonic() - started
            # The removal runs in the background, so its stub may not have logged yet.
            deadline = time.monotonic() + 10
            while await_removal and time.monotonic() < deadline and (
                not log.exists() or "sudo" not in log.read_text()
            ):
                time.sleep(0.05)
            commands = (
                [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
            )
            return result, commands

    def test_refuses_local_self_hosted_and_non_linux_contexts(self):
        for overrides in (
            {"GITHUB_ACTIONS": "false"},
            {"RUNNER_ENVIRONMENT": "self-hosted"},
            {"RUNNER_ENVIRONMENT": ""},
            {"RUNNER_OS": "macOS"},
        ):
            with self.subTest(overrides=overrides):
                result, commands = self.run_script(overrides)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("GitHub-hosted Linux", result.stderr)
                self.assertEqual(commands, [])

    def test_only_fixed_sdk_paths_are_removed_after_the_disk_report(self):
        result, commands = self.run_script(await_removal=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(commands, [
            ["df", "-h", "/"],
            ["sudo", "rm", "-rf", "--", "/usr/share/dotnet", "/usr/local/lib/android"],
        ])

    def test_script_does_not_wait_for_the_removal(self):
        result, commands = self.run_script(removal_status=8, removal_seconds=5, await_removal=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertLess(self.elapsed, 4)
        self.assertEqual(commands[-1][0], "sudo")


if __name__ == "__main__":
    unittest.main()
