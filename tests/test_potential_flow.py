"""Preflight checks for Euler/PotentialFlow modules (no Lean execution)."""

from __future__ import annotations

import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PF = ROOT / "Euler" / "PotentialFlow"

REQUIRED_LEAN = [
    "Definitions.lean",
    "GradientCurl.lean",
    "Laplace.lean",
    "Bernoulli.lean",
    "ExteriorDomain.lean",
    "Circulation.lean",
    "VortexCoreCoupling.lean",
]


class TestPotentialFlowPreflight(unittest.TestCase):
    def test_module_files_exist(self) -> None:
        for name in REQUIRED_LEAN:
            path = PF / name
            self.assertTrue(path.is_file(), f"missing {path}")

    def test_aggregator_and_readme_exist(self) -> None:
        self.assertTrue((ROOT / "Euler" / "PotentialFlow.lean").is_file())
        self.assertTrue((PF / "README.md").is_file())
        self.assertTrue((ROOT / "run_euler_potential_flow.cmd").is_file())

    def test_readme_mentions_gauge_distinction(self) -> None:
        text = (PF / "README.md").read_text(encoding="utf-8")
        self.assertIn("v = ∇φ", text)
        self.assertIn("v = ∇ × A", text)
        self.assertIn("BLOCKED", text)

    def test_no_sorry_in_sources(self) -> None:
        import re

        for name in REQUIRED_LEAN:
            text = (PF / name).read_text(encoding="utf-8")
            self.assertIsNone(re.search(r"\bsorry\b", text), f"sorry in {name}")
            self.assertIsNone(re.search(r"\badmit\b", text), f"admit in {name}")

    def test_validation_schema_if_present(self) -> None:
        path = ROOT / "VALIDATION_POTENTIAL_FLOW.json"
        if not path.is_file():
            self.skipTest("validation report not written yet")
        data = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(data.get("project"), "Euler.PotentialFlow")
        gates = data.get("gates", {})
        for key in ["P0", "P1", "P2", "P3", "P4", "P5", "P6", "P7", "P8"]:
            self.assertIn(key, gates)
            self.assertIn(gates[key], ["PASS", "FAIL", "BLOCKED", "UNRESOLVED"])


if __name__ == "__main__":
    unittest.main()
