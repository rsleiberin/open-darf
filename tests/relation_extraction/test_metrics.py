import json
import os
import tempfile
import unittest

from scripts.relation_extraction.common import micro_prf1


class TestMetrics(unittest.TestCase):
    def test_micro_prf1_exact_match(self):
        gold = {("A", "B", "rel")}
        pred = {("A", "B", "rel")}
        p, r, f1, sup = micro_prf1(gold, pred)
        self.assertEqual(sup, 1)
        self.assertAlmostEqual(p, 1.0)
        self.assertAlmostEqual(r, 1.0)
        self.assertAlmostEqual(f1, 1.0)

    def test_emit_rel_metrics_zero(self):
        # Build a tiny toy JSONL with one gold relation and ensure emitter writes zeros (no preds)
        toy = {
            "doc_id": "D1",
            "entities": [
                {"id": "A", "type": "X", "sent": 0},
                {"id": "B", "type": "Y", "sent": 0},
            ],
            "relations": [{"head": "A", "tail": "B", "type": "rel"}],
        }
        from scripts.relation_extraction.emit_rel_metrics import (
            main as emit_main,
        )  # lazy import

        with tempfile.TemporaryDirectory() as td:
            inp = os.path.join(td, "toy.jsonl")
            outp = os.path.join(td, "out.json")
            with open(inp, "w", encoding="utf-8") as fh:
                fh.write(json.dumps(toy) + "\n")
            # Monkeypatch argv for emitter
            import sys

            old_argv = sys.argv
            sys.argv = ["emit_rel_metrics.py", "--input", inp, "--out", outp]
            try:
                emit_main()
            finally:
                sys.argv = old_argv
            with open(outp, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            self.assertIn("biored", data)
            self.assertEqual(data["biored"]["relation_f1"], 0.0)


if __name__ == "__main__":
    unittest.main()
