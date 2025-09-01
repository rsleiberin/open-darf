import json
import os
import tempfile
import unittest
import sys


class TestHeuristicPredictor(unittest.TestCase):
    def test_heuristic_assoc_gene_disease(self):
        # Toy: Gene-Disease in same sentence should predict 'assoc' and yield F1=1.0
        toy = {
            "doc_id": "D1",
            "entities": [
                {"id": "A", "type": "Gene", "sent": 0},
                {"id": "B", "type": "Disease", "sent": 0},
            ],
            "relations": [{"head": "A", "tail": "B", "type": "assoc"}],
        }
        with tempfile.TemporaryDirectory() as td:
            inp = os.path.join(td, "toy.jsonl")
            outp = os.path.join(td, "out.json")
            with open(inp, "w", encoding="utf-8") as fh:
                fh.write(json.dumps(toy) + "\n")
            # run emitter in heuristic mode
            from scripts.relation_extraction.emit_rel_metrics import main as emit_main

            old_argv = sys.argv
            sys.argv = [
                "emit_rel_metrics.py",
                "--input",
                inp,
                "--out",
                outp,
                "--predictor",
                "heuristic",
            ]
            try:
                emit_main()
            finally:
                sys.argv = old_argv
            data = json.load(open(outp, "r", encoding="utf-8"))
            self.assertAlmostEqual(data["biored"]["relation_f1"], 1.0)


if __name__ == "__main__":
    unittest.main()
