import unittest
from scripts.relation_extraction.common import Entity, generate_candidates


class TestCandidates(unittest.TestCase):
    def test_pairs_same_sentence(self):
        ents = [
            Entity("T1", "A", 0),
            Entity("T2", "B", 0),
            Entity("T3", "C", 0),
            Entity("T4", "D", 1),
        ]
        # For 3 entities in sent 0: C(3,2) = 3 pairs; T4 isolated in sent 1
        pairs = generate_candidates(ents)
        self.assertEqual(len(pairs), 3)
        self.assertIn(("T1", "T2"), pairs)
        self.assertIn(("T1", "T3"), pairs)
        self.assertIn(("T2", "T3"), pairs)


if __name__ == "__main__":
    unittest.main()
