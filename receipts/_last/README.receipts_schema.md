# Canonical ML Accuracy Receipts (Phase 6B)

Each dataset writes a single JSON file under receipts/_last/:

  {
    "micro": { "P": float, "R": float, "F1": float, "tp": int, "fp": int, "fn": int },
    "meta":  { "dataset": "SciERC|BioRED", "split": "test", "generated_at": ISO8601, "version": "semver" }
  }
