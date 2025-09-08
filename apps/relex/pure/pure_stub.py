#!/usr/bin/env python3
"""
PURE baseline scaffold.
- If deps missing, print {"status":"skipped", ...} and exit 0 (keeps CI green).
- If deps present, print {"status":"ready", ...} and exit 0 (implementation can be added later).
"""
import json, sys
def has(pkg):
    try:
        __import__(pkg); return True
    except Exception:
        return False
torch_ok = has("torch")
tx_ok = has("transformers")
status = "ready" if (torch_ok and tx_ok) else "skipped"
print(json.dumps({
    "status": status,
    "torch": bool(torch_ok),
    "transformers": bool(tx_ok),
    "note": "Scaffold mode; implements detection only."
}))
sys.exit(0)
