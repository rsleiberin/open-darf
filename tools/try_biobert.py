#!/usr/bin/env python3
import json
import sys
from apps.knowledge_graph.entity_extraction import extract_all

text = (
    " ".join(sys.argv[1:]) or "Aspirin inhibits COX enzymes and reduces inflammation."
)
print(json.dumps(extract_all(text), ensure_ascii=False, indent=2))
