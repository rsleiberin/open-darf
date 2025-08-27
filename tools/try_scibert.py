#!/usr/bin/env python3
import json
import sys
from apps.knowledge_graph.entity_extraction import extract_all

text = " ".join(sys.argv[1:]) or "Graph neural networks accelerate science."
print(json.dumps(extract_all(text), ensure_ascii=False, indent=2))
