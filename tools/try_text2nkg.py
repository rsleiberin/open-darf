#!/usr/bin/env python3
import json
import sys
from apps.knowledge_graph.entity_extraction import extract_all

txt = " ".join(sys.argv[1:]) or "Research uses datasets."
print(json.dumps(extract_all(txt), ensure_ascii=False, indent=2))
