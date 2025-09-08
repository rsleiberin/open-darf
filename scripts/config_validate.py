#!/usr/bin/env python3
import json, sys
try:
    from packages.darf_config.settings import load_settings
    s = load_settings()
    print(json.dumps({"status":"ok","settings":{k:getattr(s,k) for k in dir(s) if k.isupper() and not k.startswith('_')}}))
except Exception as e:
    print(json.dumps({"status":"error","reason":str(e)}))
    sys.exit(1)
