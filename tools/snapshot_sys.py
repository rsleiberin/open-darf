#!/usr/bin/env python3
import sys, json, os, time

import platform, subprocess, time, os, json
def sh(cmd):
    try:
        return subprocess.check_output(cmd, shell=True, stderr=subprocess.STDOUT, text=True, timeout=5)
    except Exception as e:
        return f"ERR:{e}"
snap = {
  "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
  "platform": platform.platform(),
  "machine": platform.machine(),
  "python": platform.python_version(),
  "cpu": sh("lscpu"),
  "mem": sh("free -h"),
  "disk": sh("df -h"),
  "kernel": sh("uname -a"),
  "os_release": sh("cat /etc/os-release"),
}
receipt_dir = os.path.join("var", "receipts", time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()))
os.makedirs(receipt_dir, exist_ok=True)
with open(os.path.join(receipt_dir, "snapshot_sys.out"), "w") as f:
    f.write(json.dumps(snap, indent=2, sort_keys=True))
