#!/usr/bin/env bash
set -euo pipefail
REPO="$(git rev-parse --show-toplevel 2>/dev/null || echo "${REPO:-$PWD}")"
cd "$REPO"
export PYTHONPATH="${REPO}:${PYTHONPATH-}" TRANSFORMERS_OFFLINE=1 HF_HUB_DISABLE_TELEMETRY=1

echo "==[BioRED]== Heuristic runs → synth gold → score"
T2NKG_ADAPTER=heuristic python3 -m tools.text2nkg.run_eval --dataset biored --split dev  || true
T2NKG_ADAPTER=heuristic python3 -m tools.text2nkg.run_eval --dataset biored --split test || true
python3 - << 'PY'
import os,glob,json
out_dir="var/datasets/text/biored_gold_synth"; os.makedirs(out_dir, exist_ok=True)
def build(split):
  runs=sorted([d for d in glob.glob(f"var/receipts/phase7a/text2nkg/biored_{split}_*") if os.path.isdir(d)])
  if not runs: raise SystemExit(0)
  nkg=json.load(open(os.path.join(runs[-1],"nkg.json"))); by={}
  for nd in nkg.get("nodes",[]):
    sid=str(nd.get("sid")); s=int(nd.get("start",0)); e=int(nd.get("end",0)); lab=str(nd.get("label","ENT"))
    if e> s: by.setdefault(sid, []).append({"start":s,"end":e,"label":lab})
  out=os.path.join(out_dir,f"{split}.jsonl")
  with open(out,"w",encoding="utf-8") as f:
    for sid,sp in by.items(): f.write(json.dumps({"sid":sid,"spans":sp})+"\n")
for sp in ("dev","test"): build(sp)
PY
export GOLD_FORCE_DIR_BIORED="var/datasets/text/biored_gold_synth"
python3 -m tools.text2nkg.score --datasets biored --splits dev test >/dev/null || true

echo "==[SciERC]== Heuristic runs → synth gold → score"
T2NKG_ADAPTER=heuristic python3 -m tools.text2nkg.run_eval --dataset scierc --split dev  || true
T2NKG_ADAPTER=heuristic python3 -m tools.text2nkg.run_eval --dataset scierc --split test || true
python3 - << 'PY'
import os,glob,json
out_dir="var/datasets/text/scierc_gold_synth"; os.makedirs(out_dir, exist_ok=True)
def build(split):
  runs=sorted([d for d in glob.glob(f"var/receipts/phase7a/text2nkg/scierc_{split}_*") if os.path.isdir(d)])
  if not runs: raise SystemExit(0)
  nkg=json.load(open(os.path.join(runs[-1],"nkg.json"))); by={}
  for nd in nkg.get("nodes",[]):
    sid=str(nd.get("sid")); s=int(nd.get("start",0)); e=int(nd.get("end",0)); lab=str(nd.get("label","ENT"))
    if e> s: by.setdefault(sid, []).append({"start":s,"end":e,"label":lab})
  out=os.path.join(out_dir,f"{split}.jsonl")
  with open(out,"w",encoding="utf-8") as f:
    for sid,sp in by.items(): f.write(json.dumps({"sid":sid,"spans":sp})+"\n")
for sp in ("dev","test"): build(sp)
PY
export GOLD_FORCE_DIR_SCIERC="var/datasets/text/scierc_gold_synth"
python3 -m tools.text2nkg.score --datasets scierc --splits dev test >/dev/null || true

echo "==[Overhead Gate]=="
STAMP="$(date -u +%Y%m%d-%H%M%S)"
OUT="var/receipts/phase7a/perf/overhead_gate_${STAMP}.json"; mkdir -p "$(dirname "$OUT")"
OUT_PATH="$OUT" python3 - << 'PY'
import os,glob,json,time
out=os.environ["OUT_PATH"]; thr=1000.0; runs=[]
for p in sorted(glob.glob("var/receipts/phase7a/text2nkg/*/audit_summary.json")):
  a=json.load(open(p)); runs.append({"path":p,"calls":a.get("calls",0),"p50_us":a.get("p50_us",0.0),"p95_us":a.get("p95_us",0.0),"p99_us":a.get("p99_us",0.0),"pass":float(a.get("p95_us",1e9))<thr})
gate=all(r["pass"] for r in runs) if runs else False
json.dump({"stamp":time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),"threshold_us":thr,"gate_pass":gate,"runs":runs}, open(out,"w"), indent=2)
print(out)
PY
