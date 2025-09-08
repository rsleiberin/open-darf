#!/usr/bin/env python3
import sys, json, pathlib, glob

SCHEMA_PATH = pathlib.Path("docs/schemas/metrics_v1.json")

def shallow_check(obj):
    required = ["dataset","split","model","precision_micro","recall_micro","f1_micro","f1_unlabeled","pred_count","gold_pairs","latency_ms"]
    missing = [k for k in required if k not in obj]
    return missing

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="var/receipts/phase7g", help="Root to search for metrics.json files")
    ap.add_argument("--strict", action="store_true", help="Require jsonschema and strict validation")
    args = ap.parse_args()

    files = glob.glob(f"{args.root}/**/metrics.json", recursive=True)
    if not files:
        print(json.dumps({"status":"warn","note":"no metrics.json found","root":args.root}))
        return 0

    try:
        import jsonschema  # type: ignore
        schema = json.loads(SCHEMA_PATH.read_text())
        use_schema = True
    except Exception:
        if args.strict:
            print(json.dumps({"status":"error","reason":"jsonschema_missing"})); return 1
        use_schema = False
        schema = None

    results = []
    rc = 0
    for fp in files:
        try:
            obj = json.loads(pathlib.Path(fp).read_text())
            if use_schema:
                jsonschema.validate(instance=obj, schema=schema)  # type: ignore
                results.append({"file":fp,"status":"ok","mode":"jsonschema"})
            else:
                miss = shallow_check(obj)
                if miss:
                    results.append({"file":fp,"status":"fail","missing":miss,"mode":"shallow"})
                    rc = 1
                else:
                    results.append({"file":fp,"status":"ok","mode":"shallow"})
        except Exception as e:
            results.append({"file":fp,"status":"error","reason":str(e)})
            rc = 1
    print(json.dumps({"status":"ok" if rc==0 else "fail","results":results}, indent=2))
    return rc

if __name__ == "__main__":
    sys.exit(main())
