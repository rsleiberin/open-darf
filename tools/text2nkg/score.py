import os, json, glob, argparse, time
from typing import Dict, Any, List, Tuple
from tools.text2nkg.gold_utils import discover_gold

def strict_match(pred, gold, ignore_label=True):
    tp=0
    used=[False]*len(gold)
    for s,e,l in pred:
        for j,(gs,ge,gl) in enumerate(gold):
            if used[j]: continue
            if s==gs and e==ge and (ignore_label or l==gl):
                used[j]=True; tp+=1; break
    fp = len(pred) - tp
    fn = len(gold) - tp
    return tp,fp,fn

def prf1(tp,fp,fn):
    p = (tp/(tp+fp)) if (tp+fp)>0 else 0.0
    r = (tp/(tp+fn)) if (tp+fn)>0 else 0.0
    f1 = (2*p*r/(p+r)) if (p+r)>0 else 0.0
    return {"precision": p, "recall": r, "f1": f1}

def load_pred_by_sid(run_dir: str) -> Tuple[str,str,Dict[str,List[Tuple[int,int,str]]]]:
    nkg_path=os.path.join(run_dir,"nkg.json")
    nkg=json.load(open(nkg_path))
    run=nkg.get("run",{})
    dataset=run.get("dataset","?")
    split=run.get("split","?")
    by_sid={}
    for nd in nkg.get("nodes",[]):
        sid=str(nd.get("sid"))
        by_sid.setdefault(sid, []).append((int(nd.get("start",0)), int(nd.get("end",0)), str(nd.get("label","ENT"))))
    return dataset, split, by_sid

def score_run(run_dir: str, ignore_sid: bool=False) -> Dict[str,Any]:
    dataset, split, pred_by_sid = load_pred_by_sid(run_dir)
    gold_path, gold = discover_gold(dataset, split)
    if not gold:
        out={"dataset":dataset,"split":split,"scored":False,"reason":"gold_not_found_or_empty","gold_path":gold_path}
        json.dump(out, open(os.path.join(run_dir,"scores.json"),"w"), indent=2)
        return out
    tp=fp=fn=0
    if ignore_sid:
        all_pred=[x for xs in pred_by_sid.values() for x in xs]
        all_gold=[x for xs in gold.values() for x in xs]
        tp,fp,fn = strict_match(all_pred, all_gold, ignore_label=True)
    else:
        for sid, pred in pred_by_sid.items():
            a,b,c = strict_match(pred, gold.get(sid, []), ignore_label=True)
            tp+=a; fp+=b; fn+=c
    metrics=prf1(tp,fp,fn)
    out={"dataset":dataset,"split":split,"tp":tp,"fp":fp,"fn":fn,
         "entities_strict_span":metrics,"scored":True,
         "gold_path":gold_path,"gold_sids":len(gold),"pred_sids":len(pred_by_sid)}
    json.dump(out, open(os.path.join(run_dir,"scores.json"),"w"), indent=2)
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--datasets", nargs="+", default=["biored","scierc"])
    ap.add_argument("--splits",   nargs="+", default=["dev","test"])
    ap.add_argument("--ignore-sid", action="store_true")
    args=ap.parse_args()

    results=[]
    base="var/receipts/phase7a/text2nkg"
    for ds in args.datasets:
        for sp in args.splits:
            cands = sorted([d for d in glob.glob(os.path.join(base, f"{ds}_{sp}_*")) if os.path.isdir(d)])
            if not cands:
                results.append({"dataset":ds,"split":sp,"error":"no_run_found"}); continue
            results.append(score_run(cands[-1], ignore_sid=args.ignore_sid))
    stamp=os.environ.get("STAMP") or time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outp=f"var/receipts/phase7a/text2nkg/scoreboard_{stamp}.json"
    os.makedirs(os.path.dirname(outp), exist_ok=True)
    with open(outp,"w") as f: json.dump({"stamp":stamp,"results":results}, f, indent=2)
    print(outp)

if __name__=="__main__":
    main()
