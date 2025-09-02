import os, json
from typing import Dict, Any, Iterable, List, Tuple, Optional

SID_KEYS = ("sid","sentence_id","sent_id","id","index","doc_id")
SPAN_LIST_KEYS = (
    "entities","spans","mentions","gold","gold_entities","gold_spans",
    "concept_mentions","annotations","ann"
)
START_KEYS = ("start","span_start","char_start","begin","offset_start","start_offset")
END_KEYS   = ("end","span_end","char_end","finish","offset_end","end_offset")
LABEL_KEYS = ("label","type","entity_group","tag","category")

def pick_first(obj: Dict[str,Any], keys: Iterable[str], default=None):
    for k in keys:
        if k in obj: return obj[k]
    return default

def extract_spans(obj: Dict[str,Any]) -> List[Tuple[int,int,str]]:
    spans = pick_first(obj, SPAN_LIST_KEYS, [])
    out: List[Tuple[int,int,str]] = []
    if isinstance(spans, dict):
        # Some schemas nest under a key
        for v in spans.values():
            if isinstance(v, list):
                for e in v:
                    out.extend(extract_spans({"_": e}))
        return out
    if not isinstance(spans, list):
        return out
    for e in spans:
        # handle tuple/list formats like [s,e] or [s,e,label]
        if not isinstance(e, dict):
            try:
                if isinstance(e, (list,tuple)) and len(e)>=2:
                    s=int(e[0]); t=int(e[1]); lab=str(e[2]) if len(e)>=3 else "ENT"
                    if s>=0 and t>=0:
                        out.append((s,t,lab))
                        continue
            except Exception:
                pass
            continue
        # nested containers: offsets/location/char_span
        if "offsets" in e and isinstance(e["offsets"], dict):
            try:
                s=int(e["offsets"].get("start", -1)); t=int(e["offsets"].get("end",-1))
                lab=str(e.get("label", e.get("type","ENT")))
                if s>=0 and t>=0:
                    out.append((s,t,lab)); continue
            except Exception:
                pass
        for key in ("location","char_span","span","pos"):
            if key in e and isinstance(e[key], (list,tuple)) and len(e[key])>=2:
                try:
                    s=int(e[key][0]); t=int(e[key][1]); lab=str(e.get("label", e.get("type","ENT")))
                    if s>=0 and t>=0:
                        out.append((s,t,lab)); 
                        continue
                except Exception:
                    pass

        if not isinstance(e, dict): continue
        s = pick_first(e, START_KEYS, -1)
        t = pick_first(e, END_KEYS, -1)
        try:
            s = int(s); t = int(t)
        except Exception:
            continue
        if s < 0 or t < 0: continue
        lab = pick_first(e, LABEL_KEYS, "ENT")
        out.append((s,t,str(lab)))
    return out

def extract_sid(obj: Dict[str,Any], i_fallback: int) -> str:
    sid = pick_first(obj, SID_KEYS, i_fallback)
    try:
        return str(int(sid))
    except Exception:
        return str(sid)

def load_gold_jsonl(path: str) -> Dict[str, List[Tuple[int,int,str]]]:
    gold: Dict[str, List[Tuple[int,int,str]]] = {}
    with open(path, "r", encoding="utf-8") as f:
        for i, line in enumerate(f):
            try:
                obj = json.loads(line)
            except Exception:
                continue
            sid = extract_sid(obj, i)
            spans = extract_spans(obj)
            if spans:
                gold.setdefault(sid, []).extend(spans)
    return gold

def discover_gold(dataset: str, split: str) -> Tuple[Optional[str], Dict[str, List[Tuple[int,int,str]]]]:
    # Env override (directory with {split}.jsonl)
    force_dir = None
    if dataset == "biored":
        force_dir = os.environ.get("GOLD_FORCE_DIR_BIORED")
    elif dataset == "scierc":
        force_dir = os.environ.get("GOLD_FORCE_DIR_SCIERC")
    if force_dir:
        p = os.path.join(force_dir, f"{split}.jsonl")
        if os.path.exists(p):
            g = load_gold_jsonl(p)
            if sum(len(v) for v in g.values()) > 0:
                return p, g

    candidates: List[str] = []
    if dataset == "biored":
        candidates += [
            f"var/datasets/text/biored_by_sentence/{split}.jsonl",
            f"var/datasets/normalized/biored_concept/{split}.jsonl",
            f"var/datasets/biored/{split}.jsonl",
        ]
    else:
        candidates += [
            f"var/datasets/text/scierc_by_sentence/{split}.jsonl",
            f"var/datasets/normalized/scierc/{split}.jsonl",
        ]
    for pth in candidates:
        if not os.path.exists(pth): continue
        gold = load_gold_jsonl(pth)
        total = sum(len(v) for v in gold.values())
        if total > 0:
            return pth, gold
    for pth in candidates:
        if os.path.exists(pth):
            return pth, {}
    return None, {}
