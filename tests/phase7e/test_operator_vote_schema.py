def test_vote_resolution_rules(tmp_path):
    import json, subprocess, sys, pathlib
    vote = {
        "version":"vote_schema_v1",
        "decision_context":{"id":"t1","description":"test"},
        "votes":[
            {"principle":"A","decision":"ALLOW","weight":0.6,"rationale":"x"}
        ]
    }
    f = tmp_path/"vote.json"
    f.write_text(json.dumps(vote), encoding="utf-8")
    exe = pathlib.Path("tools/constitutional/reasoning/validate_votes.py")
    out = subprocess.check_output([sys.executable, str(exe), str(f)])
    assert b"ACCEPTABLE" in out
