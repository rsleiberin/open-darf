from typing import List


def optional_index_cypher() -> List[str]:
    return [
        "CREATE LOOKUP INDEX node_label_lookup IF NOT EXISTS FOR (n) ON EACH labels(n)",
        "CREATE LOOKUP INDEX rel_type_lookup IF NOT EXISTS FOR ()-[r]-() ON EACH type(r)",
        "CREATE INDEX principal_id_idx IF NOT EXISTS FOR (p:Principal) ON (p.id)",
        "CREATE INDEX action_id_idx IF NOT EXISTS FOR (a:Action) ON (a.id)",
        "CREATE INDEX resource_id_idx IF NOT EXISTS FOR (r:Resource) ON (r.id)",
    ]


def dry_run() -> List[str]:
    return optional_index_cypher()
