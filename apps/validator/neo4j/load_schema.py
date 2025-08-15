from pathlib import Path
from neo4j import GraphDatabase
import os, re

def main():
    uri = os.getenv("NEO4J_URI", "bolt://localhost:7687")
    user = os.getenv("NEO4J_USER", "neo4j")
    password = os.getenv("NEO4J_PASSWORD", "neo4j")
    database = os.getenv("NEO4J_DB", "neo4j")
    cypher_dir = Path(__file__).parent / "cypher"

    drv = GraphDatabase.driver(uri, auth=(user, password))
    try:
        with drv.session(database=database) as s:
            for p in sorted(cypher_dir.glob("*.cypher")):
                text = p.read_text()
                # strip block and line comments
                text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
                text = re.sub(r"//.*", "", text)
                # split on semicolons and run only non-empty statements
                for stmt in [x.strip() for x in text.split(";") if x.strip()]:
                    s.run(stmt)
                    first = stmt.splitlines()[0][:60]
                    print(f"applied: {p.name}: {first}")
    finally:
        drv.close()

if __name__ == "__main__":
    main()
