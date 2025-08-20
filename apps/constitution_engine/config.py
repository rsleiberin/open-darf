import os
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class Neo4jConfig:
    uri: Optional[str]
    user: Optional[str]
    password: Optional[str]


def load_config() -> Neo4jConfig:
    return Neo4jConfig(
        uri=os.getenv("NEO4J_URI"),
        user=os.getenv("NEO4J_USER"),
        password=os.getenv("NEO4J_PASSWORD"),
    )
