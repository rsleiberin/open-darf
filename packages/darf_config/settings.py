"""
DARF Config Surface — Pydantic BaseSettings (v1-compatible)
Prefixes: DB_, API_, LLM_
Note: If pydantic is not installed in runtime, a graceful fallback prints a warning.
"""
from typing import Optional, Literal
import os, json

try:
    from pydantic import BaseSettings, Field, ValidationError  # type: ignore
except Exception:  # pydantic not installed
    BaseSettings = object  # type: ignore
    ValidationError = Exception  # type: ignore

class Settings(BaseSettings):  # type: ignore
    # Database (Neo4j)
    DB_HOST: str = "localhost"
    DB_PORT: int = 7687
    DB_USER: str = "neo4j"
    DB_PASSWORD: Optional[str] = None
    DB_SCHEME: Literal["neo4j","bolt"] = "neo4j"

    # API surface
    API_HOST: str = "0.0.0.0"
    API_PORT: int = 8000

    # LLM provider
    LLM_PROVIDER: Literal["none","openai","anthropic","azure_openai","vertex_ai"] = "none"
    LLM_API_KEY: Optional[str] = None

    class Config:  # pydantic v1
        env_prefix = ""  # use explicit prefixes per field
        case_sensitive = False

def load_settings() -> "Settings":
    try:
        return Settings()  # type: ignore
    except NameError:
        # pydantic missing
        print(json.dumps({"status":"warn","reason":"pydantic_missing","note":"Install pydantic to validate config"}))
        return Settings()  # type: ignore
    except ValidationError as e:  # type: ignore
        print(json.dumps({"status":"error","errors":json.loads(e.json())}))
        raise
