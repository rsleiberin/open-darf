from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
import os
import typing as t
from neo4j import GraphDatabase
from langchain.embeddings import OpenAIEmbeddings
from qdrant_client import QdrantClient
from langchain_community.vectorstores import Qdrant as LCQdrant


class Query(BaseModel):
    question: str


class GraphRAGRetriever:
    def __init__(self):
        self.embed = OpenAIEmbeddings()
        self.qdrant = LCQdrant(
            client=QdrantClient(url=os.getenv("QDRANT_URL")),
            collection_name="adr_chunks",
            embeddings=self.embed,
        )
        self.driver = GraphDatabase.driver(
            os.getenv("NEO4J_URL"),
            auth=(os.getenv("NEO4J_USER"), os.getenv("NEO4J_PASSWORD")),
        )

    def query(self, q: str) -> t.Dict[str, t.Any]:

        docs = self.qdrant.similarity_search_with_score(q, k=5)
        answer = "\n".join(d.page_content for d, _ in docs)
        return {"answer": answer, "sources": [d.metadata for d, _ in docs]}


app = FastAPI()
retriever = GraphRAGRetriever()


@app.get("/health")  # acceptance for #55
def health():
    return {"ok": True}


@app.post("/rag/query")  # Issue #58
def rag_query(payload: Query):
    try:
        return retriever.query(payload.question)
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
