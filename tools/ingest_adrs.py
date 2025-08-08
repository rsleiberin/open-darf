import glob
import os
import hashlib
import fitz
from tqdm import tqdm
from qdrant_client import QdrantClient, models
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain.embeddings.openai import OpenAIEmbeddings

COLL="adr_chunks"; PATH="docs/reference/*.pdf"
qc = QdrantClient(url=os.getenv("QDRANT_URL"))
emb = OpenAIEmbeddings()
if COLL not in [c.name for c in qc.get_collections().collections]:
    qc.create_collection(
        collection_name=COLL,
        vectors_config=models.VectorParams(size=1536, distance=models.Distance.COSINE)
    )

splitter = RecursiveCharacterTextSplitter(chunk_size=800, chunk_overlap=200)
for pdf in tqdm(glob.glob(PATH)):
    doc = fitz.open(pdf)
    text = "\n".join(page.get_text() for page in doc)
    for chunk in splitter.split_text(text):
        vec = emb.embed_query(chunk)
        uid = hashlib.md5(chunk.encode()).hexdigest()
        qc.upsert(
            collection_name=COLL,
            points=[models.PointStruct(id=uid, vector=vec,
                   payload={"pdf": os.path.basename(pdf), "text": chunk[:200]})]
        )
print("✅ Ingestion complete.")
