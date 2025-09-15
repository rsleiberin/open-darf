FROM python:3.7-bullseye

# System deps
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential git curl ca-certificates unzip && \
    rm -rf /var/lib/apt/lists/*

# Pin legacy toolchain compatible with older packages
RUN python -m pip install --upgrade pip==22.3.1 wheel==0.38.4 setuptools==59.8.0

WORKDIR /app
COPY . /app

# Install CPU torch first from the official CPU index, then the rest
RUN pip install --no-cache-dir -f https://download.pytorch.org/whl/cpu/torch_stable.html \
      torch==1.4.0+cpu && \
    pip install --no-cache-dir -r requirements.txt && \
    python -m spacy download en_core_web_sm || true

# Prefetch pretrained SciERC checkpoints used by PURE's evaluation recipes
RUN mkdir -p /app/scierc_models && \
    curl -L -o /tmp/ent-scib-ctx0.zip https://nlp.cs.princeton.edu/projects/pure/scierc_models/ent-scib-ctx0.zip && \
    curl -L -o /tmp/rel-scib-ctx0.zip https://nlp.cs.princeton.edu/projects/pure/scierc_models/rel-scib-ctx0.zip && \
    unzip -q /tmp/ent-scib-ctx0.zip -d /app/scierc_models && rm -f /tmp/ent-scib-ctx0.zip && \
    unzip -q /tmp/rel-scib-ctx0.zip -d /app/scierc_models && rm -f /tmp/rel-scib-ctx0.zip

# Helper entrypoint that writes predictions to /out/predictions.json
COPY docker_run_scierc.sh /usr/local/bin/docker_run_scierc.sh
RUN chmod +x /usr/local/bin/docker_run_scierc.sh

ENTRYPOINT ["/usr/local/bin/docker_run_scierc.sh"]
