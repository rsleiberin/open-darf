# syntax=docker/dockerfile:1
FROM python:3.12-slim AS base

WORKDIR /app

# install Poetry inside the image
RUN pip install --no-cache-dir poetry

# copy metadata first to leverage Docker layer-cache
COPY pyproject.toml poetry.lock ./
RUN poetry config virtualenvs.create false \
 && poetry install --no-interaction --no-dev --no-root

# copy source code
COPY apps ./apps
COPY packages ./packages

CMD ["python", "apps/backend/main.py"]
