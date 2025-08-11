# Local Dev Postgres (Quickstart)

Run these from the repo root.

    make db-up           # start db (podman or docker)
    make db-psql         # open psql (\q to exit)
    make test-db         # run integration test
    make db-logs         # tail container logs
    make db-down         # stop db

The helpers read `.env` if present (`POSTGRES_USER`, `POSTGRES_PASSWORD`, `POSTGRES_DB`).
Data persists in the container volume `janus-pgdata`.
