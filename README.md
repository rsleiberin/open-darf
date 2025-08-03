# Darf Intelligence Stack (monorepo)

A self-hosted, off-grid-capable AI platform that runs on a single fan-less PC yet can scale out to a LAN or cloud cluster when needed.

| Slot / Concern         | Locked-in Tech                                      |
|------------------------|-----------------------------------------------------|
| **Backend language**   | Python 3.12 (Poetry 2.1.3)                          |
| **Frontend language**  | TypeScript 5 (Pnpm 8)                               |
| **Frontend framework** | Next 15 · React 19 · Tailwind 4 · shadcn/UI         |
| **Message broker**     | RabbitMQ 3                                          |
| **Task queue**         | Dramatiq + Redis                                    |
| **Relational DB**      | PostgreSQL 15                                       |
| **Knowledge graph**    | Neo4j 5 (Community)                                 |
| **Vector store**       | Qdrant v1                                           |
| **Object store**       | MinIO (S3-compatible)                               |
| **Cache / Pub-sub**    | Redis 7                                             |
| **Container runtime**  | Podman 4 + Quadlet                                  |
| **CI**                 | GitHub Actions (pre-commit status check)            |

---

## Repository layout

    apps/
      backend/        # runnable Python services
      frontend/       # Next 15 full-stack app
    packages/
      shared/         # reusable Python modules
    infra/
      docker/         # Containerfile & Quadlet units
    docs/             # architecture, ADRs, research, process
    .github/          # CI workflows
    Makefile          # lint · fix · test · scan targets

---

## Quick start

### Backend service

    git clone https://github.com/rsleiberin/darf-source.git
    cd darf-source
    poetry install --no-interaction
    make lint
    make fix
    python apps/backend/main.py

### Frontend app

    cd apps/frontend
    pnpm install
    pnpm dev            # opens http://localhost:3000

---

## Roadmap & planned slots

See `docs/architecture/rar-system.md` and `docs/content/architecture/00-roadmap.md`.

Immediate next tasks  
1. PostgreSQL Quadlet unit  
2. FastAPI health endpoints + pytest  
3. CONTRIBUTING / LICENSE / CODE_OF_CONDUCT cleanup

---

## Contributing

Conventional Commits • pre-commit hooks • PR-first workflow (even while private).  
See `CONTRIBUTING.md` for details.

---

## License

To be decided – likely MIT or Apache-2.0.
