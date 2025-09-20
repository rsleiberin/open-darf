# Contributing to open-darf

Thanks for helping peers verify systems locally.

- Use **tildes (~~~)** for code fences (avoid backticks).
- Keep scripts **cancel-safe** (trap Ctrl-C) and show **heartbeats** every ~2s.
- Prefer **cwd-agnostic** paths (resolve repo root at runtime).
- Add receipts for any non-trivial operation to `results/`.

## Dev loop
~~~bash
bash ./scripts/run.sh
bash ./scripts/validator_acceptance.sh
~~~
