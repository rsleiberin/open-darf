#!/usr/bin/env bash
set -euo pipefail
NET="$(docker inspect -f '{{range $k,$v := .NetworkSettings.Networks}}{{printf "%s\n" $k}}{{end}}' darf-minio-1 2>/dev/null | head -n1)"
[[ -z "$NET" ]] && { echo "[mc] cannot determine network for darf-minio-1" >&2; exit 2; }
docker run --rm --network "$NET" --name darf-mc-$$ \
  -e MC_HOST_local="http://$(docker inspect -f '{{range .Config.Env}}{{println .}}{{end}}' darf-minio-1 | awk -F= '/^MINIO_ROOT_USER=|^MINIO_ACCESS_KEY=/{print $2; exit}'):$(docker inspect -f '{{range .Config.Env}}{{println .}}{{end}}' darf-minio-1 | awk -F= '/^MINIO_ROOT_PASSWORD=|^MINIO_SECRET_KEY=/{print $2; exit}')@minio:9000" \
  minio/mc:latest "$@"
