#!/usr/bin/env bash
set -euo pipefail
docker run --rm --network "darf_net"   -e MC_HOST_local="http://admin:adminadmin@minio:9000"   -v "/home/tank/darf-source:/host:ro"   --name darf-mc-$$ minio/mc:latest "$@"
