# MinIO Dev Pattern (Podman on WSL/Linux)

> Purpose: immutable originals + derived blobs, private + versioned; least-priv service user.
> Scope: local dev. SSE-S3 encryption deferred until KMS is configured.

Prereqs
    podman, curl, mc (MinIO client), jq

Start MinIO (admin defaults OK for dev; app uses a service user)
    mkdir -p "$HOME/minio/data"
    podman rm -f minio >/dev/null 2>&1 || true
    podman run -d --name minio --restart=always \
      -p 9000:9000 -p 9001:9001 \
      -v "$HOME/minio/data":/data:Z \
      -e MINIO_ROOT_USER="${MINIO_ADMIN_ACCESS_KEY:-${MINIO_ACCESS_KEY:-minioadmin}}" \
      -e MINIO_ROOT_PASSWORD="${MINIO_ADMIN_SECRET_KEY:-${MINIO_SECRET_KEY:-minioadmin}}" \
      quay.io/minio/minio server /data --console-address ":9001"
    curl -fsS "${MINIO_URL:-http://127.0.0.1:9000}/minio/health/ready" -o /dev/null && echo "MinIO is ready."

Admin alias (uses MINIO_ACCESS_KEY/SECRET_KEY from .env for now)
    mc alias set darf-admin "${MINIO_URL:-http://127.0.0.1:9000}" "${MINIO_ACCESS_KEY}" "${MINIO_SECRET_KEY}"

Buckets (private, versioned; encryption deferred)
    for b in "${MINIO_BUCKET_ORIGINALS:-darf-originals}" "${MINIO_BUCKET_DERIVED:-darf-derived}" "${MINIO_BUCKET_REPORTS:-darf-reports}"; do
      mc mb "darf-admin/$b" 2>/dev/null || true
      mc anonymous set none "darf-admin/$b"
      mc version enable      "darf-admin/$b"
    done

Least-priv policy (RW; no delete) and service user
    POLICY='{"Version":"2012-10-17","Statement":[
      {"Sid":"List","Effect":"Allow","Action":["s3:ListAllMyBuckets","s3:GetBucketLocation"],"Resource":["arn:aws:s3:::*"]},
      {"Sid":"Originals","Effect":"Allow","Action":["s3:ListBucket","s3:GetObject","s3:PutObject"],"Resource":["arn:aws:s3:::darf-originals","arn:aws:s3:::darf-originals/*"]},
      {"Sid":"Derived","Effect":"Allow","Action":["s3:ListBucket","s3:GetObject","s3:PutObject"],"Resource":["arn:aws:s3:::darf-derived","arn:aws:s3:::darf-derived/*"]},
      {"Sid":"Reports","Effect":"Allow","Action":["s3:ListBucket","s3:GetObject","s3:PutObject"],"Resource":["arn:aws:s3:::darf-reports","arn:aws:s3:::darf-reports/*"]}
    ]}'
    printf '%s\n' "$POLICY" > /tmp/darf-ingest-rw.json
    mc admin policy create darf-admin darf-ingest-rw /tmp/darf-ingest-rw.json
    SVC_USER="darf-ingester"; SVC_SECRET="$(tr -dc 'A-Za-z0-9' </dev/urandom | head -c 40)"
    mc admin user add darf-admin "$SVC_USER" "$SVC_SECRET"
    mc admin policy attach darf-admin darf-ingest-rw --user "$SVC_USER"
    mc alias set darf "${MINIO_URL:-http://127.0.0.1:9000}" "$SVC_USER" "$SVC_SECRET"

Rotate .env to service creds (preserve admin as MINIO_ADMIN_*)
    cp .env ".env.bak.$(date +%Y%m%d-%H%M%S)"
    OLD_AK="$(grep -E '^MINIO_ACCESS_KEY=' .env | sed 's/^[^=]*=//')"
    OLD_SK="$(grep -E '^MINIO_SECRET_KEY=' .env | sed 's/^[^=]*=//')"
    grep -q '^MINIO_ADMIN_ACCESS_KEY=' .env || echo "MINIO_ADMIN_ACCESS_KEY=$OLD_AK" >> .env
    grep -q '^MINIO_ADMIN_SECRET_KEY=' .env || echo "MINIO_ADMIN_SECRET_KEY=$OLD_SK" >> .env
    sed -i -E "s/^MINIO_ACCESS_KEY=.*/MINIO_ACCESS_KEY=$SVC_USER/" .env
    sed -i -E "s/^MINIO_SECRET_KEY=.*/MINIO_SECRET_KEY=$SVC_SECRET/" .env

Smoke test (hash-address)
    tmp="$(mktemp)"; printf 'minio smoke %s\n' "$(date -Iseconds)" > "$tmp"
    sha="$(sha256sum "$tmp" | awk '{print $1}')"
    mc cp "$tmp" "darf/${MINIO_BUCKET_ORIGINALS:-darf-originals}/sha256/$sha"
    diff <(mc cat "darf/${MINIO_BUCKET_ORIGINALS:-darf-originals}/sha256/$sha") "$tmp" && echo "smoke OK"

SSE-S3 Encryption
    Requires KMS (KES or Vault). Track as a follow-up; enable with `mc encrypt set sse-s3 ...` after KMS config.

Env keys referenced
    MINIO_URL, MINIO_ACCESS_KEY, MINIO_SECRET_KEY,
    MINIO_ADMIN_ACCESS_KEY, MINIO_ADMIN_SECRET_KEY,
    MINIO_BUCKET_ORIGINALS, MINIO_BUCKET_DERIVED, MINIO_BUCKET_REPORTS
