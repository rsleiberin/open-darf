# RTX 3080 (12 GB) — Memory & Latency Strategy

_Commit:_ a821dfa  •  _Generated:_ 2025-09-01T23:30:30Z

## Objectives
- Keep constitutional validation at ~sub-millisecond latency per check by design (hermetic, small I/O footprint).
- Enable local fine-tuning experiments within 12 GB constraints while keeping CI hermetic (CI remains receipt-driven).

## Inference (small heads / classical components)
- Prefer fp16/bf16 where supported; fall back to fp32 for numerically sensitive ops.
- Static batch sizing; cap sequence/context windows to bounded sizes for relation candidate scoring.
- Use pinned memory and preallocated workspaces to avoid allocator churn.

## Fine-tuning Options (future phases; **not** CI)
- Parameter-efficient tuning (LoRA/QLoRA) to fit in 12 GB.
- Gradient checkpointing; micro-batching; offload optimizer states to CPU when needed.
- ZeRO-2 style partitioning if moving beyond single-GPU (out of scope for CI).

## Data Movement & I/O
- Keep artifacts small (JSON summaries); avoid large tensor artifacts in repo/CI.
- Serialize deterministic receipts only; training artifacts remain local.

## Measurement Plan
- Add local-only microbenchmarks (not in CI) to time:
  - relation candidate gen
  - relation scoring pass
  - constitutional invariant checks

## Risk Notes
- Kernel drift across drivers can affect timings; receipts capture numbers but CI gates only check presence/thresholds.
- Avoid device-specific assumptions inside CI code paths.
