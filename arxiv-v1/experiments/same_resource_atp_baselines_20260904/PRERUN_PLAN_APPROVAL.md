# Pre-run plan and approval

Status: explicitly approved by the user on 2026-09-04.

| Experiment | Claim supported | Essential? | Estimated runtime | Disk | Compute/cost | External data | Decision |
|---|---|---:|---:|---:|---|---|---|
| Vampire 5.0.1, 4,271 records | Same-resource ATP comparison | yes | 1--1.5 h | <2 GB private raw; compressed public subset | 150 remote 2-vCPU/2-GiB Sandboxes, provider-account cost | none; frozen local benchmark and pinned binary | approved |
| E 3.5.1, 4,271 records | Same-resource ATP comparison | yes | 1--1.5 h | <2 GB private raw; compressed public subset | same | none | approved |
| Twee 2.6.1, parameter-free complete search, 4,271 records | ALPS-aligned same-resource ATP comparison | yes | 1--1.5 h | <2 GB private raw; compressed public subset | same | none | approved |

Worst-case aggregate solver work is 12,813 × 120 seconds.  With 150 concurrent
Sandboxes used sequentially per ATP, the pure-compute lower bound is about 2.85
hours. Including creation, transfer, cleanup, postprocessing, and bounded
infrastructure retries, the expected wall-clock range is 3--5 hours.

No external dataset is downloaded.  The three pinned ATP binaries are already
available locally and are used only in remote Sandboxes.  Their binary hashes
must match the preregistered manifest before any run starts.
