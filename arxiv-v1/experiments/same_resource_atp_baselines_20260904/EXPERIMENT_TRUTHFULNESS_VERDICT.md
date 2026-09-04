# Experiment truthfulness verdict

Verdict: suitable for public release as a bounded same-resource ATP comparison.

The released evidence supports the reported per-tool terminal counts, the
order5 and ALPS4141 source-separated tables, the 94-theorem/4-counter ALPS4141
union, and the exact/normalized overlap audits. It also supports the statement
that Vampire and E emitted raw counter text that is scientifically
nondecisive under these proving configurations.

The artifact does not support claims that an unsolved problem is ATP-hard or
ATP-unsolvable; that a Twee counter is an explicit finite or infinite model;
or that ATP output has been checked by Lean/Judge v3. Those stronger claims are
explicitly excluded throughout the release.

All solver executions were remote. The public package omits provider lifecycle
logs, sandbox IDs, credentials, and absolute private paths. Published payloads
are limited to decisive results, raw counter evidence, and the frozen focus28
subset; hashes and sizes remain for every omitted nondecisive stream.

