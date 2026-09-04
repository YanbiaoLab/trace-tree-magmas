# Experiment plan

## Question

Measure Vampire, E, and ALPS-aligned Twee completion on the same frozen
equational implications under a common remote-sandbox resource protocol. This
comparison describes observed capability under the stated implementation and
budget; it is not evidence that unsolved problems are mathematically
intractable.

## Inputs

- order5: 130 records = Austin96 (96) + Generality34 (34).
- ALPS4141: 4141 records.
- execution file: their 4271-record concatenation.

The source-specific denominators are primary. Exact and alpha-normalized
deduplications of the concatenation are secondary audit views.

## Resources

- remote sandbox only;
- 2 logical CPUs and 2048 MiB sandbox memory;
- 120 seconds of solver time per problem and tool;
- 2000 MiB aggregate RSS across the complete solver process group;
- 0.05-second RSS sampling;
- wrapper startup, cleanup, and RPC time recorded outside solver time;
- requested concurrency 150, with actual ready pools reported;
- 16 MiB per stdout/stderr stream and bounded infrastructure retries.

## Programs

Commands, versions, archive hashes, and binary hashes are frozen in
`config/run_config.json` and `config/tool_sources.json`. Twee uses the default
parameter-free complete search used by ALPS. Its only extra option is
`--formal-proof`, needed to retain a complete proof block when it proves a
theorem.

## Terminal classification

A theorem requires a clean exit, a success SZS status, and exactly one complete
proof block. Wrapper timeouts and memory kills cannot be overridden by solver
text. Mutually incompatible trusted terminal statuses are audit failures.

Vampire/E counters are raw-only because these runs use incomplete `triv`
proving strategies. A clean `CounterSatisfiable` from the parameter-free Twee
completion is trusted. Full details are in
`COUNTER_SATISFIABLE_POLICY.md`.

## Publication boundary

Controller lifecycle logs, sandbox identifiers, and provider errors remain
private. Public per-problem rows retain stream hashes and byte counts. Complete
compressed payloads are retained for every theorem, every raw or trusted
counter status, and all 28 frozen focus records. The public verifier checks the
manifest and scans for private paths, credentials, and sandbox identifiers.

