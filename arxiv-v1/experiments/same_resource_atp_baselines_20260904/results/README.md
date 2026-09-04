# Results layout

- `atp/summary.json`: authoritative aggregate results and resource statistics.
- `atp/*/per_problem_results.jsonl.gz`: all sanitized per-problem rows.
- `atp/*/status_evidence_streams.jsonl.gz`: complete output streams for every
  theorem and every raw/trusted counter record.
- `atp/*/focus28_streams.jsonl.gz`: complete streams for the frozen focus set.
- `atp/by_source/`: Austin96, Generality34, and ALPS4141 splits.
- `atp/deduplicated/`: exact and normalized unique-problem audit views.
- `input_overlap/`: independent overlap calculation from equation trees.
- `alps_etp_coverage/`: ALPS corpus-layer membership audit.

Use `../scripts/verify_results.py`; do not manually add the 130- and
4141-record denominators because they overlap.

