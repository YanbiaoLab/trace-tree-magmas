# Privacy scan report

Scope: every file in this release artifact.

The release verifier checks structured results recursively for forbidden raw
fields, including Sandbox IDs, campaign run IDs, control job IDs, private
backend URLs, submission timestamps, embedded code, and raw stdout/stderr.  It
also scans text for local Windows paths, private-IP URLs, concrete Sandbox
instance IDs, and non-placeholder credential assignments.

Expected configuration variable names and placeholder values in
`runner/.env.example` are public interface documentation, not credentials.
Actual `.env` files, private CA certificates, provider credentials, internal
endpoints, persistent Sandbox pool files, and raw controller/Judge logs are
excluded.

Final automated result: zero privacy-pattern hits and zero forbidden structured
result fields.  Re-run `python scripts/verify_release.py` after any edit.
