from __future__ import annotations

import json
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any

from solver_runtime_sandbox.models import Stage2Problem

DEFAULT_PROOF_POLICY: dict[str, list[str]] = {
    "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "allowed_declarations": ["letFun"],
    "allowed_declaration_prefixes": [
        "And.",
        "Bool.",
        "Classical.",
        "Decidable.",
        "Eq.",
        "EquationLHS",
        "EquationRHS",
        "Goal",
        "Exists.",
        "False.",
        "Fin.",
        "Fintype.",
        "Function.",
        "HEq.",
        "Iff.",
        "Init.",
        "Int.",
        "Lean.",
        "List.",
        "Magma.",
        "Mathlib.",
        "MemoFinOp.",
        "Nat.",
        "Nonempty.",
        "Not.",
        "NthRewrites.",
        "OfNat.",
        "Option.",
        "Or.",
        "Prod.",
        "PUnit.",
        "RewriteCombinations.",
        "RewriteGoal.",
        "RewriteHypothesis.",
        "RewriteHypothesisAndGoal.",
        "SimpleRewrites.",
        "Std.",
        "Subgraph.",
        "Subtype.",
        "Sum.",
        "Trans.",
        "True.",
        "Unit.",
        "JudgeDecide.",
        "JudgeFinOp.",
        "JudgeMagma.",
        "inst",
        "of_decide_",
        "submission.",
        "congrArg",
        "congr_arg",
        "eq_self",
        "of_eq_true",
        "id",
        "eq_comm",
        "eq_mp",
        "eq_mpr",
        "rfl",
        "absurd",
    ],
}

JUDGE_PROBLEM_FIELDS = {
    "id",
    "eq1_id",
    "eq2_id",
    "equation1",
    "equation2",
    "proof_policy",
}


@dataclass(frozen=True)
class JudgeV3Client:
    base_url: str
    request_timeout_seconds: int = 330
    lean_timeout_seconds: int = 300

    def health(self) -> dict[str, Any]:
        return self._request("GET", f"{self.base_url.rstrip('/')}/health")

    def verify(
        self,
        *,
        problem: Stage2Problem,
        verdict: str,
        code: str,
        lean_timeout_seconds: int | None = None,
    ) -> dict[str, Any]:
        active_lean_timeout = max(
            1,
            min(
                self.lean_timeout_seconds,
                lean_timeout_seconds or self.lean_timeout_seconds,
            ),
        )
        # Dataset rows may carry bookkeeping fields because Stage2Problem allows
        # extras.  The judge schema is deliberately strict, so only forward the
        # public Stage 2 problem contract.
        problem_payload = problem.model_dump(
            include=JUDGE_PROBLEM_FIELDS,
            exclude_none=True,
        )
        problem_payload.setdefault("proof_policy", DEFAULT_PROOF_POLICY)
        payload = {
            "problem": problem_payload,
            "verdict": verdict,
            "code": code,
            "timeout_seconds": active_lean_timeout,
        }
        return self._request(
            "POST",
            f"{self.base_url.rstrip('/')}/verify",
            payload,
            timeout_seconds=min(self.request_timeout_seconds, active_lean_timeout + 30),
        )

    def _request(
        self,
        method: str,
        url: str,
        payload: dict[str, Any] | None = None,
        *,
        timeout_seconds: int | None = None,
    ) -> dict[str, Any]:
        data = None
        headers: dict[str, str] = {}
        if payload is not None:
            data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
            headers["Content-Type"] = "application/json"
        request = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(
                request, timeout=timeout_seconds or self.request_timeout_seconds
            ) as response:
                decoded = json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", errors="replace")[:2000]
            raise RuntimeError(f"judge-v3 HTTP {exc.code}: {body}") from exc
        except (OSError, TimeoutError, json.JSONDecodeError) as exc:
            raise RuntimeError(f"judge-v3 request failed: {type(exc).__name__}: {exc}") from exc
        if not isinstance(decoded, dict):
            raise RuntimeError("judge-v3 returned a non-object response")
        return decoded
