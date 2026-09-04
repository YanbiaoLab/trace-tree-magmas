from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, field_validator

MAX_SOLVER_BYTES = 500_000
MAX_LEAN_CODE_BYTES = 100_000
MAX_FALSE_CERT_BYTES = 20_000


class Stage2Problem(BaseModel):
    model_config = ConfigDict(extra="allow")

    id: str
    eq1_id: int
    eq2_id: int
    equation1: str
    equation2: str
    proof_policy: dict[str, Any] | None = None

    @field_validator("id", "equation1", "equation2")
    @classmethod
    def _non_empty(cls, value: str) -> str:
        value = value.strip()
        if not value:
            raise ValueError("must not be empty")
        return value


class JudgeAttempt(BaseModel):
    verdict: str | None
    code: str
    response: dict[str, Any]
    metadata: dict[str, Any] | None = None


class SandboxCreateErrorRecord(BaseModel):
    attempt: int
    error_type: str
    error: str
    retryable: bool
    will_retry: bool
    backoff_seconds: float = 0.0


class SandboxRunResult(BaseModel):
    run_id: str
    sandbox_id: str | None
    problem_id: str
    status: Literal[
        "accepted",
        "generated",
        "rejected",
        "solver_exit",
        "solver_timeout",
        "protocol_error",
        "infrastructure_error",
    ]
    solved: bool
    verdict: Literal["true", "false"] | None = None
    code: str | None = None
    judge_calls: int = 0
    llm_calls: int = 0
    create_attempts: int = 0
    create_errors: list[SandboxCreateErrorRecord] = Field(default_factory=list)
    create_elapsed_seconds: float = 0.0
    attempts: list[JudgeAttempt] = Field(default_factory=list)
    elapsed_seconds: float
    solver_elapsed_seconds: float | None = None
    judge_elapsed_seconds: float = 0.0
    judge_remote_elapsed_seconds: float = 0.0
    solver_exit_code: int | None = None
    protocol_log: list[str] = Field(default_factory=list)
    stderr_tail: str = ""
    memory_profile: dict[str, Any] | None = None
    error: str | None = None
