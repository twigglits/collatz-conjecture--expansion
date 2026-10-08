# Project continuity

Read [MEMORY.md](MEMORY.md) at the start of a session, then
[ATTEMPT.md](ATTEMPT.md) and the notes relevant to the current user request.
The memory is a dated research handoff; source files, verification records,
and newer user instructions take precedence.

- Preserve the distinction between kernel proofs, native finite checks,
  independent Python checks, written arguments, and external dependencies.
- The positive-integer Collatz conjecture remains unresolved in this project.
  Do not report a reformulation, finite exclusion, or restricted-family
  result as a complete proof.
- Allow longer Rust and Lean runtimes on the current machine. Prefer
  sequential heavy checks and reuse completed verification when appropriate.
- The user stages and commits work while the assistant works. Preserve the
  index and existing changes; stage or commit only if explicitly asked.
- Keep credentials out of source, memory, output, and commits. See the
  credential-handling note in MEMORY.md before any necessary installation.

Keep MEMORY.md current after substantive research milestones or explicit
user requests to save project context.
