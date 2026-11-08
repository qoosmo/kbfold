# Locked completion plan — Chapters 12–15

This project has exactly **four remaining major manuscript blocks** after Chapters 1–11. No new numbered chapters or independent research tracks are permitted without an explicit change of scope.

| Chapter | Deliverable | Acceptance criterion |
|---|---|---|
| **12 — Global Temporal Extraction and Soundness** | One coherent classical extraction strategy for every registered bit commitment and affine parity proof, retaining a single real transcript and the independence of both outer Ring Switching challenges; quantitative soundness reduction | Theorem with explicit reset/replay model, per-run extraction failure, discrete-log reduction, algebraic error and external oracle error; Rust checks; Lean dependency map |
| **13 — Complete Masked KBFold Protocol** | The original odd-characteristic KBFold PCS, commitments, authenticated fold oracles, masked Sumcheck, all opening messages and a typed simulator interface | End-to-end prover/verifier pseudocode, explicit randomness schedule and adaptive transcript; no missing verifier checks |
| **14 — Final Security Theorems** | Completeness, proximity soundness, zero-knowledge simulation, composition and model-specific claims | Each theorem either has a full proof with its hypotheses or a named exact unresolved lemma, together with a complete error budget; no unjustified transfer from characteristic 2 to odd characteristic |
| **15 — Lean and Rust Certification / Final Audit** | Mechanization map, executable tests, costs, references, consistency and final document | Compiled and audited sources, proof-ledger and certification status for every theorem, downloadable PDF/LaTeX archive |

## Non-expansion rule

- No Chapter 16 or later.
- New lemmas and arguments belong to one of the four blocks or its appendices.
- Avoid stand-alone chapters for bibliographic context, small algebraic checks, code tutorials or speculation.
- Stage 12's extraction theorem is the immediate critical path; if a concrete obstruction remains, give the exact obstruction and bound instead of creating an additional chapter.
- Distinguish source mathematical proofs, machine-checked Lean proofs, and conditional external cryptographic assumptions.
- Preserve the public manuscript in `paper/zk-extension/` and CI regression tests.

**Version:** locked by project scope decision, 2026-11-08.
