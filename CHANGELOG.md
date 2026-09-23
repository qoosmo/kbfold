# Changelog

## v0.1.0 — 2026-09-23
First public release: paper, Lean formalisation and Rust implementation.

### Paper
- Self-contained version (55 pages), rewritten section by section with notation table (Appendix A) and Lean map (Appendix B).
- **Post-quantum security** now rests on published theorems (Chiesa–Di–Hu–Zheng, ePrint 2025/2166, Theorems 6.10, 8.3, 11.3) instead of an assumption:
  - new §3.5, which restates the definitions (relaxed RBR knowledge soundness, committed relations) and gives the specialised concrete bound (Thm 3.16);
  - new §7.7, which proves relaxed RBR knowledge soundness for the protocol as an interactive oracle reduction, including partial strings produced by the extractor (erasures, Lemma 7.24);
  - post-quantum parameters recomputed with explicit constants (κ = 248, 256-bit hash, error < 2^−31.8 at 2^64 queries).
- Round errors are required to be non-negative in Defs 3.6–3.7. Lemma 3.8 is false without this; the gap was found by the Lean formalisation.

### Lean
- 16 modules, about 7,000 lines, no `sorry`, one axiom (BCIKS correlated agreement).

### Rust
- `kbfold` crate: Goldilocks field and quadratic extension, NTT, Merkle trees, PCS in kernel and coefficient form.
- Tests, 76 numerical paper checks, benchmarks, and an exact post-quantum parameter computation (`pq_params`).
