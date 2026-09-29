# Changelog

## v0.3.0 (unreleased, ePrint version)

### Paper
- New title: "Post-Quantum Multilinear Polynomial Commitments from FRI Folding in the Boolean-Kernel Basis" (also in README, CITATION.cff, the crate description and the project page).
- Shorter abstract; plain-text abstract, keywords, category and license for ePrint in `paper/EPRINT.md`.
- Author block with ORCID; acknowledgments with a statement on the use of generative AI tools.
- Introduction: Figure 1 (the fold dictionary as a commutative diagram), a contribution paragraph on the Lean formalisation, a scope paragraph, and the statement that the paper is self-contained.
- Scope statements in §5 (Remark on batching), §6, §7 and §8 point to the new §10.1 (Future work).
- §10: future work (soundness, zero knowledge, implementation, formal verification, other domains) and §10.2 (Artefacts: repository, release, commands to reproduce each table and check, Lean toolchain).
- Reference added: Libra (Xie et al., CRYPTO 2019).

### Rust (breaking changes)
- **Compiler of CDHZ25 (Construction 11.7).** Salted Merkle trees (leaf `H_K0(a || b || salt)`, 32-byte salts from a keyed BLAKE3 stream), one round salt per round, challenges derived from all previous roots and salts; salts from a fresh operating-system seed per commitment and per opening (`getrandom`). Transcript label `kbfold/v0.3/pcs`.
- **Quartic extension** `Fp4 = F_p[i]/(i^4 - 7)` and the trait `ExtField`; the protocol is generic in the challenge field (`Fp2` or `Fp4`).
- **Challenge maps of the paper:** `phi` from 64(e+1) bits (the integer reduced mod p^e, base-p digits), and `pos` (kappa blocks of m+R bits).
- `Params` gains `salt_len`, `new`, `classical` (148 queries, `Fp2`), `post_quantum` (248 queries, `Fp4`) and `validate`.
- `commit`, `open` and `verify` return `Result<_, Error>`; the verifier never panics on malformed proofs. `Proof` gains `round_salts`, leaf salts in each opening, and `to_bytes` (canonical encoding).
- `#![forbid(unsafe_code)]`; feature `insecure-test-vectors` (seeded provers, never for production).
- Tests: completeness in both extensions, every single mutation of a proof rejected, lengths and random truncations without panic, fresh salts, invalid parameters; test vectors in `rust/vectors/` (transcript challenges, complete proofs). CI runs the vector tests.

### Paper (with the code)
- §7: extension fields, salted trees, Fiat-Shamir by rounds, relation to the compiler of CDHZ25, proof format, tests.
- Remark 7.30 (scope), introduction and §10.1 updated: the implementation follows the compiler; the conformance item leaves the future work.
- §9: the measurements were recorded with version 0.1 (to be re-measured).

### Benchmarks
- Feature `parallel` (rayon): transforms, NTT, Merkle trees, folds and sumcheck on all cores; the proofs are identical (CI checks them against the test vectors).
- `examples/bench.rs`: modes `scaling`, `pq` (F_{p^4}, 248 queries), `salt`, `stop`, `rate`, `breakdown`; CSV with thread count. `bench/run_all.sh` runs all of them, in both threading modes, and optionally the WHIR implementation as an external reference.
- New measurements in `rust/results/vm-2cpu/`; the version 0.1 data move to `rust/results/v0.1/`.

### Paper (§9, measurements of 0.3.0)
- All tables re-measured with 0.3.0 (salted trees). New: post-quantum parameters (Table 3), cost of salts, parallel speed-up, and WHIR on the same machine (Table 6), with the three techniques behind its smaller proofs added to future work (§10.1).
- Introduction and conclusion describe the new measurements; stray characters before §10.1 removed.

### Committed levels and merged paths (proof 1147 -> 237 KiB at n = 20)
- **Committed levels** (`Params::fold_log`, k = 4 by default): the prover commits to w_0, w_k, w_2k, ...; a leaf of w_j (j > 0) holds a coset of 2^k values and the verifier folds k times locally. The commitment tree keeps one fibre per leaf, ordered so that the fibres of a coset are consecutive (the committed string and the relation are unchanged).
- **Merged paths:** the openings of one committed word are the distinct leaves in increasing order plus one merged authentication path; the verifier rejects unless every node is used exactly once.
- `Proof` now has `level0` and `levels` (`LevelOpening`: values, salts, nodes). The transcript absorbs k. Tests cover k = 1..4, all mutations of the new openings, and truncations; vectors regenerated.
- `examples/bench.rs`: mode `arity`; breakdown measures the commitment tree.

### Paper (committed levels)
- §6.3 "Committing to fewer words": committed levels J, cosets, Lemma 6.x (local folding), the protocol Pi_eval^J and Lemma 6.x (skipping commitments, a reduction to Pi_eval for every transcript).
- §7.9 "Committed levels": Theorem 7.x transfers soundness, binding, round-by-round knowledge soundness, the relaxed version (IOR over a disjoint-union alphabet, reordered implicit instance) and the post-quantum corollary with the same errors; Remark on parameters and merged paths. Reviewed by an independent pass; its corrections are included.
- Lean: new module `KBFold/Skip.lean` formalises Lemma "Skipping commitments" and Theorem "Committed levels", item 1 (soundness far and close, evaluation binding), with the same axioms as the originals; the Lean appendix, `lean/README.md` and `docs/LEAN_MAP.md` list it.
- §8 describes committed levels, leaf order and merged openings; §9 re-measured, with a new table on k; abstract and introduction give the headline numbers; notation table and Lean appendix updated.

### Docs
- `docs/ROADMAP.md`: version 1 (first ePrint submission) and version 2 (revision of the same entry).

## v0.2.0 — 2026-09-27

### License and crate
- Code under MIT OR Apache-2.0, paper under CC BY 4.0 (license files added).
- The Rust library is published on crates.io as `kbfold`: package metadata, license files in the crate, crate documentation with a tested example, `cargo doc` without warnings; CI builds the documentation, runs `cargo publish --dry-run` and builds with the minimum supported Rust version (1.85).

### Rust
- `rust/src/merkle.rs`: leaves and internal nodes are hashed with BLAKE3 in keyed mode under two fixed keys (domain separation) instead of one-byte prefixes, so that an internal node is 64 bytes, one compression. Same change as in the Kronecker-FRI implementation, which keeps the comparison of the Kronecker-FRI paper at identical engineering. The data in `rust/results/` were recorded with the earlier format.

### Paper
- §7: the Merkle hashing format; the measurements of §8 predate it.

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
