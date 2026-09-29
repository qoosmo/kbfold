# Roadmap

Planned directions for turning KBFold into a full R&D project. Items are ordered by dependency, not by date.

## Version 1 (first ePrint submission)
The paper as released with the code and Lean files of the tagged release (paper §10.2): kernel basis, fold dictionary, PCS, unique-decoding soundness, post-quantum corollary, Lean formalisation, reference implementation.

## Version 2 (revision of the same ePrint entry)
The items of paper §10.1 that change the main results:
- **List decoding:** soundness and round-by-round knowledge soundness up to the Johnson bound; fewer queries in both the classical and the post-quantum parameters.
- **Batched and repeated openings:** proof for the batched opening of Remark 6.7 and several openings of one commitment.
- **Zero knowledge:** masked commitment `U_f + X^N R`, Libra-style masked sumcheck, masking codeword; simulator proof, following the technique developed for Kronecker-FRI 0.5.
- **Lean:** the new theorems formalised with the same single axiom.

## Later

### Theory
- **Other domains.** A kernel-type basis for circle domains and additive subspaces.

### Implementation
- **Engineering:** Merkle multiproofs, parallel commit and open, SIMD field arithmetic.
- **Documentation:** a stable API and documentation (`cargo doc`), and fuzzing of the verifier.

### Formal verification
- **Pending items:** formalise Lemma 2.21 (Galois descent) and Facts 2.2 and 2.20 (cyclicity of $\mathbb{F}_q^\times$ from Mathlib; a verified decoder).
- **Abstract IOR structure:** state relaxed round-by-round knowledge soundness (Def 3.14) for a general interactive oracle reduction in Lean, and instantiate it with `NonInteractive`.
- **Linking:** connect the Rust implementation to the Lean specification (for example with extracted test vectors, or Aeneas/hax-style verification of the folding kernel).
- **Replacing the axiom:** replace `bciks_unique` by a formal proof of correlated agreement in the unique-decoding regime.
