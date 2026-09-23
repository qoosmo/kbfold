# Roadmap

Planned directions for turning KBFold into a full R&D project. Items are ordered by dependency, not by date.

## Theory
- **List decoding.** Extend soundness (Thm 7.13) and round-by-round knowledge soundness to proximity parameters up to the Johnson bound. This needs correlated agreement beyond unique decoding, and the passing-set argument with lists instead of unique codewords.
- **Several openings.** Several openings of one commitment, and batched openings via random linear combinations (Remark 6.7).
- **Zero knowledge.** Masking for the kernel encoding.
- **Other domains.** A kernel-type basis for circle domains and additive subspaces.

## Implementation
- **Conformance with CDHZ25, Construction 11.7:**
  - salted Merkle trees;
  - challenge derivation from the roots and salts;
  - the quartic extension $\mathbb{F}_p[\iota]/(\iota^4 - 7)$.

  With these, Corollary 7.26 applies to the code as released.
- **Engineering:** Merkle multiproofs, parallel commit and open, SIMD field arithmetic.
- **Documentation:** a stable API and documentation (`cargo doc`), and fuzzing of the verifier.

## Formal verification
- **Pending items:** formalise Lemma 2.21 (Galois descent) and Facts 2.2 and 2.20 (cyclicity of $\mathbb{F}_q^\times$ from Mathlib; a verified decoder).
- **Abstract IOR structure:** state relaxed round-by-round knowledge soundness (Def 3.14) for a general interactive oracle reduction in Lean, and instantiate it with `NonInteractive`.
- **Linking:** connect the Rust implementation to the Lean specification (for example with extracted test vectors, or Aeneas/hax-style verification of the folding kernel).
- **Replacing the axiom:** replace `bciks_unique` by a formal proof of correlated agreement in the unique-decoding regime.
