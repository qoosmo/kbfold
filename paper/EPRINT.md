# ePrint submission data

Fields for the IACR Cryptology ePrint Archive form (https://eprint.iacr.org/submit). The PDF is `paper/kbfold.pdf` of the release tagged in §10.2 of the paper.

## Title
Post-Quantum Multilinear Polynomial Commitments from FRI Folding in the Boolean-Kernel Basis

## Author
Abdelali Mkhida, Algorizk Labs, ali.mkhida@algorizk.xyz, ORCID 0009-0009-2101-9070

## Abstract (plain text)
Hash-based multilinear polynomial commitment schemes in the BaseFold paradigm are candidates for post-quantum security; they commit to a Reed-Solomon encoding and prove evaluations by interleaving a sumcheck with FRI-style folding. Over smooth multiplicative domains the classical fold acts on monomial coefficients, so a prover holding a table of values on the Boolean hypercube must first convert it to coefficient form. We introduce the Boolean-kernel basis K_b(X) = prod_{k=1}^{n} (X^{2^{k-1}} + b_k), b in {0,1}^n, of the univariate polynomials of degree less than 2^n. Its change of basis to monomials is the Kronecker power of a 2x2 matrix and costs (n/2)2^n additions or subtractions. In this basis a normalised FRI fold is exactly the restriction of one variable of the multilinear extension of the coordinate table, so folding the encoding of a table evaluates its multilinear extension directly. On this fold dictionary we build a transparent, hash-based multilinear polynomial commitment scheme and prove it sound, evaluation binding and round-by-round knowledge sound in the unique-decoding regime; the only external result about codes is the correlated-agreement theorem for Reed-Solomon codes. With the BCS theorem for interactive oracle reductions of Chiesa, Di, Hu and Zheng, the non-interactive scheme is knowledge sound, for a single opening, against quantum adversaries in the quantum random oracle model, with explicit bounds. A Rust implementation over the Goldilocks field matches the running time of a coefficient-form baseline sharing all other code, and companion Lean 4 files formalise the algebraic, probabilistic and soundness results, with correlated agreement as the only axiom.

## Keywords
polynomial commitment, multilinear polynomial, FRI, BaseFold, Reed-Solomon codes, proximity gaps, post-quantum, formal verification, Lean

## Category
Cryptographic protocols

## License
CC BY 4.0 (the same as the paper in the repository). The license cannot be changed after submission.

## Notes
- Later versions are submitted as revisions of the same ePrint entry, not as new submissions; see `docs/ROADMAP.md`, "Version 2".
- After the ePrint number is assigned: add it to `README.md`, `CITATION.cff` and the Kronecker-FRI paper.
