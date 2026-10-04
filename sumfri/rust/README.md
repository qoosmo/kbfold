# sumfri (Rust)

Reference implementation of the Sum-FRI paper (`../paper`): the commitment `Enc(f) = ev_L(V_f)`,
the evaluation protocol `Π_eval` for claims `P_f(z) = v` and the sum protocol `Π_sum` for
`Σ_a f(a) = v`, compiled with salted BLAKE3 Merkle trees and Fiat–Shamir. Built on the
[`kbfold`](../../rust) crate (Goldilocks and its extensions, NTT, Merkle trees, transcript).

```
cargo test --release                            # completeness, tampering, consistent cheater, dictionary
cargo run --release --example bench -- sum 22   # Section 8 (also: eval, pq, breakdown)
bench/run_all.sh <tag> 22 <whir_dir>            # every measurement of Section 8, CSV in results/<tag>/
```

The module `quotient` is the baseline of Section 8 that proves the sum by opening `V_f` at `X = 1`
with a quotient and FRI. Research code, not audited.
