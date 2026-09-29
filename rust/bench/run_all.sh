#!/usr/bin/env bash
# Runs every benchmark of Section 9 and writes CSV files to results/<tag>/.
# Usage (from rust/):  bench/run_all.sh <tag> [max_m] [whir_dir]
#   whir_dir: a build of https://github.com/WizardOfMenlo/whir (cargo build --release --bin main),
#             run as an external reference; omitted if not given.
set -euo pipefail
tag=${1:?tag}; max=${2:-22}; whir=${3:-}
out=results/$tag; mkdir -p "$out"
{ uname -a; (lscpu 2>/dev/null || sysctl -n machdep.cpu.brand_string) | head -20; rustc --version; git rev-parse HEAD; } > "$out/machine.txt"
cargo build -q --release --example bench
cargo build -q --release --features parallel --example bench --target-dir target/par
for mode in scaling pq salt stop rate breakdown; do
  ./target/release/examples/bench "$mode" "$max" > "$out/$mode.csv"
  echo "$mode done"
done
for mode in scaling pq; do
  ./target/par/release/examples/bench "$mode" "$max" > "$out/${mode}_parallel.csv"
  echo "$mode parallel done"
done
if [ -n "$whir" ]; then
  echo "config,m,threads,commit_ms,open_ms,prover_ms,verify_ms,proof_kib" > "$out/whir.csv"
  for m in $(seq 12 2 "$max"); do
    for cfg in "unique-k1:-k 1 -i 1 --decoding-regime Unique" "johnson-k4:-k 4 -i 4 --decoding-regime Johnson"; do
      name=${cfg%%:*}; args=${cfg#*:}
      for th in 1 $(nproc 2>/dev/null || sysctl -n hw.ncpu); do
        rows=""
        for rep in 1 2 3; do
          o=$(RAYON_NUM_THREADS=$th "$whir/target/release/main" -d "$m" -r 2 -p 0 -l 100 -f Goldilocks2 --reps 21 $args 2>&1)
          # "Prover time: 1.7ms + 3.0ms = 4.7ms", "Verifier time: 345.3µs"; units s, ms or µs
          rows="$rows$(echo "$o" | awk -f bench/whir_times.awk)\n"
          size=$(echo "$o" | sed -n 's/^Proof size: \([0-9.]*\) KiB/\1/p')
        done
        # median of three runs, by prover time
        med=$(printf "$rows" | awk 'NF==3' | sort -n -k1 | sed -n 2p)
        echo "$name,$m,$th,$(echo $med | awk '{printf "%.2f,%.2f,%.2f,%.3f", $1, $2, $1+$2, $3}'),$size" >> "$out/whir.csv"
      done
    done
  done
  echo "whir done"
fi
