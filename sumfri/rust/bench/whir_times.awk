# Reads WHIR's output; prints "commit_ms open_ms verify_ms".
function ms(x) {
  if (x ~ /µs$/) { sub(/µs$/, "", x); return x / 1000 }
  if (x ~ /ms$/) { sub(/ms$/, "", x); return x + 0 }
  if (x ~ /s$/)  { sub(/s$/, "", x);  return x * 1000 }
  return x + 0
}
/^Prover time:/   { c = ms($3); o = ms($5) }
/^Verifier time:/ { v = ms($3) }
END { printf "%.3f %.3f %.4f\n", c, o, v }
