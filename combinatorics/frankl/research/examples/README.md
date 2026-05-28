# Frankl Experiment Examples

This directory stores small, reusable payloads extracted from the larger
experimental certificates.  The examples are meant to be stable test cases for
future Lean migration and for quick debugging of the Python search routines.

- `generated_feasible_size11.json`: the smallest family-size entry currently
  extracted from `../center_generation_certificate.json` whose sampled
  critical-center miss is resolved by one exact assignment column.
- `tc_centered_cost_dominates_size6.json`: the smallest currently stored
  centered permutation example where raw coordinate entropy gain is positive
  but total-correlation growth is larger, so the net entropy gain is negative.
