# Singmaster's conjecture — computational exploration

Script: `explore.py`. It computes the exact multiplicity `N(a) = #{(n,k) :
C(n,k)=a}` for every `a ∈ [2, 10⁶]` by sweeping Pascal's triangle (the `k=1`
column gives every `a` its base `2`; interior columns `k≥2` add the rare extra
coincidences, and `C(n,2) ≤ L` already forces `n ≤ √(2L)`, so the sweep is
cheap).

## Multiplicity distribution for `a ∈ [2, 10⁶]`

| `N(a)` | # of `a` |
|---|---|
| 1 | 1            (just `a=2`) |
| 2 | 998 266      (almost everything) |
| 3 | 10 |
| 4 | 1 715 |
| 5 | **0** |
| 6 | 6 |
| 7 | **0** |
| 8 | 1            (`a = 3003`) |

**Maximum multiplicity in range = 8**, attained uniquely by
`3003 = C(3003,1) = C(78,2) = C(15,5) = C(14,6)` (with symmetric partners).
This is the evidence for Singmaster's conjectured constant `C = 8`.

Numbers appearing exactly 6 times: `120, 210, 1540, 7140, 11628, 24310`.
Numbers appearing ≥ 8 times: `3003` only.

## Observations

- **Odd multiplicities > 3 do not occur** (no `a ≤ 10⁶` appears 5 or 7 times).
  Reason: an interior occurrence `(n,k)` with `k ≠ n-k` contributes its mirror
  `(n,n-k)` too, so interior occurrences come in pairs; combined with the `2` from
  the `k=1` column, total multiplicities are even *unless* a central coefficient
  `C(2k,k)` is involved (which contributes an odd `1`). The value `3` arises only
  from a single central coincidence; `5,7` would need rarer central coincidences
  that simply do not happen in range.
- **`N(a) ≥ 2` for all `a ≥ 3`**, **`N(a) = 2` generically** — matches the Lean
  theorem `two_le_singmasterCount`.
- **`C(n,2)` always reaches `N ≥ 4`** for `n ≥ 5` — matches the Lean theorem
  `four_le_singmasterCount_choose_two` (the proved infinite family).

## Cross-check against the Lean theorems

| fact | Python | Lean |
|---|---|---|
| `N(2)` | 1 | `singmasterCount_two` |
| `N(6)` | 3 | `singmasterCount_six` |
| `N(10)` | 4 | `singmasterCount_ten` |
| `min_{a≥3} N(a)` | 2 | `two_le_singmasterCount` |
| `min_{n∈[5,59]} N(C(n,2))` | 4 | `four_le_singmasterCount_choose_two` |

## The open frontier

No *constant* upper bound on `N(a)` is proved. The best known is
`N(a) = O(log a / log log a)` (Singmaster 1971; Abbott–Erdős–Hanson 1974),
and `N(a) = O((log a)(log log log a)/(log log a)³)` (Kane 2007). An infinite
family with `N(a) ≥ 6` is known (Singmaster, via a Fibonacci identity giving
`C(F_{2i+2}F_{2i+3}, F_{2i}F_{2i+3}) = C(F_{2i+2}F_{2i+3}-1, F_{2i}F_{2i+3}+1)`;
`i=1` gives `3003`). Whether any `a` appears `> 8` times is open; none is known.
The Lean project proves the lower bound `C ≥ 4` (`four_le_of_singmasterConjecture`)
and leaves the uniform bound as the single `sorry`.
