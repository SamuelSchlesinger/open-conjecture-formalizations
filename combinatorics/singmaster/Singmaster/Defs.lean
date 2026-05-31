import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
# Singmaster's conjecture — definitions

Reference: https://en.wikipedia.org/wiki/Singmaster%27s_conjecture

Let `a ≥ 2`.  Its *Singmaster multiplicity* `N(a)` is the number of positions
`(n, k)` (with `0 ≤ k ≤ n`) in Pascal's triangle at which the binomial
coefficient equals `a`:

```
N(a) = #{ (n,k) : k ≤ n, C(n,k) = a }.
```

> **Conjecture (Singmaster 1971).** There is a constant `C` with `N(a) ≤ C` for
> all `a ≥ 2`.  Singmaster conjectured `C = 8` (no number is known to appear
> more than `8` times; `3003 = C(3003,1) = C(78,2) = C(15,5) = C(14,6)` and their
> symmetric partners realize `8`).

## Making `N(a)` a computable `Finset` cardinality

For `a ≥ 2`, every occurrence has `n ≤ a`: if `1 ≤ k ≤ n-1` then
`C(n,k) ≥ n` (the row-minimum away from the `1`-valued ends), so `a = C(n,k) ≥ n`;
the cases `k = 0` or `k = n` give `C = 1 ≠ a`.  Hence all occurrences live in the
finite box `{0,…,a} × {0,…,a}`, and

```
singmasterCount a = #{ (n,k) ∈ {0,…,a}² : k ≤ n ∧ C(n,k) = a }
```

is an honest, *computable* cardinality equal to `N(a)` for `a ≥ 2`
(`Basic.singmasterCount_eq`).  Small cases are therefore decidable by the kernel
(`decide`).  (For `a ≤ 1` the box undercounts — `1` occurs infinitely often —
which is exactly why the conjecture is stated for `a ≥ 2`.)
-/

set_option autoImplicit false

namespace Singmaster

/-- The set of Pascal-triangle positions `(n, k)` inside the box `{0,…,a}²` with
`k ≤ n` and `C(n, k) = a`. -/
def occurrences (a : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (a + 1)).filter
    (fun p => p.2 ≤ p.1 ∧ p.1.choose p.2 = a)

/-- The **Singmaster multiplicity** `N(a)`: the number of times `a` occurs in
Pascal's triangle (faithful for `a ≥ 2`; see the module doc-comment). -/
def singmasterCount (a : ℕ) : ℕ := (occurrences a).card

/-- Membership in `occurrences`, unpacked. -/
@[simp] theorem mem_occurrences {a n k : ℕ} :
    (n, k) ∈ occurrences a ↔ (n < a + 1 ∧ k < a + 1) ∧ k ≤ n ∧ n.choose k = a := by
  unfold occurrences
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]

/-- **Singmaster's conjecture**: the multiplicity is uniformly bounded. -/
def SingmasterConjecture : Prop :=
  ∃ C : ℕ, ∀ a : ℕ, 2 ≤ a → singmasterCount a ≤ C

end Singmaster
