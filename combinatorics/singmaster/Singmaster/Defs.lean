import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Image

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
the cases `k = 0` or `k = n` give `C = 1 ≠ a` (`Basic.le_of_choose_eq`).  Hence

```
singmasterCount a = #{ (n,k) : n ≤ a ∧ k ≤ n ∧ C(n,k) = a }
```

is an honest, *computable* cardinality equal to `N(a)` for `a ≥ 2`.  We build it
row by row (`biUnion` over `n ≤ a`, then `image` of the valid columns) rather
than as a square product `{0,…,a}²`: this keeps membership proofs free of the
quadratic blow-up a literal `range (a+1) ×ˢ range (a+1)` would force in the
elaborator for large `a` (e.g. `a = 3003`, used in `Records`).  Small cases are
decidable by the kernel (`decide`).  (For `a ≤ 1` this undercounts — `1` occurs
infinitely often — which is exactly why the conjecture is stated for `a ≥ 2`.)
-/

set_option autoImplicit false

namespace Singmaster

/-- The set of Pascal-triangle positions `(n, k)` with `n ≤ a`, `k ≤ n` and
`C(n, k) = a`.  We build it row by row (`biUnion` over `n`, then `image` of the
valid columns) rather than as a square product `{0,…,a}²`: this keeps membership
proofs free of the quadratic blow-up that a literal `range (a+1) ×ˢ range (a+1)`
would force for large `a` (e.g. `a = 3003`). -/
def occurrences (a : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1)).biUnion fun n =>
    ((Finset.range (n + 1)).filter fun k => n.choose k = a).image fun k => (n, k)

/-- The **Singmaster multiplicity** `N(a)`: the number of times `a` occurs in
Pascal's triangle (faithful for `a ≥ 2`; see the module doc-comment). -/
def singmasterCount (a : ℕ) : ℕ := (occurrences a).card

/-- Membership in `occurrences`, unpacked: `(n,k)` occurs iff `n ≤ a`, `k ≤ n`
and `C(n,k) = a`. -/
@[simp] theorem mem_occurrences {a n k : ℕ} :
    (n, k) ∈ occurrences a ↔ n < a + 1 ∧ k ≤ n ∧ n.choose k = a := by
  simp only [occurrences, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨n', hn', k', ⟨hk', hc⟩, rfl, rfl⟩; exact ⟨hn', by omega, hc⟩
  · rintro ⟨hn, hk, hc⟩; exact ⟨n, hn, k, ⟨by omega, hc⟩, rfl, rfl⟩

/-- **Singmaster's conjecture**: the multiplicity is uniformly bounded. -/
def SingmasterConjecture : Prop :=
  ∃ C : ℕ, ∀ a : ℕ, 2 ≤ a → singmasterCount a ≤ C

end Singmaster
