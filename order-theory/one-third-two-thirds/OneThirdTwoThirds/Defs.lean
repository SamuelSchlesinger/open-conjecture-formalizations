import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

/-!
# The 1/3–2/3 conjecture — definitions

Reference: https://en.wikipedia.org/wiki/1/3%E2%80%932/3_conjecture

Let `P = (X, ≤)` be a finite poset.  A *linear extension* of `P` is a total
order on `X` that contains `≤`; equivalently, an order-preserving bijection
`X ≃ Fin n` where `n = |X|`.  Write `e(P)` for the number of linear extensions
and, for an incomparable pair `x ∥ y`, `e(P, x<y)` for the number of linear
extensions placing `x` before `y`.  With
`δ(x,y) = e(P, x<y) / e(P) ∈ (0,1)`, the conjecture (Kislitsyn 1968; Fredman;
Linial 1984) asserts that every finite poset that is **not a chain** has an
incomparable pair with `1/3 ≤ δ(x,y) ≤ 2/3`.

## Encoding linear extensions

We encode a linear extension as a *ranking*: a function `f : X → Fin n`
(`n = |X|`) that is injective and monotone (`a ≤ b → f a ≤ f b`).  Since `X`
has `n` elements, an injective `f : X → Fin n` is automatically a bijection,
and monotonicity makes the pullback of `Fin n`'s order a linear order
containing `≤`.  This correspondence is bijective: distinct linear extensions
give distinct rankings and vice versa.  The advantage over the
`OrderHom`/`Set`-based encoding (cf. `google-deepmind/formal-conjectures`) is
that the set of rankings is a genuine `Finset`, so `e(P)` and `e(P, x<y)` are
honest, computable cardinalities — and small posets are decidable.

## Fraction-free statement

Following the project's Frankl convention of avoiding division, "`δ(x,y)` lies
in `[1/3, 2/3]`" is written as the pair of `ℕ`-inequalities
`e(P) ≤ 3 · e(P, x<y)` and `3 · e(P, x<y) ≤ 2 · e(P)`.
-/

set_option autoImplicit false

namespace OneThirdTwoThirds

variable {X : Type*}

/-- A *ranking* (encoded linear extension) of a finite poset on `X`:
an injective, monotone map from `X` to the positions `Fin |X|`.

Injectivity says all elements get distinct positions; monotonicity
(`a ≤ b → f a ≤ f b`) says the positions respect the partial order.  As `|X|`
positions are assigned injectively to `|X|` elements, `f` is a bijection, so
this is exactly a linear extension of the poset. -/
def IsLinExt [Preorder X] [Fintype X] (f : X → Fin (Fintype.card X)) : Prop :=
  Function.Injective f ∧ ∀ a b : X, a ≤ b → f a ≤ f b

instance [Preorder X] [Fintype X] [DecidableEq X] [DecidableLE X]
    (f : X → Fin (Fintype.card X)) : Decidable (IsLinExt f) := by
  unfold IsLinExt
  have : Decidable (Function.Injective f) := by
    unfold Function.Injective
    infer_instance
  infer_instance

variable [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X]

/-- The finite set of all linear extensions (rankings) of the poset on `X`. -/
def linExts : Finset (X → Fin (Fintype.card X)) :=
  Finset.univ.filter IsLinExt

/-- `e(P)`: the number of linear extensions of the poset on `X`. -/
def numLinExts : ℕ := (linExts (X := X)).card

/-- `e(P, x<y)`: the number of linear extensions placing `x` before `y`
(i.e. assigning `x` a strictly smaller position than `y`). -/
def numBefore (x y : X) : ℕ :=
  ((linExts (X := X)).filter (fun f => f x < f y)).card

/-- Two elements are *incomparable* when neither is `≤` the other.  This is the
hypothesis under which `δ(x,y)` is interesting (for comparable `x < y` every
extension places `x` before `y`, so `δ = 1`). -/
def Incomp (x y : X) : Prop := ¬ x ≤ y ∧ ¬ y ≤ x

instance (x y : X) : Decidable (Incomp x y) := by unfold Incomp; infer_instance

/-- The *balanced pair* predicate, fraction-free.  An incomparable pair `{x,y}`
is balanced when `1/3 ≤ δ(x,y) ≤ 2/3`, written as
`e(P) ≤ 3·e(P,x<y)` and `3·e(P,x<y) ≤ 2·e(P)`. -/
def IsBalancedPair (x y : X) : Prop :=
  Incomp x y ∧
    numLinExts (X := X) ≤ 3 * numBefore x y ∧
    3 * numBefore x y ≤ 2 * numLinExts (X := X)

instance (x y : X) : Decidable (IsBalancedPair x y) := by
  unfold IsBalancedPair; infer_instance

/-- A poset is *not a chain* when it has an incomparable pair. -/
def IsNotChain : Prop := ∃ x y : X, Incomp x y

/-- The 1/3–2/3 conjecture for the single poset on `X`: if the poset is not a
chain, it has a balanced incomparable pair. -/
def OneThirdTwoThirdsFor : Prop :=
  IsNotChain (X := X) → ∃ x y : X, IsBalancedPair x y

end OneThirdTwoThirds

namespace OneThirdTwoThirds

/-- **The 1/3–2/3 conjecture** (Kislitsyn 1968; Fredman; Linial 1984).
Every finite poset that is not a chain has an incomparable pair `{x, y}` with
`1/3 ≤ e(P, x<y)/e(P) ≤ 2/3`. -/
def OneThirdTwoThirdsConjecture : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] [PartialOrder X] [DecidableLE X],
    OneThirdTwoThirdsFor (X := X)

end OneThirdTwoThirds
