# FC-Certificate Probe — Findings

Research probe (2026-05-28) after pausing the entropy-transport strategy.  Goal:
search for *new* FC-families ("Frankl-complete": small families that force an
abundant element in any union-closed family containing them) and extract
**sound, Lean-formalizable certificates** generalizing the singleton/doubleton
proofs.

Engine: `research/fc_certificates.py` (validated, exact-rational certificates).

## What the engine does

For a candidate family `A` on `[n]`:

1. **Ground truth (Poonen).** Decide FC-ness by Poonen's weight LP over *all*
   union-closed `B ⊇ A` on `[n]` (full enumeration, exact for `n ≤ 4`).
   Poonen's Theorem (arXiv:2301.01331, Thm 1.1): `A` is FC iff there are weights
   `c ≥ 0`, `Σcᵢ = 1`, with `Σᵢ cᵢ|Bᵢ| ≥ |B|/2` for every such `B`.

2. **Formalizable certificate.** Search for weights `c` plus Farkas multipliers
   on the *fiber-injection* inequalities `m_T ≤ m_{T∪W}` (`W ∈ ⟨A⟩`), where for a
   union-closed `F ⊇ A` grouped by trace `T = B∩[n]`, the map `B ↦ B∪W` injects
   fiber `T` into fiber `T∪W`.  A nonnegative combination proving
   `Σ_T m_T (w_c(T) − ½) ≥ 0` is a finite, `linarith`-closable certificate.
   Each candidate `(c, λ, s)` is re-verified **exactly over ℚ**.

## Results

| Family | Poonen FC? | Fiber-injection certificate? |
|--------|-----------|------------------------------|
| `{x}` (singleton) | yes | **yes**, `c=(1)`, `λ_{W={x},T=∅}=½` |
| `{x,y}` (doubleton) | yes | **yes**, `c=(½,½)`, `λ_{W={x,y},T=∅}=½` |
| single 3-set `{a,b,c}` | **no** | — |
| three triangles through a common vertex, e.g. `{012,013,023}` on `[4]` | yes | **no** |
| any 3 of the 4 triangles on `[4]` | yes | **no** |

Both elementary cases are reproduced with their exact certificates.  These match
the formalized Lean theorems in `Frankl.Basic`
(`isFranklElement_left_or_right_of_pair_mem`).

## The boundary (the real finding)

**The fiber-injection certificate certifies exactly the size-≤2 cases.**  Genuine
3-set FC-families are FC but provably *not* certifiable this way:

- The `B ↦ B∪W` injections are **sound but incomplete**.  They give linear
  inequalities `m_T ≤ m_{T∪W}` on the trace-fiber counts, but they ignore that
  the trace *support* must itself be union-closed — a non-linear constraint.
  Dropping it makes the certificate LP a too-weak relaxation, which is infeasible
  for the 3-set families.  This missing constraint is exactly where Frankl's
  difficulty concentrates.

- For `{012,013,023}` (all members share vertex `0`) the shared vertex is **not**
  forced abundant: in 106 of the 1494 union-closed `B ⊇ A` on `[4]`, element `0`
  is below half.  The Poonen weights are spread (`≈ 7/22, 6/22, 6/22, 3/22`), so
  there is no single-injection / single-element proof — the certificate is
  irreducibly global.

## Honest status

- **No new small FC-families exist to find.**  FC-families are fully classified
  up to a 6-element universe (Marić–Vučković–Živković, FC(6), formalized in
  Isabelle/HOL).  The probe confirms rather than extends this.
- **The elementary (injection) method tops out at the doubleton.**  Anything
  beyond requires the global Poonen argument (spread weights + support
  union-closure), whose only existing formalization is in Isabelle/HOL — porting
  even one 3-set FC certificate to Lean would be a substantial, genuinely novel
  *formalization* effort, not an elementary proof.

## Reproduce

```sh
python3 research/fc_certificates.py --validate
python3 research/fc_certificates.py --search-3sets 4
```
