# Prime-Offset Formulation

This note records the strongest Route 2 formulation that currently looks
mathematically promising in this project.

## Setup

Fix `n >= 1`. Let

- `q = lastIncludedPrime n`
- `r` be the next prime after `q`, so `ConsecutivePrimes q r`

The existing Route 2 hypothesis in the formalization is the upper-interval
statement

```text
∃ p, Prime p ∧ q# + 1 < p ∧ p < q# + r^2.
```

In Lean this is `IntervalPrimeExistsAtPrime q r`, and it is equivalent to the
plain offset form

```text
∃ k, 1 < k ∧ k < r^2 ∧ Prime (q# + k).
```

In Lean this is `OffsetPrimeExistsAtPrime q r`.

## Stronger Formulation

The more interesting research target is the prime-offset strengthening

```text
∃ m, Prime m ∧ q < m ∧ m < r^2 ∧ Prime (q# + m).
```

In Lean this is `PrimeOffsetPrimeExistsAtPrime q r`.

The point is that this does not merely ask for some short offset producing a
prime translate of `q#`; it asks for a prime offset above the whole range of
primes already built into the primorial.

## Why This Is Useful

This formulation is stronger than the interval statement already used in the
formal reduction chain, so any proof of it would immediately feed into the
existing machinery:

```text
PrimeOffsetPrimeExistsAtPrime
  -> OffsetPrimeExistsAtPrime
  -> IntervalPrimeExistsAtPrime
  -> Route2ReductionBound
  -> FortuneConjecture.
```

The corresponding Lean theorems are:

- `offsetPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime`
- `intervalPrimeExistsAtPrime_of_primeOffsetPrimeExistsAtPrime`
- `route2_reductionBound_of_primeOffsetPrimeExistence`
- `route2_fortune_of_primeOffsetPrimeExistence`

So this is not a competing reformulation. It is a strictly stronger target that
plugs directly into the route we already formalized.

The next refinement of this strategy is the sifted-candidate formulation in
[`sieve-target.md`](./sieve-target.md), which isolates the analytic gap in a
form closer to sieve methods.

## Why This Looks More Natural Than Raw Interval Primes

The interval statement

```text
q# + 1 < p < q# + r^2
```

is mathematically correct but somewhat indirect. It quantifies over an ambient
prime `p` and only recovers the offset after subtracting `q#`.

The prime-offset version instead talks about the arithmetic object we actually
care about:

- the offset is itself prime
- the offset already lies above `q`
- `q# + offset` is also prime

This interacts well with the primorial congruence structure. If `m` is prime
and `m > q`, then for every prime `ell <= q` we have `m mod ell != 0`, so

```text
q# + m ≡ m (mod ell)
```

cannot vanish modulo any included prime. In other words, prime offsets above
`q` automatically evade all divisibility obstructions coming from the primorial
base.

## Why Generic Short-Interval Prime Results Are Not Enough

The current interval has length about `r^2`, which is about `q^2`. Since
`q ≈ log(q#)`, this means the interval near `q#` has length on the scale

```text
O((log q#)^2).
```

That is far shorter than the ranges controlled by standard unconditional
prime-in-short-interval theorems. So even though Route 2 is phrased as an
interval-existence statement, the live research problem is not a generic prime
gap question near a large number. The special structure of primorial translates
has to do the real work.

This is one reason the prime-offset formulation seems like the better target:
it keeps the problem focused on the structured family

```text
m, q# + m
```

rather than on arbitrary primes in a short interval.

## Heuristic Interpretation

The prime-offset formulation asks for a prime `m` such that both members of the
pair

```text
m, q# + m
```

are prime, with `q < m < r^2`.

For primes `ell <= q`, the condition `ell ∤ m` is automatic once `m` is prime
and larger than `q`, and then also `ell ∤ (q# + m)`. So the obvious local
obstructions from the included primes are already removed. That does not prove
anything, but it suggests that the right heuristic object is a structured
two-prime pattern rather than a bare interval.

## Status

This note is a strategy document, not a proof. The repository currently proves:

- the interval criterion imported from the literature in
  [`Fortune.Literature`](../Fortune/Literature.lean)
- the equivalence between interval and plain offset forms in
  [`Fortune.IntervalExistence`](../Fortune/IntervalExistence.lean)
- the implication from the stronger prime-offset formulation to
  `FortuneConjecture`
- the sifted-candidate and full-sieve formulations in
  [`Fortune.Sieve`](../Fortune/Sieve.lean)

What remains open is the actual existence statement `PrimeOffsetPrimeExistsAtPrime`
in any uniform infinite form.

## References

- Čejchan, A.; Křížek, M.; Somer, L. "There are no sign changes in formulae
  involving prime numbers." *Rocky Mountain J. Math.* 48 (2018), 1165-1178.
  This is the source of the primorial interval theorem formalized in
  [`Fortune.Literature`](../Fortune/Literature.lean). See also
  [`references.md`](../../../references.md#number-theory).
- Křížek, M.; Luca, F.; Somer, L. *17 Lectures on Fermat Numbers: From Number
  Theory to Geometry*. Springer, 2022. Section 2.4 surveys Fortune-related
  primorial interval results. Open chapter PDF:
  <https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.pdf>
- Guy, R. K. *Unsolved Problems in Number Theory*. 3rd ed., Springer, 2004.
  This remains the standard problem-source reference for Fortune's conjecture;
  see [`references.md`](../../../references.md#number-theory).
