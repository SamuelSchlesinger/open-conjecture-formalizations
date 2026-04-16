# Sieve Target

This note makes the analytic gap in the Fortune project explicit.

The point is to separate two logically different steps:

1. produce a prime offset `m` in the Route 2 range whose translate `q# + m`
   has no small proper prime factor
2. upgrade that sifted information to the conclusion that `q# + m` is prime

## Setup

Fix `n >= 1`, set `q = lastIncludedPrime n`, and let `r` be the next prime
after `q`.

The prime-offset formulation asks for

```text
∃ m, Prime m ∧ q < m ∧ m < r^2 ∧ Prime (q# + m).
```

In Lean this is `PrimeOffsetPrimeExistsAtPrime q r`.

## Sifted Candidate

The new formal intermediate notion is a sifted candidate:

```text
Prime m
∧ q < m
∧ m < r^2
∧ for every prime ell <= z,
    if ell | (q# + m), then ell = q# + m.
```

In Lean this is

```text
SiftedPrimeOffsetCandidateAtPrime q r z m.
```

So `m` is itself prime, lies in the correct range, and the translate `q# + m`
has no proper prime divisor up to the sieve level `z`.

The existential version is

```text
SiftedPrimeOffsetExistsAtPrime q r z.
```

There is also a windowed formulation that only checks primes strictly above `q`:

```text
Prime m
∧ q < m
∧ m < r^2
∧ for every prime ell with q < ell <= z,
    if ell | (q# + m), then ell = q# + m.
```

In Lean this is `WindowSiftedPrimeOffsetCandidateAtPrime q r z m`, with
existential form `WindowSiftedPrimeOffsetExistsAtPrime q r z`.

Finally, there is a roughness formulation that records actual nondivisibility in
the sieve window:

```text
Prime m
∧ q < m
∧ m < r^2
∧ for every prime ell with q < ell <= z,
    ell ∤ (q# + m).
```

In Lean this is `WindowRoughPrimeOffsetCandidateAtPrime q r z m`, with
existential form `WindowRoughPrimeOffsetExistsAtPrime q r z`.

## Why This Is The Right Formal Split

This cleanly isolates the two analytic tasks.

It is also closer to an actual sieve statement, because primes `ell <= q` do
not need to be checked at all once `m` is prime and `m > q`. That local
exclusion is now formalized as

```text
primeOffset_not_dvd_primorial_add_of_prime_le
```

in [`Fortune.Sieve`](../Fortune/Sieve.lean).

The first task is a lower-bound sieve problem:

```text
show that some prime m in (q, r^2) survives the local congruence conditions
up to a useful sieve level z.
```

The second task is the parity or primality upgrade:

```text
show that surviving to that sieve level forces q# + m to be prime.
```

There are now two formal upgrade mechanisms in the repository:

1. the full-sieve upgrade, which checks prime divisors all the way up to
   `q# + r^2`
2. the square-bound roughness upgrade, which only checks nondivisibility up to
   `z`, provided `q# + m <= z^2`

In the repository this is reflected by the route-level definitions

- `Route2SieveLowerBound`
- `Route2ParityUpgrade`

in [`Fortune.Progress`](../Fortune/Progress.lean).

There is also a generic theorem

```text
route2_primeOffsetPrimeExistence_of_sieveLowerBound_and_parityUpgrade
```

showing that these two inputs together recover the prime-offset formulation.

## Full-Sieve Target

The specialized sharp target uses the full interval endpoint as sieve level:

```text
fullSieveLevelAtPrime q r = q# + r^2.
```

The corresponding existential statement is

```text
FullSiftedPrimeOffsetExistsAtPrime q r.
```

At the route level this becomes

```text
Route2FullSiftedPrimeOffsetExistence.
```

This is the new single open target currently encoded in the project.

There is also a strictly more sieve-shaped version:

```text
Route2FullWindowSiftedPrimeOffsetExistence.
```

This asks only for control of prime divisors in the window

```text
q < ell <= q# + r^2.
```

Because the primes `ell <= q` are already excluded for structural reasons, this
windowed target has the same force for the current reduction pipeline.

That equivalence is now formalized both pointwise and at route level:

- `siftedPrimeOffsetExistsAtPrime_iff_windowSiftedPrimeOffsetExistsAtPrime`
- `route2SieveLowerBound_iff_route2WindowSieveLowerBound`
- `route2FullSiftedPrimeOffsetExistence_iff_route2FullWindowSiftedPrimeOffsetExistence`

## Square-Root Upgrade

The roughness formulation becomes especially useful once the sieve level reaches
the square-root scale.

If

```text
q# + m <= z^2
```

and `q# + m` has no prime divisor in the window `q < ell <= z`, then `q# + m`
is prime. The reason is simple:

- any prime divisor `ell <= q` is already impossible by the primorial structure
- if `q# + m` were composite, its least prime factor would be at most `sqrt(q# + m)`
- so that least prime factor would lie in the forbidden window `q < ell <= z`

This is now formalized as

```text
prime_translate_of_windowRoughPrimeOffsetCandidateAtPrime
```

in [`Fortune.Sieve`](../Fortune/Sieve.lean).

At route level, the corresponding abstract inputs are:

- `Route2WindowRoughLowerBound Z`
- `Route2SquareSieveLevel Z`

and together they imply the prime-offset formulation via

```text
route2_primeOffsetPrimeExistence_of_windowRoughLowerBound_and_squareSieveLevel
```

and hence also `FortuneConjecture`.

## Canonical Square-Root Target

The abstract square-bound hypothesis can now be eliminated entirely by choosing
the canonical sieve level

```text
z = floor(sqrt(q# + r^2)) + 1.
```

In Lean this is `canonicalSquareSieveLevelAtPrime q r`.

The key arithmetic fact is

```text
q# + r^2 <= (floor(sqrt(q# + r^2)) + 1)^2,
```

formalized as

```text
fullSieveLevelAtPrime_le_canonicalSquareSieveLevelAtPrime_sq.
```

So the generic square-root upgrade immediately yields a canonical rough target:

```text
Route2CanonicalSquareWindowRoughExistence.
```

There is also a parallel canonical sifted target:

```text
Route2CanonicalSquareWindowSiftedExistence.
```

The sifted target asks that every prime divisor in the canonical window be
trivial. The rough target asks that no prime divisor occur there at all. The
bridge from canonical sifted to canonical rough is now formalized using the
Euclid-style bound

```text
r <= q# + 1
```

for consecutive primes `q < r`, together with the resulting theorem
`canonicalSquareSieveLevelAtPrime_lt_translate_of_consecutivePrimes`.

The rough target is still the sharpest one-line analytic target in the project.
It asks for a prime `m` with `q < m < r^2` such that `q# + m` has no prime
divisor in the window

```text
q < ell <= floor(sqrt(q# + r^2)) + 1.
```

At route level, the sifted target implies the conjectural prime-offset
statement via

```text
route2_primeOffsetPrimeExistence_of_canonicalSquareWindowSiftedExistence
```

and the rough target implies it via

```text
route2_primeOffsetPrimeExistence_of_canonicalSquareWindowRoughExistence
```

and hence also `FortuneConjecture`.

## Why Full Sieve Already Suffices

If `m < r^2`, then

```text
q# + m < q# + r^2.
```

So if every prime divisor of `q# + m` up to `q# + r^2` is trivial, then in
particular the least prime divisor of `q# + m` must be `q# + m` itself. That
forces primality.

The corresponding Lean theorem is

```text
prime_translate_of_siftedPrimeOffsetCandidateAtPrime
```

in [`Fortune.Sieve`](../Fortune/Sieve.lean).

From this we get the fully formal implication chain

```text
Route2FullSiftedPrimeOffsetExistence
  -> Route2PrimeOffsetPrimeExistence
  -> Route2ReductionBound
  -> FortuneConjecture.
```

The endpoint theorems are:

- `route2_primeOffsetPrimeExistence_of_fullSiftedPrimeOffsetExistence`
- `route2_reductionBound_of_fullSiftedPrimeOffsetExistence`
- `route2_fortune_of_fullSiftedPrimeOffsetExistence`
- `route2_primeOffsetPrimeExistence_of_fullWindowSiftedPrimeOffsetExistence`
- `route2_reductionBound_of_fullWindowSiftedPrimeOffsetExistence`
- `route2_fortune_of_fullWindowSiftedPrimeOffsetExistence`
- `route2_primeOffsetPrimeExistence_of_windowRoughLowerBound_and_squareSieveLevel`
- `route2_reductionBound_of_windowRoughLowerBound_and_squareSieveLevel`
- `route2_fortune_of_windowRoughLowerBound_and_squareSieveLevel`

The converse direction from genuine prime translates is now also formalized:
if `q# + m` is already prime with `m` prime and `q < m < r^2`, then the
window-sifted predicate automatically holds at any sieve level. In Lean this is
`windowSiftedPrimeOffsetCandidateAtPrime_of_primeTranslate`, and it yields
`canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime`.

As a consequence, the verified finite interval-prime results for `1 <= n <= 17`
now immediately produce:

- `route2_primeOffsetPrimeExistence_one_to_seventeen_progress`
- `route2_canonicalSquareWindowSiftedExistence_one_to_seventeen_progress`

## What Is Still Hard

The full-sieve target is not yet a proof method by itself. It packages the
problem sharply, but proving it uniformly is still hard.

What it does accomplish is this:

- it removes vague language about "probably a sieve argument"
- it tells us exactly what kind of candidate must be produced
- it separates the existence part from the primality-upgrade part

So future work can aim at either of two fronts:

1. prove `Route2SieveLowerBound Z` for some useful sieve level `Z`
2. prove `Route2ParityUpgrade Z` at that same level

The trivial fully formal upgrade is available when `Z q r = q# + r^2`, but that
is analytically too strong to expect from a standard lower-bound sieve alone.

## Lean Location

The main new formal objects are in [`Fortune.Sieve`](../Fortune/Sieve.lean):

- `SiftedPrimeOffsetCandidateAtPrime`
- `SiftedPrimeOffsetExistsAtPrime`
- `WindowSiftedPrimeOffsetCandidateAtPrime`
- `WindowSiftedPrimeOffsetExistsAtPrime`
- `WindowRoughPrimeOffsetCandidateAtPrime`
- `WindowRoughPrimeOffsetExistsAtPrime`
- `fullSieveLevelAtPrime`
- `canonicalSquareSieveLevelAtPrime`
- `FullSiftedPrimeOffsetExistsAtPrime`
- `FullWindowSiftedPrimeOffsetExistsAtPrime`
- `CanonicalSquareWindowSiftedPrimeOffsetExistsAtPrime`
- `CanonicalSquareWindowRoughPrimeOffsetExistsAtPrime`
- `windowSiftedPrimeOffsetCandidateAtPrime_of_primeTranslate`
- `prime_translate_of_siftedPrimeOffsetCandidateAtPrime`
- `prime_translate_of_windowSiftedPrimeOffsetCandidateAtPrime`
- `prime_translate_of_windowRoughPrimeOffsetCandidateAtPrime`
- `canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime_of_primeOffsetPrimeExistsAtPrime`
- `primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowSiftedPrimeOffsetExistsAtPrime`
- `primeOffsetPrimeExistsAtPrime_of_fullSiftedPrimeOffsetExistsAtPrime`
- `primeOffsetPrimeExistsAtPrime_of_fullWindowSiftedPrimeOffsetExistsAtPrime`
- `primeOffsetPrimeExistsAtPrime_of_windowRoughPrimeOffsetExistsAtPrime`
- `primeOffsetPrimeExistsAtPrime_of_canonicalSquareWindowRoughPrimeOffsetExistsAtPrime`

The route-level decomposition is in [`Fortune.Progress`](../Fortune/Progress.lean).
