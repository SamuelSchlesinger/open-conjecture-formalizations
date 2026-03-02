---
title: References
layout: default
nav_order: 7
---

# References

A centralized bibliography for the formalizations and conjecture index in this
repository. For per-conjecture details, see the linked project documentation.

## Lean & Mathlib

- [Lean 4 documentation](https://lean-lang.org/lean4/doc/) — official language reference
- [Mathlib4 documentation](https://leanprover-community.github.io/mathlib4_docs/) — community math library API docs
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — tutorial for formalizing mathematics
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — introduction to dependent type theory in Lean

## Number Theory

### General references

- Hardy, G. H. & Wright, E. M. *An Introduction to the Theory of Numbers*. Oxford University Press.
- Ireland, K. & Rosen, M. *A Classical Introduction to Modern Number Theory*. Springer GTM 84.
- Guy, R. K. *Unsolved Problems in Number Theory*. 3rd ed., Springer, 2004.

### Formalized conjectures

- **Agoh–Giuga conjecture** — Agoh, T. "On Giuga's conjecture." *Manuscripta Math.* 87 (1995), 501–510. [Submodule](number-theory/ago-giuga/)
- **Carmichael totient conjecture** — Carmichael, R. D. "On Euler's φ-function." *Bull. Amer. Math. Soc.* 13 (1907), 241–243. [Submodule](number-theory/carmichael-totient/)
- **Catalan-Mersenne conjecture** — Catalan-Mersenne numbers and historical conjectural remarks: [Wikipedia](https://en.wikipedia.org/wiki/Double_Mersenne_number#Catalan%E2%80%93Mersenne_number). [In-repo project](number-theory/catalan-mersenne/)
- **Collatz conjecture** — Lagarias, J. C. "The 3x+1 problem and its generalizations." *Amer. Math. Monthly* 92 (1985), 3–23. [Submodule](number-theory/collatz/)
- **Erdős–Straus conjecture** — Erdős, P. "Az 1/x₁ + 1/x₂ + … + 1/xₙ = a/b egyenletről." *Mat. Lapok* 1 (1950), 192–210. [Submodule](number-theory/erdos-straus/)
- **Goldbach's conjecture** — Helfgott, H. A. "The ternary Goldbach conjecture is true." arXiv:1312.7748, 2013. [Submodule](number-theory/goldbach/)
- **Legendre's conjecture** — Legendre, A.-M. *Essai sur la Théorie des Nombres*. 2nd ed., 1808. [Submodule](number-theory/legendre/)
- **New Mersenne conjecture** — Bateman, P. T.; Selfridge, J. L.; Wagstaff, S. S. Jr. and later expositions on Mersenne conjectures. [Wikipedia summary](https://en.wikipedia.org/wiki/Mersenne_conjectures#New_Mersenne_conjecture). [In-repo project](number-theory/new-mersenne/)
- **Oppermann's conjecture** — Oppermann, L. "Om vor Kundskab om Primtallenes Mængde mellem givne Grændser." *Oversigt Dansk. Vidensk. Selsk. Forh.* (1882), 169–179. [Submodule](number-theory/oppermann/)
- **Fortune's conjecture** — Guy, R. K. *Unsolved Problems in Number Theory*. 3rd ed., Springer, 2004 (Fortunate numbers section). [In-repo project](number-theory/fortune/)
  - Golomb, S. W. "A connected graph associated with the fortunate numbers." *Amer. Math. Monthly* 88 (1981), 113–115.
  - Kaczorowski, J.; Szydło, B. "On the conjecture of Reo Fortune concerning certain quadratic congruences." *Math. Comp.* 76 (2007), 249–258.
  - Čejchan, A.; Křížek, M.; Somer, L. "There are no sign changes in formulae involving prime numbers." *Rocky Mountain J. Math.* 48 (2018), 1165–1178. (Source of primorial interval theorems formalized in `Fortune.Literature`.)
  - Křížek, M.; Luca, F.; Somer, L. *17 Lectures on Fermat Numbers: From Number Theory to Geometry*. Springer, 2022. (Section 2.4 surveys Fortune-related primorial interval theorems.) Open chapter PDF: <https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.pdf>
  - OEIS Foundation Inc. *A005235* (Fortunate numbers), with computational notes and links. <https://oeis.org/A005235>
- **Twin prime conjecture** — de Polignac, A. "Six propositions arithmologiques déduites du crible d'Ératosthène." *Nouv. Ann. Math.* 8 (1849), 423–429. [Submodule](number-theory/twin-prime/)

## Combinatorics

### General references

- van Lint, J. H. & Wilson, R. M. *A Course in Combinatorics*. 2nd ed., Cambridge University Press, 2001.
- Stanley, R. P. *Enumerative Combinatorics*. Vol. 1 & 2, Cambridge University Press.

### Formalized conjectures

- **Dittert conjecture** — N. J. Cavenagh, J. Hämäläinen, C. M. Wanless, "On Dittert's conjecture," *Electronic Journal of Combinatorics* (2008). [In-repo project](combinatorics/dittert/)
- **Gold partition conjecture** — M. Peczarski, "The Gold Partition Conjecture," *Order* 29 (2012), 321–336. [In-repo project](combinatorics/gold-partition/)
- **Hadamard conjecture** — Hadamard, J. "Résolution d'une question relative aux déterminants." *Bull. Sci. Math.* 17 (1893), 240–246. [Submodule](combinatorics/hadamard-conjecture/)
- **Sensitivity conjecture** (now theorem) — Huang, H. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." *Ann. of Math.* 190 (2019), 949–955. [Submodule](combinatorics/sensitivity/)

## Algebra

### General references

- Lang, S. *Algebra*. Revised 3rd ed., Springer GTM 211.
- Rotman, J. J. *An Introduction to the Theory of Groups*. 4th ed., Springer GTM 148.

### Formalized conjectures

- **Herzog–Schönheim conjecture** — Herzog, M. & Schönheim, J. "Research problem No. 9." *Canad. Math. Bull.* 17 (1974), 150. [Submodule](algebra/herzog-schonheim/)

## Graph Theory

### General references

- Diestel, R. *Graph Theory*. 5th ed., Springer GTM 173, 2017.
- Bondy, J. A. & Murty, U. S. R. *Graph Theory*. Springer GTM 244, 2008.

### Formalized conjectures

- **Reconstruction conjecture** — Kelly, P. J. "A congruence theorem for trees." *Pacific J. Math.* 7 (1957), 961–968. Ulam, S. M. *A Collection of Mathematical Problems*. Interscience, 1960. [Submodule](graph-theory/reconstruction-conjecture/)

## General Problem Collections

- Guy, R. K. *Unsolved Problems in Number Theory*. 3rd ed., Springer, 2004.
- Croft, H. T.; Falconer, K. J. & Guy, R. K. *Unsolved Problems in Geometry*. Springer, 1991.
- Wikipedia. [List of conjectures](https://en.wikipedia.org/wiki/List_of_conjectures).
