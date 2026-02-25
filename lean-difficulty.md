# Lean 4 Formalization Difficulty Assessment

[← Back to Index](README.md)

Estimated difficulty of formalizing each conjecture in Lean 4 with Mathlib,
assessed along two axes:

## Rating Scale

### Statement Difficulty (S) — How hard to *state* the conjecture

| Rating | Label | Meaning |
|--------|-------|---------|
| S1 | Elementary | Basic arithmetic, primes, natural numbers. All definitions in Mathlib. |
| S2 | Standard | Standard definitions mostly in Mathlib or easy to add. |
| S3 | Moderate | Some definitions not in Mathlib but conceptually straightforward. |
| S4 | Substantial | Needs significant infrastructure partially or not yet formalized. |
| S5 | Deep | Requires vast machinery far from formalized (schemes, L-functions, étale cohomology, etc.). |

### Proof Difficulty (P) — For proved theorems, how hard to formalize the proof

| Rating | Label | Meaning |
|--------|-------|---------|
| P1 | Short | A few lines to a page; elementary. |
| P2 | Moderate | Nontrivial but bounded; a focused effort. |
| P3 | Long | Extended proof using standard but substantial techniques. |
| P4 | Deep | Requires formalizing significant background theory. |
| P5 | Monumental | Hundreds of pages, or computer-assisted, or depends on classification-scale results. |

---

## Summary Statistics

| Tier | Open | Proved | Disproved | Total |
|------|------|--------|-----------|-------|
| S1   | 12   | 5      | 3         | 20    |
| S2   | 42   | 15     | 11        | 68    |
| S3   | 17   | 14     | 5         | 36    |
| S4   | 17   | 11     | 4         | 32    |
| S5   | 15   | 13     | 1         | 29    |

---

## Open Problems

### Number Theory

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | abc conjecture | S2 | Radical of n, coprimality, exponent bounds. All elementary to define. |
| 2 | Agoh–Giuga conjecture | S2 | Bernoulli numbers (in Mathlib), primality test equivalence. |
| 3 | Agrawal's conjecture | S2 | Polynomial rings over Z/nZ. Polynomial infrastructure exists. |
| 4 | Andrica's conjecture | S2 | Needs nth prime function and real square roots. |
| 5 | Artin conjecture (L-functions) | S5 | Artin L-functions, Galois representations, holomorphicity. None formalized. |
| 6 | Artin's conjecture on primitive roots | S2 | Primitive roots in Mathlib. Statement: infinitely many primes for which a is a primitive root. |
| 7 | Bateman–Horn conjecture | S3 | Asymptotic density of prime values of polynomials. Needs asymptotic analysis of prime counting. |
| 8 | Beal's conjecture | S1 | A^x + B^y = C^z with x,y,z > 2 implies gcd > 1. Purely elementary. |
| 9 | Beilinson conjecture | S5 | Motivic cohomology, special values of L-functions, regulators. Very deep. |
| 10 | Birch and Swinnerton-Dyer | S5 | Elliptic curves (partially in Mathlib), L-functions, analytic rank. L-functions not formalized. |
| 11 | Birch–Tate conjecture | S5 | Algebraic K₂ of rings of integers, Dedekind zeta values. |
| 12 | Bloch–Beilinson conjectures | S5 | Chow groups, Abel-Jacobi maps, filtrations on algebraic cycles. |
| 13 | Brocard's conjecture | S2 | Between p_n² and p_{n+1}² there are ≥ 4 primes. Needs prime enumeration. |
| 14 | Brumer–Stark conjecture | S5 | Class field theory, Artin L-functions, Brumer-Stickelberger element. |
| 15 | Bunyakovsky conjecture | S2 | Irreducible polynomials over Z taking infinitely many prime values. |
| 16 | Carmichael totient conjecture | S1 | For every n, the preimage φ⁻¹(n) has size ≠ 1. Euler's totient in Mathlib. |
| 17 | Catalan–Dickson conjecture | S2 | Aliquot sequences (sum-of-divisors iteration) terminate or cycle. |
| 18 | Catalan's Mersenne conjecture | S2 | Iterated Mersenne numbers. Elementary sequence definition. |
| 19 | Collatz conjecture | S1 | The 3n+1 function eventually reaches 1. Completely elementary. |
| 20 | Cramér's conjecture | S2 | Prime gaps bounded by O((log p)²). Needs asymptotic notation for primes. |
| 21 | De Polignac's conjecture | S1 | For every even k, infinitely many primes p with p+k also prime. |
| 22 | Elliott–Halberstam conjecture | S3 | Prime distribution in arithmetic progressions, error terms with π(x;q,a). |
| 23 | Erdős–Straus conjecture | S1 | 4/n = 1/x + 1/y + 1/z has positive integer solutions for all n ≥ 2. |
| 24 | Firoozbakht's conjecture | S2 | p_n^(1/n) is strictly decreasing. Needs nth prime, real exponentiation. |
| 25 | Fortune's conjecture | S2 | Fortunate numbers (smallest m > 1 with p_n# + m prime) are all prime. |
| 26 | Four exponentials conjecture | S3 | Transcendence theory: linear independence over Q, exponentials. |
| 27 | Gauss circle problem | S3 | Error term in lattice point counting in circles. Needs asymptotics. |
| 28 | Gilbreath conjecture | S2 | Iterated absolute differences of primes always start with 1. |
| 29 | Goldbach's conjecture | S1 | Every even n ≥ 4 is the sum of two primes. |
| 30 | Goormaghtigh conjecture | S2 | Diophantine equation (x^m-1)/(x-1) = (y^n-1)/(y-1). |
| 31 | Grimm's conjecture | S2 | Consecutive composites can be assigned distinct prime divisors. |
| 32 | Keating–Snaith conjecture | S4 | Moments of Riemann zeta on the critical line. Needs complex zeta function. |
| 33 | Legendre's conjecture | S1 | There is a prime between n² and (n+1)². |
| 34 | Lemoine's conjecture | S1 | Every odd n ≥ 7 can be written as p + 2q for primes p, q. |
| 35 | Lenstra–Pomerance–Wagstaff | S3 | Asymptotic density of Mersenne primes. Needs heuristic formalization. |
| 36 | Leopoldt's conjecture | S5 | p-adic regulator of a number field is nonzero. Needs p-adic analysis, units of number fields. |
| 37 | Marshall Hall's conjecture | S2 | \|x² - y³\| > C·√x for x² ≠ y³. Elementary Diophantine inequality. |
| 38 | Montgomery's pair correlation | S4 | Pair correlation of zeros of ζ(s). Needs zeta zeros, distribution theory. |
| 39 | n conjecture | S2 | Generalization of abc to n coprime integers. Elementary statement. |
| 40 | New Mersenne conjecture | S2 | Equivalence of three conditions for odd primes. |
| 41 | Oppermann's conjecture | S2 | π(n²+n) - π(n²) ≥ 1 and π(n²) - π(n²-n) ≥ 1. Needs prime counting. |
| 42 | Pillai's conjecture | S2 | a^x - b^y = c has finitely many solutions. |
| 43 | Riemann hypothesis | S4 | Zeros of ζ(s). Complex zeta function not fully in Mathlib. Partial work exists in Lean/Mathlib. |
| 44 | Sato–Tate conjecture | S5 | Distribution of Frobenius traces on elliptic curves. Needs elliptic curves over finite fields, equidistribution. |
| 45 | Schanuel's conjecture | S3 | Transcendence degree of {α_i, e^{α_i}} over Q. Needs transcendence degree. |
| 46 | Schinzel's hypothesis H | S2 | Simultaneous prime values of integer polynomials under natural conditions. |
| 47 | Second Hardy–Littlewood | S2 | π(x+y) ≤ π(x) + π(y). Uses only prime counting function. |
| 48 | Selfridge's conjecture | S2 | No Wieferich prime is also a Wall–Sun–Sun prime. |
| 49 | Twin prime conjecture | S1 | Infinitely many p with p+2 prime. |
| 50 | Unicity for Markov numbers | S2 | Each Markov number determines unique Markov triple (up to permutation). |
| 51 | Vandiver's conjecture | S4 | p does not divide h⁺ of Q(ζ_p). Needs cyclotomic fields, class numbers. |
| 52 | Vojta's conjecture | S5 | Heights on varieties, proximity/counting functions. Deep Diophantine geometry. |
| 53 | Waring's conjecture | S2 | Exact formula for g(k) in Waring's problem. |

### Graph Theory

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | Conway's thrackle | S3 | Needs embedded/drawn graphs (topological graph theory). |
| 2 | Erdős–Faber–Lovász | S2 | Chromatic number of union of cliques. Basic graph coloring in Mathlib. |
| 3 | Erdős–Gyárfás | S2 | Cycle with power-of-2 length in graphs with min degree ≥ 3. |
| 4 | Goldberg–Seymour | S2 | Chromatic index bounds. Edge coloring definitions needed. |
| 5 | List coloring conjecture | S3 | List chromatic index = chromatic index. List coloring not in Mathlib. |
| 6 | Lovász conjecture | S3 | Hamiltonian paths in vertex-transitive graphs. Needs Hamiltonian path, vertex-transitivity. |
| 7 | Petersen coloring | S3 | Petersen-minor coloring of bridgeless cubic graphs. |
| 8 | Reconstruction conjecture | S2 | Graphs on ≥ 3 vertices determined by multiset of vertex-deleted subgraphs. |
| 9 | Ringel–Kotzig conjecture | S2 | Trees have graceful labelings. |
| 10 | Tuza's conjecture | S2 | Triangle cover vs. triangle packing. |
| 11 | Vizing's conjecture | S2 | γ(G□H) ≥ γ(G)·γ(H) for domination number. |

### Algebra

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | Hodge conjecture | S5 | Hodge decomposition, algebraic cycles, cohomology of complex manifolds. |
| 2 | MNOP conjecture | S5 | Donaldson–Thomas invariants, Gromov–Witten invariants. |
| 3 | Standard conj. on algebraic cycles | S5 | Weil cohomology theories, algebraic cycles, Lefschetz standard. |
| 4 | Tate conjecture | S5 | Étale cohomology, Galois representations, algebraic cycles. |
| 5 | Virasoro conjecture | S5 | Moduli of curves, Gromov–Witten invariants, Virasoro algebra action. |
| 6 | Weight monodromy | S5 | ℓ-adic cohomology, monodromy filtration, weight filtration. |
| 7 | Eilenberg–Ganea | S4 | Cohomological dimension, Eilenberg–Ganea dimension, CW complexes. |
| 8 | Novikov conjecture | S4 | Higher signatures, surgery theory, classifying spaces, assembly maps. |
| 9 | Whitehead conjecture | S3 | Subcomplex of aspherical 2-complex is aspherical. CW complexes partially formalized. |
| 10 | Bloch–Kato conjecture | S5 | Galois cohomology, Milnor K-theory, norm residue map. |
| 11 | Homological conjectures | S4 | Intersection multiplicity, local cohomology, big Cohen-Macaulay modules. |
| 12 | Serre's multiplicity conj. | S4 | Tor over local rings, intersection multiplicity, vanishing/positivity. |
| 13 | Jacobson's conjecture | S3 | Jacobson radical powers in Noetherian rings. Both concepts in Mathlib. |
| 14 | Kaplansky conjectures | S3 | Group rings, zero divisors, units. Group rings in Mathlib. |
| 15 | Köthe conjecture | S3 | Sum of two nil left ideals is nil. Nil ideals partially in Mathlib. |
| 16 | Andrews–Curtis | S3 | Balanced presentations of trivial group, AC-moves. |
| 17 | Cherlin–Zilber | S4 | Simple groups of finite Morley rank are algebraic. Needs model theory + group theory. |
| 18 | Herzog–Schönheim | S2 | Coset partition of a group cannot have all distinct indices. |
| 19 | Green's conjecture | S5 | Syzygies of canonical curves, Koszul cohomology, algebraic geometry of curves. |

### Geometry & Topology

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | Borel conjecture | S4 | Aspherical closed manifolds, homotopy equivalent ⇒ homeomorphic. |
| 2 | Bost conjecture | S4 | Assembly map variant of Baum–Connes. |
| 3 | Farrell–Jones | S4 | K- and L-theory assembly maps for group rings. |
| 4 | Hilbert–Smith | S4 | No faithful action of p-adic integers on a manifold. Needs p-adic groups, manifolds. |
| 5 | Carathéodory conjecture | S3 | Convex surfaces have ≥ 2 umbilical points. Needs differential geometry of surfaces. |
| 6 | Filling area conjecture | S4 | Systolic geometry, filling area of Riemannian 2-disc. |
| 7 | Bombieri–Lang | S5 | Varieties of general type, Zariski density of rational points. |
| 8 | Manin conjecture | S5 | Rational points on Fano varieties, height zeta functions, asymptotic counting. |
| 9 | Mazur's conjectures | S4 | Topology of rational points on varieties over number fields. |
| 10 | Uniformity conjecture | S5 | Uniform bound on rational points on curves of given genus. |
| 11 | Big-line-big-clique | S2 | Point sets in the plane, collinearity, cliques. Elementary discrete geometry. |
| 12 | Gilbert–Pollack (Steiner ratio) | S3 | Steiner trees in Euclidean plane, minimum spanning trees, ratio bounds. |
| 13 | Hopf conjectures | S4 | Sectional curvature, Euler characteristic, Riemannian manifolds. |
| 14 | Toeplitz' conjecture | S3 | Every Jordan curve inscribes a square. Needs Jordan curves, inscribed polygons. |
| 15 | Ulam's packing conjecture | S3 | Sphere has lowest packing density among convex bodies. Needs packing density. |

### Analysis

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | Brennan conjecture | S3 | Conformal mappings, integral conditions. |
| 2 | Sendov's conjecture | S2 | Polynomial zeros and critical points in the unit disk. Complex polynomials in Mathlib. |
| 3 | Bochner–Riesz | S4 | Fourier multiplier operators, L^p boundedness. Needs Fourier analysis infrastructure. |
| 4 | Invariant subspace problem | S3 | Bounded operator on separable Hilbert space has nontrivial invariant subspace. Hilbert spaces in Mathlib. |
| 5 | Baum–Connes | S5 | K-theory of group C*-algebras, assembly maps, classifying spaces. |
| 6 | Zauner's conjecture | S3 | SIC-POVMs: d² equiangular lines in C^d. Needs finite-dimensional Hilbert spaces, equiangularity. |

### Combinatorics & Order Theory

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | Dittert conjecture | S2 | Permanent function, doubly stochastic matrices. |
| 2 | Frankl conjecture | S1 | Union-closed families of sets have an element in ≥ half. Very elementary. |
| 3 | Hadamard conjecture | S2 | Hadamard matrix of order 4k exists for every k. |
| 4 | 1/3–2/3 conjecture | S2 | Partial orders, fraction of linear extensions with a < b. |
| 5 | Gold partition conjecture | S2 | Related to 1/3–2/3, about gold partitions of finite posets. |
| 6 | Rudin's conjecture | S3 | Λ(p) sets in additive combinatorics. Nontrivial definitions. |
| 7 | Scholz conjecture | S2 | Addition chain for 2n-1 is ≤ n-1 + addition chain for n. |
| 8 | Singmaster's conjecture | S1 | Binomial coefficient C(n,k) appears finitely many times for each value > 1. |

### Other Fields

| # | Conjecture | S | Notes |
|---|-----------|---|-------|
| 1 | Quantum PCP conjecture | S4 | Local Hamiltonians, quantum proof systems. Needs quantum computation formalization. |
| 2 | Unique games conjecture | S3 | Constraint satisfaction, approximation hardness. Needs complexity classes. |
| 3 | Berry–Tabor | S5 | Eigenvalue statistics of quantum integrable systems. Needs spectral theory on manifolds. |
| 4 | Quantum unique ergodicity | S5 | Eigenfunctions on Riemannian manifolds, weak-* convergence of measures. |
| 5 | Sarnak conjecture | S3 | Möbius function uncorrelated with bounded-complexity sequences. |
| 6 | Weinstein conjecture | S4 | Every contact manifold has a closed characteristic. Needs symplectic/contact geometry. |
| 7 | Casas-Alvero | S2 | Polynomial sharing root with each of its derivatives is a power of a linear form. |
| 8 | Jacobian conjecture | S3 | Polynomial map C^n → C^n with constant nonzero Jacobian is bijective. |
| 9 | Littlewood conjecture | S2 | lim inf n·‖nα‖·‖nβ‖ = 0 for all α, β. Fractional parts. |
| 10 | Deligne conjecture | S5 | Several formulations, all requiring deep homotopical/algebraic machinery. |
| 11 | Grothendieck–Katz p-curvature | S4 | Algebraic differential equations, p-curvature, algebraic solutions. |
| 12 | Birkhoff conjecture | S4 | Only elliptical billiard tables are integrable. Needs billiard dynamics. |
| 13 | Chowla conjecture | S3 | Correlations of the Liouville function vanish. |
| 14 | Ibragimov–Iosifescu | S3 | CLT for φ-mixing sequences under specific moment conditions. |
| 15 | Kung–Traub | S2 | Optimal order of multipoint iterative methods. |
| 16 | Pierce–Birkhoff | S4 | Piecewise polynomial functions are f-rings generated by polynomials. |

---

## Conjectures Now Proved (Theorems)

For proved theorems, both statement (S) and proof (P) difficulty are given.

| # | Theorem (former conjecture) | S | P | Notes |
|---|----------------------------|---|---|-------|
| 1 | Feit–Thompson (Burnside conj.) | S3 | P5 | 255-page proof. Odd order theorem. |
| 2 | Heawood conjecture | S3 | P4 | Genus of surfaces, graph embeddings. |
| 3 | Adams conjecture | S4 | P4 | J-homomorphism, K-theory operations. |
| 4 | Weil conjectures | S5 | P5 | Étale cohomology, Frobenius eigenvalues. ~15 years of development. |
| 5 | Blattner's conjecture | S4 | P4 | Representations of semisimple groups, K-types. |
| 6 | Mumford conjecture (Haboush) | S4 | P3 | Geometric invariant theory, reductive groups. |
| 7 | Four color theorem | S2 | P5 | Statement simple; proof is computer-assisted (already formalized in Coq). |
| 8 | Serre's conj. on proj. modules | S3 | P3 | Projective modules over polynomial rings are free. |
| 9 | Denjoy's conjecture | S3 | P3 | Rectifiable curves, Cauchy integral. |
| 10 | Kummer's cubic Gauss sums | S3 | P3 | Gauss sums, equidistribution. |
| 11 | Mordell conjecture (Faltings) | S4 | P5 | Curves of genus ≥ 2 have finitely many rational points. Deep proof. |
| 12 | Wagner's conj. (graph minor thm) | S2 | P5 | Well-quasi-ordering of graphs by minors. Statement easy; proof is enormous series. |
| 13 | Manin–Mumford | S4 | P4 | Torsion points on abelian varieties. |
| 14 | Smith conjecture | S3 | P4 | Fixed points of finite cyclic group actions on S³. |
| 15 | Bieberbach conjecture | S3 | P4 | Univalent functions, coefficient bounds. |
| 16 | Segal's conjecture | S4 | P4 | Stable cohomotopy of classifying spaces. |
| 17 | Sullivan conjecture | S4 | P4 | Maps from BG to finite complexes. |
| 18 | Oppenheim conjecture | S2 | P3 | Quadratic forms evaluated on integer lattice; Margulis's ergodic proof. |
| 19 | Weil's conj. on Tamagawa numbers | S5 | P5 | Algebraic groups, adelic volumes. Long case-by-case analysis. |
| 20 | Epsilon conjecture (Ribet) | S5 | P4 | Modular forms, Galois representations. |
| 21 | Conway–Norton (Moonshine) | S4 | P5 | Monster group, modular functions, vertex algebras. |
| 22 | Abhyankar's conjecture | S4 | P4 | Algebraic fundamental groups of curves, covers. |
| 23 | Fermat's Last Theorem | S1 | P5 | Statement trivial; proof (modularity) is monumental. |
| 24 | Dinitz conjecture | S2 | P2 | List coloring of complete bipartite graphs. |
| 25 | Alternating sign matrix conj. | S2 | P3 | Enumeration of ASMs; explicit product formula. |
| 26 | Milnor conjecture (K-theory) | S5 | P5 | Milnor K-theory mod 2, Galois cohomology. Voevodsky's motivic methods. |
| 27 | Kepler conjecture | S2 | P5 | Sphere packing density ≤ π/(3√2). Statement simple; proof computer-assisted (Flyspeck project completed in Lean-adjacent HOL Light). |
| 28 | Dodecahedral conjecture | S3 | P4 | Voronoi cells in sphere packings. |
| 29 | Gradient conjecture | S3 | P3 | Gradient flow trajectories have tangent lines at limit points. |
| 30 | Taniyama–Shimura (Modularity) | S5 | P5 | Every elliptic curve over Q is modular. Modularity lifting, Galois representations. |
| 31 | n! conjecture | S3 | P4 | Diagonal harmonics, Hilbert series. |
| 32 | Guralnick–Thompson | S4 | P4 | Composition factors of monodromy groups. |
| 33 | Catalan's conjecture (Mihăilescu) | S1 | P3 | x^p - y^q = 1 only solution (3²-2³). Statement trivial. |
| 34 | Strong perfect graph conj. | S2 | P5 | A graph is perfect iff no odd hole or odd antihole. Statement is simple; proof is 150+ pages. |
| 35 | Poincaré conjecture | S4 | P5 | Every simply connected closed 3-manifold is S³. Needs 3-manifolds, Ricci flow. |
| 36 | Geometrization conjecture | S5 | P5 | Thurston's 8 geometries for 3-manifolds. |
| 37 | Cameron–Erdős | S2 | P3 | Counting sum-free subsets of {1,...,n}. |
| 38 | Nirenberg–Treves | S4 | P4 | Local solvability of pseudo-differential operators, condition (Ψ). |
| 39 | Frobenius conjecture | S2 | P5 | Depends on classification of finite simple groups (tens of thousands of pages). |
| 40 | Stanley–Wilf | S2 | P2 | Permutation pattern avoidance grows at most exponentially. |
| 41 | Nagata's conj. on automorphisms | S3 | P3 | Wild automorphisms of polynomial rings in 3 variables. |
| 42 | Tameness conjecture | S4 | P5 | Hyperbolic 3-manifolds are topologically tame. |
| 43 | Road coloring conjecture | S2 | P3 | Aperiodic directed graphs have synchronizing colorings. |
| 44 | Serre's modularity conjecture | S5 | P5 | Odd irreducible 2-dimensional Galois representations are modular. |
| 45 | Surface subgroup conjecture | S4 | P4 | Closed hyperbolic 3-manifold groups contain surface subgroups. |
| 46 | Scheinerman's conjecture | S2 | P3 | Every planar graph is intersection graph of line segments. |
| 47 | Circular law | S3 | P3 | Eigenvalues of random matrices with iid entries converge to uniform on disk. |
| 48 | Hanna Neumann conjecture | S3 | P3 | Bound on rank of intersection of free group subgroups. |
| 49 | Hsiang–Lawson's conjecture | S3 | P4 | Clifford torus is unique minimal torus in S³. |
| 50 | Willmore conjecture | S4 | P4 | Willmore energy of torus in R³ ≥ 2π². Needs immersions, Willmore functional. |
| 51 | Bounded gap conjecture | S1 | P4 | lim inf (p_{n+1} - p_n) < ∞. Statement trivial; Zhang's proof deep. |
| 52 | Kadison–Singer problem | S3 | P3 | Paving conjecture for Euclidean spaces; solved via random polynomials. |
| 53 | Vinogradov main conj. | S3 | P4 | Mean-value estimate for exponential sums. Decoupling theory. |
| 54 | g-conjecture | S3 | P4 | f-vectors of simplicial convex polytopes / simplicial spheres. |
| 55 | Duffin–Schaeffer | S2 | P4 | Metric Diophantine approximation with arbitrary error function. |
| — | Deligne's conj. on 1-motives | S5 | P5 | 1-motives, Hodge realization, comparison isomorphisms. |
| — | Goldbach's weak conjecture | S1 | P4 | Every odd n ≥ 7 is sum of three primes. Statement trivial; Helfgott's proof uses deep analytic number theory. |
| — | Sensitivity conjecture | S1 | P2 | Boolean functions: sensitivity vs. degree/block-sensitivity. Huang's proof is short and elegant. |

---

## Disproved Conjectures

Statement difficulty (S) indicates how hard it is to state the conjecture.
A separate estimate (C) rates how hard the counterexample is to formalize.

| # | Conjecture | S | C | Notes |
|---|-----------|---|---|-------|
| 1 | Aharoni–Korman (fishbone) | S2 | C3 | Posets, well-founded partial orders. |
| 2 | Atiyah conjecture | S5 | C4 | L²-Betti numbers, von Neumann algebras. |
| 3 | Borsuk's conjecture | S2 | C3 | Can every bounded set in R^n be split into n+1 smaller-diameter pieces? |
| 4 | Chinese hypothesis | S1 | C1 | 2^p ≡ 2 mod p ⇒ p prime? Counterexample: 341 = 11 × 31. Trivial computation. |
| 5 | Doomsday conjecture | S4 | C4 | Homotopy theory, differentials in Adams spectral sequence. |
| 6 | Euler's sum of powers | S1 | C1 | Explicit numerical counterexample (Lander & Parkin, 1966). |
| 7 | Ganea conjecture | S4 | C4 | Lusternik–Schnirelmann category of product spaces. |
| 8 | Generalized Smith | S3 | C3 | Group actions on spheres, fixed point sets. |
| 9 | Hauptvermutung | S4 | C4 | Triangulations of manifolds, PL topology. |
| 10 | Hedetniemi's conjecture | S2 | C3 | χ(G×H) = min(χ(G), χ(H))? Shitov's counterexample (2019). |
| 11 | Hirsch conjecture | S2 | C3 | Diameter of polytope ≤ facets minus dimension. Santos's counterexample. |
| 12 | Kaplansky unit conjecture | S2 | C2 | Group rings of torsion-free groups. Gardam's counterexample. |
| 13 | Intersection graph conjecture | S2 | C2 | About word-representability of graphs. |
| 14 | Kelvin's conjecture | S3 | C3 | Optimal foam structure for equal-volume cells. |
| 15 | Kouchnirenko's conjecture | S3 | C3 | Polynomial systems, Newton polytopes. |
| 16 | Mertens conjecture | S2 | C3 | \|M(x)\| ≤ √x for Mertens function. Disproved by Odlyzko & te Riele (1985), non-constructive. |
| 17 | Pólya conjecture | S2 | C2 | L(n) ≤ 0 for Liouville function cumulative sum. |
| 18 | Ragsdale conjecture | S3 | C3 | Real algebraic curves, Harnack's theorem bounds. |
| 19 | Schoenflies conjecture | S3 | C3 | Topological embeddings of S² in R³. Alexander horned sphere. |
| 20 | Tait's conjecture | S2 | C2 | 3-connected cubic planar graphs are Hamiltonian. Tutte's counterexample. |
| 21 | Von Neumann conjecture | S2 | C3 | Non-amenable ⇒ contains free subgroup on 2 generators? Ol'shanskii's counterexample. |
| 22 | Weyl–Berry conjecture | S4 | C4 | Spectral asymptotics on fractal domains. |
| 23 | Williamson conjecture | S2 | C2 | About Williamson matrices for Hadamard matrix construction. |

---

## Refutations of Conventional Wisdom

| # | Belief refuted | S | C | Notes |
|---|---------------|---|---|-------|
| 1 | All numbers are rational | S1 | C1 | Irrationality of √2 already in Mathlib. Done. |
| 2 | Parallel postulate | — | — | Not a mathematical conjecture in formal sense; models of non-Euclidean geometry exist in Mathlib. |
| 3 | Fermat numbers are prime | S1 | C1 | 2^32+1 = 641 × 6700417. Arithmetic verification. |
| 4 | Transcendentals are rare | S2 | C2 | Cantor's cardinality argument. Countability of algebraics in Mathlib. |
| 5 | li(x) always > π(x) | S3 | C4 | Littlewood's existence proof is non-constructive. |
| 6 | Continuous ⇒ "usually" differentiable | S2 | C2 | Weierstrass function; nowhere differentiability formalizable. |
| 7 | Pólya conjecture | S2 | C2 | Same as disproved entry above. |

---

## Tier Summary for Open Problems — "Low-Hanging Fruit" for Lean 4

### Tier 1 (S1) — Immediately Statable

These can be stated in Lean 4 today with existing Mathlib, likely in under 10
lines:

- Beal's conjecture
- Carmichael totient conjecture
- Collatz conjecture
- De Polignac's conjecture
- Erdős–Straus conjecture
- Frankl conjecture (union-closed sets)
- Goldbach's conjecture
- Legendre's conjecture
- Lemoine's conjecture
- Singmaster's conjecture
- Twin prime conjecture

### Tier 2 (S2) — Statable with Minor Definitions

Require defining a few concepts (nth prime, graph coloring variants, etc.) but
all within reach of current Mathlib:

Most of number theory (abc, Andrica, Collatz variants, Gilbreath, etc.),
most graph theory (Erdős–Faber–Lovász, Tuza, Vizing, etc.),
Herzog–Schönheim, Casas-Alvero, Littlewood, and many others.

### Tier 5 (S5) — Requires Major Foundational Work

These need mathematical infrastructure that is years away from Mathlib:

- Artin conjecture on L-functions
- Beilinson conjectures / Bloch–Beilinson
- Birch and Swinnerton-Dyer
- Brumer–Stark conjecture
- All six algebraic geometry conjectures (Hodge, MNOP, Standard, Tate, Virasoro, Weight monodromy)
- Bloch–Kato (algebraic K-theory)
- Green's conjecture (algebraic curves)
- Bombieri–Lang, Manin, Uniformity (Diophantine geometry)
- Baum–Connes (operator K-theory)
- Berry–Tabor, QUE (quantum chaos)
- Deligne conjecture (monodromy)
- Leopoldt, Sato–Tate, Vojta (number theory)

---

## Most Interesting Formalization Targets

Combining mathematical significance with feasibility:

| Conjecture | S | Why interesting |
|-----------|---|-----------------|
| Collatz conjecture | S1 | Iconic, trivial to state, impossible to prove |
| Goldbach's conjecture | S1 | Famous, elementary, one line in Lean |
| Twin prime conjecture | S1 | Central to analytic number theory |
| Riemann hypothesis | S4 | Millennium Prize; ongoing Lean formalization efforts |
| Frankl conjecture | S1 | Recently solved (2022, Gilmer); proof may be formalizable |
| Sensitivity conjecture | S1/P2 | Proved; short elegant proof; excellent formalization target |
| Kepler conjecture | S2/P5 | Already formalized (Flyspeck, HOL Light); port to Lean possible |
| Four color theorem | S2/P5 | Already formalized in Coq; Lean port in progress |
| Fermat's Last Theorem | S1/P5 | Statement trivial; proof formalization is a major long-term project |
