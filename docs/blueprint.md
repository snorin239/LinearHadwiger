# Formalization blueprint

Source: paper/main.tex and paper/main.pdf. Theorem 2 is the first major
formalization goal; Theorem 1 remains the final objective.

| Paper result | Proposed Lean result | Status |
| --- | --- | --- |
| Theorem 1 (thm:linear) | To be chosen | Unformalized |
| Theorem 2 (thm:quantitative) | quantitative_bound | Unformalized; first goal |
| Reed--Seymour (1.3), eq:RS | reed_seymour_bound | Unformalized; proof required |
| Exponent bootstrap (thm:bootstrap) | To be chosen | Unformalized |

## Theorem 2 dependency map

Theorem 2 (paper/main.tex:184-190, proof 278-946) states that for every finite
graph G and 0 < epsilon <= 1,

    chi(G) <= 4 h(G) + epsilon |V(G)| + (100/epsilon)^(2000/epsilon^2).

The proof follows these dependencies:

1. Almost-perfect matching for nearly regular, low-codegree multihypergraphs
   (lem:matching, 316-498).
2. Token/dummy hypergraph construction, concentration and low-pair-load
   fractional-coloring rounding (lem:rounding, 506-600), using step 1.
3. Pair-constrained LP duality and bounded-degree nonedge augmentation
   (lem:augmentation, 608-703), using step 2.
4. Independent transversal and weighted matching with no short cycle through
   a matching edge (lem:transversal and lem:weighted, 722-814).
5. Matching contraction, dual-weight transfer and the proved Reed--Seymour
   bound chi_f(Q) <= 2 h(Q) (prop:robust, 712-720 and 816-856), using step 4.
6. Combine augmentation and robustness, remove large stable sets, and verify
   the explicit constants (860-946). Theorem 2 does not depend on the later
   bootstrap or Delcourt--Postle results.

Reed--Seymour's original proof
(https://cgm.cs.mcgill.ca/~breed/SummerNSERC04/frachad.pdf) uses LP duality
and a weighted stable-set theorem. Its combinatorial core is an egg
decomposition: connected pieces with half-weight independent yolks and a
chordal touching quotient. An induced-path parity obstruction, a minimal
bipartite connector and maximal support produce the decomposition.

## Proposed dependency-ordered Lean modules

Paths are relative to HadwigerLean/. Rows 1-9 are checked; later rows are
proposed. Independent modules may be built concurrently.

| Order | Module | Main contents |
| --- | --- | --- |
| 1 | Graph/Finite.lean | Finite SimpleGraph conventions; natural-valued chromatic number bridged to Mathlib's Nat-infinity chromaticNumber; stable sets and independence number. Checked. |
| 2 | Graph/Minor.lean | Connected branch-set minor model, clique-minor number h with h(empty)=0, transitivity and monotonicity. Checked. |
| 3 | Vendor/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean; Farkas.lean; Math/LinearProgramming/StrongDuality.lean | Apache-2.0 source for Farkas' lemma and finite covering-LP strong duality, copied from EconCSLib commit `cef01c7` with attribution; all three files compile under Lean 4.32.1. |
| 4 | Optimization/FiniteLP.lean | Generic finite covering LP, weak duality, compact primal sublevels, primal attainment, and a bridge to the vendored strong-duality theorem. Checked. |
| 5 | Coloring/Fractional.lean | Stable-set primal weights, vertex coverage, dual vertex weights, chi_f and weak duality; imports 1. Checked. |
| 6 | Coloring/FractionalLP.lean | Exact primal/dual LP equivalences, attained fractional coloring and dual optimum; imports 4-5. Checked. |
| 7 | Coloring/PairLoad.lean | Unordered nonedge loads, exact primal/dual LP maps, and attained equal optima; imports 4-5. Checked. |
| 8 | Coloring/IntegralComparison.lean | The bound chi_f(G) <= chi(G) from nonempty color classes. Checked. |
| 9 | Graph/TouchingQuotient.lean | Connected partition quotient and clique-minor lift; imports 2. Checked. |
| 10 | Graph/SimplicialElimination.lean | Hereditary simplicial elimination and coloring by clique number; imports 1. |
| 11 | ReedSeymour/Egg.lean | Yolks, eggs, partial decompositions, support and bipartite half-weight yolks; imports 9-10. |
| 12 | ReedSeymour/Parity.lean | Odd induced-path obstruction and bipartite minimal connector; imports 11. |
| 13 | ReedSeymour/Decomposition.lean | Star quotient, two quotient updates, maximal support and all-egg decomposition; imports 12. |
| 14 | ReedSeymour/Bound.lean | Weighted stable-set bound, then chi_f(G) <= 2 h(G), including the empty graph; imports 2, 6 and 13. |
| 15 | Hypergraph/Indexed.lean | Uniform multihypergraphs with indexed edge copies, degree, codegree and matching. |
| 16 | Probability/FiniteBernoulli.lean | Independent marking, survival and moment formulas, concentration. |
| 17 | Hypergraph/AlmostPerfectMatching.lean | Parameter inequalities, one-round deficit/waste, iteration and lem:matching; imports 15-16. |
| 18 | Coloring/LowCodegreeRounding.lean | Token/dummy construction, sampling and coloring extraction; imports 5 and 15-17. |
| 19 | Coloring/Augmentation.lean | Exact-load normalization, penalty threshold graph and lem:augmentation; imports 4, 7 and 18. |
| 20 | Graph/WeightedMatching.lean | Independent transversal, greedy distance-excluding matching, unmatched-set and weight-loss bounds; imports 1. |
| 21 | Coloring/RobustFractional.lean | Matching contraction, dual-weight transfer and prop:robust; imports 2, 6, 14 and 20. |
| 22 | Quantitative/Constants.lean | Arithmetic estimates for mu, n0, d, K and the stated A_epsilon. |
| 23 | Quantitative/Theorem2.lean | Bounded-independence case, stable-set removal and exact Theorem 2 bound; imports 19, 21 and 22. |

Import Quantitative/Theorem2 from HadwigerLean.lean only when it checks.
Theorem 1's bootstrap and other later external inputs are subsequent work.

## Modeling choices to validate in Lean

- Use finite simple graphs on a Fintype vertex type, stating numeric bounds
  over the reals. Preserve the paper's explicit real exponent in A_epsilon.
- Define minors by connected branch sets. The pinned Mathlib cache has
  ordinary coloring and independent sets, but no graph-minor or fractional
  coloring interface was found.
- Carry a simplicial-elimination invariant through Reed--Seymour's quotient
  updates. This gives the needed coloring bound without a general chordal
  characterization.
- Use indexed hyperedges: Mathlib's Hypergraph edge set discards repeated
  copies. Bernoulli marks with the paper's Poisson zero probabilities avoid
  explicit Poisson random variables without changing the survival formulas.
- Use the checked EconCSLib Fourier--Motzkin/Farkas/strong-duality proof for
  the generic finite LP. `FiniteLP.Problem.exists_dual_ge` transports its
  `Fin n` column indexing through `Fintype.equivFin`. Positive costs yield
  compact primal sublevels and attained equal optima. Fractional coloring is
  identified with this LP in `Coloring/FractionalLP.lean`; pair-load rows are
  modeled separately. The vendored README records the exact source commit,
  Apache-2.0 license, and import-only modifications.

## External results and dependencies

Reed--Seymour is part of this first milestone and is not an axiom. Theorem 2
has no other cited external graph theorem in its proof. Delcourt--Postle and
other later external results are dependencies of Theorem 1; their Lean proof
strategies remain to be determined. No external result has been assumed as
an axiom in the Lean source.
