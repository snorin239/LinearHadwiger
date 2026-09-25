# Formalization blueprint

Source: paper/main.tex and paper/main.pdf. Theorem 2 is the first major
formalization goal; Theorem 1 remains the final objective.

| Paper result | Proposed Lean result | Status |
| --- | --- | --- |
| Theorem 1 (thm:linear) | `linear_of_theorem4_corollary24`; public branch-set wrapper | Unformalized; conditional milestone planned |
| Theorem 2 (thm:quantitative) | `Theorem2.quantitative_bound`; Mathlib-facing wrapper planned | Checked internally; public wrapper pending |
| Reed--Seymour (1.3), eq:RS | ReedSeymour.reed_seymour_bound | Checked for every finite simple graph, including the empty graph |
| Exponent bootstrap (thm:bootstrap) | `LocalLinearBound` improvement from Corollary 24 | Unformalized |

## Conditional Theorem 1 milestone

The next milestone derives Theorem 1 from the checked Theorem 2 while taking
paper Theorem 4 (Delcourt--Postle small-graph reduction) and Corollary 24
(outer recursion bound) as explicit theorem hypotheses, not global Lean
axioms. The deduction also formalizes connected-bipartite packing,
induced-path localization, chromatic separation, and the exponent
bootstrap. Theorem 5 is unnecessary for this conditional deduction:
a sufficiently-large-t linear bound extends to all t >= 2 by
monotonicity of clique-minor order and a larger absolute constant.

The public Theorem 1 statement will conclude G.Colorable (C * t) and
expand the absence of a K_t minor into connected, disjoint, pairwise
touching branch sets. The pinned Mathlib has no graph-minor predicate.
A Mathlib-facing Theorem 2 wrapper will use G.chromaticNumber and the
explicit numeric term. Checked bridges connect both public statements
to the internal graph-minor and chromatic-number APIs.

The dependency order, four work lanes, input interfaces, and completion
checks are recorded in [theorem1-plan.md](theorem1-plan.md).

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

Paths are relative to HadwigerLean/. Checked modules and remaining proof
obligations are distinguished below. Independent modules may be built concurrently.

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
| 10 | Graph/SimplicialElimination.lean; Graph/CliqueMinor.lean | Hereditary simplicial elimination, clique-number coloring, relabeling and simplicial-set extension; cliqueNum <= cliqueMinorNumber. Checked. |
| 11 | ReedSeymour/Egg.lean; Absorption.lean | Real-weight yolks and eggs; half-weight bipartition yolks; no-cross union and bipartite connector absorption. Checked. |
| 12 | ReedSeymour/FiniteAveraging.lean; QuotientWeight.lean; LPBridge.lean | Color-class averaging, stable-set extraction from a colored egg partition, and LP-dual conversion to chi_f <= 2h. Checked. |
| 13 | ReedSeymour/Parity.lean; ParityStems.lean; ParityConclusion.lean | Odd-cycle gates, joined induced odd connector, and minimal connected transversal without odd connectors -> bipartite. Checked. |
| 14 | ReedSeymour/Partial.lean; Initial.lean | Partial egg invariant, relabeling, initial component partition, and maximal-support selection. Checked. |
| 14a | ReedSeymour/Decomposition.lean | Abstract and concrete central split, quotient PEO preservation, strict support growth, minimal terminal-hitting connector, and induced-graph minimality bridge. Checked. |
| 14b | ReedSeymour/Fusion.lean; PathBipartite.lean; ConnectorLift.lean | Odd-path parity classes, ambient connector transport, absorption into a neighboring egg, quotient update, and strict support growth. Checked. |
| 14c | ReedSeymour/Reindex.lean; Strategy.lean | Finite relabeling and the complete no-odd-connector improvement branch. Checked. |
| 14d | ReedSeymour/Bound.lean; Maximal.lean; Conclusion.lean | Weighted stable-set bridge, empty-graph case, maximal-support contradiction, and conditional assembly. Checked. |
| 14e | ReedSeymour/Theorem.lean | Discharges the odd-connector improvement hypothesis and proves the unconditional fractional bound. Checked. |
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

## Reed--Seymour proof

The unconditional theorem `ReedSeymour.reed_seymour_bound` in
`ReedSeymour/Theorem.lean` proves `fractionalChromaticNumber G ≤ 2 *
cliqueMinorNumber G` for every finite simple graph, including the empty
graph. It is imported by `HadwigerLean.lean` and checked by `lake build`.

The proof follows Reed and Seymour's maximal-support egg decomposition.
A minimum connected terminal-hitting set is either bipartite, giving a new
egg by splitting the central block, or it contains an odd induced terminal
path. In the latter case, a neighboring egg absorbs that path; the fused
quotient retains simplicial elimination and egg support grows. Finite
maximality therefore yields an all-egg decomposition. Quotient coloring,
weighted yolks, and the checked finite LP duality give the fractional bound.

The paper uses rational vertex weights; Lean uses real weights because the
existing fractional-coloring dual is real-valued. The egg argument applies
to finite real sums and order without changing the combinatorial proof.

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


## Active Theorem 2 parallel implementation

The durable task assignment, dependency order, and resumption log are in
`docs/theorem2-plan.md`. The first checked milestone is exact vertex-load
normalization for the pair-constrained LP. The hypergraph representation will
use a finite edge-copy index type; probability results will be polymorphic in
that index type. The augmentation lane may prove a conditional theorem from
an explicit rounding hypothesis, which will be discharged when the rounding
module is checked. The graph lane will use `SimpleGraph.edist` for distance
exclusion and a concrete matching contraction minor.

## Intermediate-statement simplification (user guidance, 2026-09-24)

The final Lean theorem should preserve the paper's stated bound, but helper
lemmas may use stronger or slacker hypotheses and conclusions. In particular,
the augmentation module now offers
exists_boundedDegree_augmentation_of_cap: any natural degree cap above the
real estimate suffices. This lets later arguments use convenient integer
caps without carrying exact ceilings through combinatorial proofs. Matching,
rounding, and robust-bound interfaces should similarly expose only the
inequalities needed downstream. Keep real error budgets until an actual
finite cardinality or coloring count requires a natural number.

## Checked assembly checkpoint (2026-09-24)

Quantitative/Peeling.lean checks maximal disjoint stable-set peeling and a
bounded-independence-to-arbitrary-graph theorem. Quantitative/Constants.lean
checks the bounded-independence assembly under explicit rounding and robust
fractional-coloring assumptions, then the exact final Theorem 2 inequality
under the bounded-independence hypothesis and `A <= Aepsilon`. The numerical
chain now proves `mu^(-1) <= (100/epsilon)^(300/epsilon)` and
`d+1 <= (100/epsilon)^(304/epsilon)` for `0 < epsilon <= 1`.
The current root `lake build` passed (3335 jobs). Theorem 2 itself remains
unformalized until the matching, rounding, robust greedy trace, and final
constant estimate are discharged.

## Explicit constant and support lemmas (2026-09-24)

`Quantitative/Constants.lean` now proves `A_le_Aepsilon`, preserving the
paper's exact real exponent. Its intermediate bounds are
`n0 <= (100/epsilon)^(1208/epsilon^2)` and
`robustAdditive <= (100/epsilon)^(1826/epsilon^2)`; their extra slack removes
unneeded floor/ceiling arithmetic. `Quantitative/Theorem2.lean` checks
`quantitative_bound_of_rounding_and_robust`, a theorem with explicit
bounded-independence rounding and robust-fractional assumptions for every
finite graph of the current universe. Those assumptions are pending proofs,
not axioms.

`Quantitative/Recurrence.lean` checks a finite survivor/deficit/waste sum.
`Quantitative/BackwardPotential.lean` checks nonnegative backward weights,
terminal and step identities, and a quadratic bound on the initial survivor
weight. `Quantitative/UnionBound.lean` checks the strict exponential union
budget with the centered Chernoff exponent `mu^2*n/256`. These standalone
lemmas are built and available to the matching and rounding lanes.

## Matching schedule and robust bridge (2026-09-24)

The matching iteration now has a checked concrete application in
`Quantitative/MatchingApplication.lean`. The integer degree caps are
`matchingD D0 r xi 0 = D0` and
`matchingD D0 r xi (i+1) = floor(exp(-(r-1)a) * D_i)`, while all error
estimates are stated over real numbers. A direct invariant
`B <= b * D_i` absorbs every floor loss; it follows from
`b*T <= 1` and avoids a separate geometric error sum. The paper's
small parameter gives `b <= a/4`, hence `a*D_i >= 4`. This is enough
for the per-round floor consequences used by the finite matching theorem.
The initial deficit is exposed as a minimum-degree condition, which is
the form produced by the sampled hypergraph.

The robust fractional coloring input is checked unconditionally in
`Coloring/RobustFractional.lean` and matched to the paper's exact
additive term by `Quantitative/RobustBridge.lean`. Consequently
`Quantitative/Theorem2.lean` now needs only the universal
low-codegree rounding inequality. The paper's final numerical
`Aepsilon` bound has already been checked; proving that rounding
inequality is the remaining logical gate for Theorem 2.
## Theorem 2 checked completion (2026-09-24)

`HadwigerLean.Theorem2.quantitative_bound` in
`Quantitative/Theorem2FinalBridge.lean` is the unconditional checked
formalization of paper Theorem 2. It states
`chromatic G <= 4 * cliqueMinorNumber G + epsilon * |V| +
Aepsilon epsilon` for every finite graph and `0 < epsilon <= 1`;
`Aepsilon` is defined as `(100/epsilon)^(2000/epsilon^2)`.
`Quantitative/RoundingBridge.lean` discharges the low-codegree
rounding input, and `Quantitative/RobustBridge.lean` discharges the
robust fractional input. The root `lake build` passed (3436 jobs).
There are no proof placeholders or new axiom declarations in the
Theorem 2 modules. The earlier conditional assembly checkpoints above
record the development path and should not be read as the current
proof status.

## Theorem 4 and Corollary 24 proof architecture (2026-09-24)

The mathematical working manuscript is
docs/theorem4-corollary24-proof.md. It is a proof document, not Lean
code or a checked theorem. Its two endpoint deductions share one
outer induction on scales a = (2/3)^i T and the up-to-b woven
property W(a,b;X). The paper-to-Lean mapping should use a finite
family of terminal pairs with cardinality at most b; the published
exactly-b formulation is only equivalent after an order/padding
argument, and several recursive uses have fewer than b paths.

Both endpoints use the additive Girão–Narayanan connected high-chromatic
hub and the same low-scale clique-minor density base. Corollary 24 then
uses its assumed chromatic separability; Theorem 4 derives that
separability through Delcourt–Postle's chromatic-inseparable argument.
The shared rooted-minor-to-woven construction tests connectivity and
minor existence after deleting all occupied original roles and
assigning distinct neighbor proxies. A minor in the undeleted graph
alone is insufficient for that construction.

The manuscript contains standalone proofs of the set Menger theorem,
the additive Girão–Narayanan theorem, the needed Mader
density-to-connectivity lemma, Kawarabayashi's rooted clique-minor
lemma, the Norin–Postle unbalanced bipartite bound, and
16k-connectivity implying k-linkedness. It also proves the
quantitative clique-minor density bound with coefficient 30
(Appendix E) and a rooted density theorem with threshold
12c+5000h (Appendix F), which replaces the cited Wollan theorem
for the parameters needed here. The appendices discharge all
non-elementary mathematical leaves used by the two endpoints.
Independent adversarial audits checked the quantitative and
rooted-minor appendices; the status of the manuscript is a
self-contained **mathematical** proof, not a Lean proof.

The Lean implementation should preserve the shared W(a,b;X)
interface and first establish the common finite Menger and
rooted-clique-minor infrastructure. The density and rooted-minor
proofs are substantial later modules; Appendix F's massed-pair
invariant and rigid truncation should be explicit reusable
interfaces. The manuscript records repairs to the printed
Delcourt–Postle base case, up-to-b use, woven parameter range,
singleton knitting stage, linkage containment, and final
constants. Neither endpoint should be marked formally proved
in Lean until all of these arguments have been implemented
without placeholders. No Lean source was changed for this
documentation checkpoint.

## Checked common graph inputs (Stage 2, 2026-09-25)

The five common inputs to the outer woven construction are now checked
Lean theorems. Their paper-to-Lean mapping is:

| Paper input | Lean endpoint |
| --- | --- |
| Girão--Narayanan chromatic connectivity (GN) | `exists_chromatic_connected_induced` in `Graph/ChromaticConnectivity/Theorem.lean` |
| Mader density-to-connectivity bound | `hasVertexConnectedInducedSubgraph_of_edgeDensity_ge` in `Graph/DensityConnectivity.lean` |
| Kawarabayashi rooted clique minor (KR) | `rootedCliqueMinor_of_connected_cliqueMinor` in `Graph/RootedCliqueMinor/Dichotomy.lean` |
| 16k-connected implies k-linked (L) | `Linkedness.kLinked_of_sixteen_mul_vertexConnected` in `Graph/Linkedness/Final.lean` |
| Coefficient-30 clique-minor density theorem (KT) | `hasCliqueMinor_of_edgeDensity_ge` in `Graph/CliqueDensity/Theorem.lean` |

The linkedness proof uses finite massed pairs, rigid min-cuts, torso
linkage gluing, and induction on the order. Its final theorem is
unconditional. All five endpoints were built with Lake; the root
`lake build` passed after their imports were added. The linkedness
endpoint's `#print axioms` lists only `propext`,
`Classical.choice`, and `Quot.sound`.

## Checked shared outer induction (Stage 3, 2026-09-25)

The finite shared scale recursion is checked in
`Woven/OuterInductionComplete.lean`. Its top result
`outerAt_top_of_contracts` assumes only a base-scale woven claim and
explicit hub and chromatic-separation contracts for each induced host.
The nonbase theorem `woven_nonbase_of_hub_separation` in
`Woven/OuterNonbaseStep.lean` discharges the entire geometric step:
normalization and distinct proxies, the large-clique-minor branch,
the low-chromatic hub and double fan, GN residual extraction, and
three connected woven children assembled into a rooted model.

`OuterAt` quantifies over every finite induced subgraph of a fixed
host; `outerAt_induce` transports it through nested induced vertex
types. The scale is `2^i 3^(m-i)`, with `3 * child = 2 * parent`.
The child color-loss ledger is
`outerChildLoss a K h σ = (45 + 12K)a + h + 2σ`.
Original roles may coincide; each occurrence receives a distinct
neighbor proxy outside all original role vertices. The double fan is
colored with at most four colors per proxy, and the output retains the
up-to-`3a` terminal-pair convention. These checked theorems remain
conditional on the base, hub, and separation inputs, which the
Corollary 24 and Theorem 4 specializations must supply.

## Checked Corollary 24 (Stage 4, 2026-09-25)

`Deduction.corollary24_proved` in
`Deduction/Corollary24Complete.lean` proves
`Corollary24Statement` unconditionally. It uses the shared outer
induction with \(K=10000\), \(B=10^6(d+1)\), \(U=2000T\),
\(h(a)=980a\), and \(\sigma(a)=14da\).
`Corollary24BaseWoven.lean` applies the checked coefficient-30 KT
minor theorem at every scale below the logarithmic cutoff after
normalizing repeated role occurrences. `Corollary24HubContract.lean`
obtains the 980a-color hub from a chromatic slice and GN.
`Corollary24SepContract.lean` transports the paper's minor-free
separability premise to each normalized induced graph.
`OuterInductionMixed.lean` handles the fact that several final
integer scales may be below the cutoff. The last scale's cutoff
inequality and all remaining integer budgets have separate checked
lemmas. The final step uses GN and the top woven claim to obtain a
forbidden clique minor. The endpoint passes `assert_no_sorry`;
`#print axioms` lists only `propext`, `Classical.choice`, and
`Quot.sound`.
