# Formalization blueprint

Source: paper/main.tex and paper/main.pdf. Theorem 2 is checked. The
conditional Theorem 1 deduction is checked with exactly paper Theorem 4
and Corollary 24 as explicit hypotheses; neither input is proved here.

| Paper result | Lean result | Status |
| --- | --- | --- |
| Theorem 1 (thm:linear) | `Deduction.linear_of_theorem4_corollary24`; `Deduction.linear_mathlib_of_theorem4_corollary24` | Lean checked, conditional on exactly the two named paper inputs. Repository-wide `lake build` passed (3460 jobs). |
| Theorem 2 (thm:quantitative) | `Theorem2.quantitative_bound`; `Deduction.quantitative_bound_mathlib` | Checked internally and in the Mathlib-facing form. |
| Reed--Seymour (1.3), eq:RS | `ReedSeymour.reed_seymour_bound` | Checked for every finite simple graph, including the empty graph. |
| Exponent bootstrap (thm:bootstrap) | `Bootstrap.local_linear_bound_step_of_path`; `Bootstrap.path_localization` | Both checked; the final deduction discharges the path hypothesis using `path_localization`. |

## Conditional Theorem 1 implementation

`Deduction/ExternalInputs.lean` defines faithful propositions for Theorem 4
(the Delcourt--Postle small-graph reduction) and Corollary 24 (the outer
recursion bound). They are theorem arguments, not global Lean axioms.
`Bootstrap.path_localization` proves the remaining graph lemma. The
intermediate `Deduction.linear_of_theorem4_corollary24_of_path` retains
that lemma as a visible third hypothesis; the final theorem in
`Deduction/ConditionalTheorem1.lean` supplies its checked proof and has
only `Theorem4Statement` and `Corollary24Statement` as inputs.

The public linear theorem concludes `G.Colorable (C * t)` and expands
absence of a `K_t` minor into the nonexistence of connected, pairwise
disjoint, pairwise touching branch sets indexed by `Fin t`. The pinned
Mathlib has no graph-minor predicate. The checked Theorem 2 wrapper uses
`ENat.toNat G.chromaticNumber` and the explicit additive term
`(100 / epsilon) ^ (2000 / epsilon ^ 2)`. Both public statements have
proved bridges to the internal minor and chromatic-number APIs.

`Deduction/Audit.lean` passes `assert_no_sorry` for the final internal and
public conditional theorems. Its `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Theorem 5 is unnecessary
for this deduction: the checked finite-order extension uses monotonicity
of clique-minor order and enlarges the absolute constant.

The dependency order and acceptance checks are recorded in
[theorem1-plan.md](theorem1-plan.md).

## Theorem 1 paper-to-Lean map (2026-09-24)

The two external hypotheses have exact named interfaces in
`Deduction/ExternalInputs.lean`:

- Paper Theorem 4 (`thm:dp`, `paper/main.tex:212-227`) is
  `Theorem4Statement`. One integer `C_DP >= 1` occurs both in
  `chi(G) <= C_DP * t * (1 + f(G,t))` and in the order cutoff
  `|H| <= C_DP * a * (log a)^4`. The ratio set includes zero and ranges
  over arbitrary `H : G.Subgraph`, not only induced subgraphs, with
  `t / sqrt(log t) <= a <= t` and no `K_a` minor. Its `sSup` is a
  maximum: `theorem4RatioSet_finite` and `theorem4MaxRatio_mem` are
  checked. `theorem4_elimination` proves the pointwise form used in the
  final deduction.
- Paper Corollary 24 (`cor:outer`, `paper/main.tex:1382-1398`) is
  `Corollary24Statement`. It requires `t >= 100`, `d >= 1`, and `T`
  to be the least power of three at least `t`. `IsOuterScale T a`
  means `3^i * a = 2^i * T` for some natural `i`.
  `OuterSeparation G T d` quantifies over every such integer scale
  `a > T / sqrt(log T)` and every induced `Y`: if `Y` has no
  `K_(14a)` minor and `chi(Y) > 28da`, then it is
  `14da`-chromatic-separable. The conclusion keeps the strict bound
  `chi(G) < 3 * (10^6 * (d+1) + 62000) * t`.

The internal deduction follows the paper with these checked mappings:

| Paper step | Lean declarations | Mapping |
| --- | --- | --- |
| Theorem 2 (`thm:quantitative`, lines 184-190) | `Theorem2.quantitative_bound`; `Deduction.quantitative_bound_mathlib` | The latter uses Mathlib's `chromaticNumber`, expanded branch-set exclusion, and the literal `A_epsilon` expression. `quantitative_bound_mathlib_at_minor_number` recovers the paper's `h(G)` form. |
| Packing lemma (`lem:packing`, lines 968-987) | `Bootstrap.exists_packing` | Produces `W,R,Q`, a quotient minor `Q`, `|Q| <= |G|/k`, `chi(G[W]) <= 2 chi(Q)`, and no connected bipartite induced `k`-set in `G[R]`. |
| Path localization (`lem:path`, lines 992-1038) | `Bootstrap.path_localization` | Checked in the numerical form used by separation; packing supplies its stronger exact-`k` exclusion. |
| Order inequality (equation `eq:order`) | `Bootstrap.card_le_twice_independence_mul_cliqueMinorNumber` | Uses the checked Reed--Seymour bound to prove `|H| <= 2 alpha(H) h(H)`. |
| Separation lemma (`lem:separation`, lines 1044-1071) | `Bootstrap.chromatic_separable_of_path_localization` | Checked with an explicit path-localization hypothesis; the separation conclusion uses `ChromaticSeparable`. |
| Bootstrap theorem (`thm:bootstrap`, lines 202-205 and 1420-1463) | `Bootstrap.local_linear_bound_step_of_path` | Checked with `h24` and `hpath`; takes exponent `alpha > 0` to `4 alpha/3` and coefficient `2D + 3(10^6(D+1)+62000)`. |
| Final deduction (`thm:linear`, lines 247-272) | `Deduction.initial_local_bound`, `local_bound_iterate`, `linear_of_theorem4_corollary24` | Theorem 2 gives an initial `6t` local bound at exponent `1/3`; nine steps exceed exponent four; Theorem 4 gives a large-order bound. `extend_linear_bound_from_large_orders` handles `2 <= t` by clique-minor order monotonicity. |

`NoLargeConnectedBipartite G k` excludes an induced connected bipartite
set of exactly `k` vertices. This is the strict `b(G) < k` conclusion of
the packing lemma. The current `PathLocalizationStatement` uses this
stronger hypothesis than paper Lemma 13's `b(G) <= k`. It records only
the two numerical conclusions needed downstream: a closed-neighborhood
core with independence number at most `k(k-1)` and complement chromatic
number below `q`. It omits the induced-path witness and the lower bound
on the core's chromatic number; the latter follows from the checked
palette inequality in the separation proof. The closed-neighborhood,
high-component, and boundary-extension helpers are present in
`Bootstrap/Path.lean`. The universal theorem `path_localization`
now proves `PathLocalizationStatement`; the final two-input theorem
applies it to discharge the intermediate `hpath` hypothesis.

`Graph/MinorFree.lean` checks the equivalence between `HasCliqueMinor`
and the public connected, disjoint, pairwise touching branch-set
condition, as well as monotonicity in the minor order.
`Deduction/PublicLinearBridge.lean` translates the internal linear
bound to `SimpleGraph.Colorable` without a `DecidableEq` parameter in
the public theorem type. `Deduction/Audit.lean` passes `assert_no_sorry` for both the intermediate
three-input assembly and the final two-input internal and public theorems.
Its `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`. No global axiom declares either external result.

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

`Quantitative/Theorem2FinalBridge.lean` and the completed Theorem 2
modules are imported from `HadwigerLean.lean`.
Theorem 1 bootstrap and deduction modules are mapped in the preceding section.

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

Reed--Seymour and Theorem 2 are checked Lean theorems, not axioms.
Theorem 4 and Corollary 24 are the two explicit, unproved external
propositions for the conditional Theorem 1 milestone. The path-localization
lemma is an internal checked theorem, and the final two-input theorem
uses it. No external result is assumed by a global
axiom in the Lean source.


## Historical Theorem 2 implementation checkpoints

The following checkpoints record development stages and are superseded by
the checked completion reported at the end of this section.

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
At that checkpoint the root `lake build` passed (3335 jobs), but Theorem 2
still needed the matching, rounding, robust greedy trace, and final
constant estimate. These obligations were discharged later.

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

### Dependency-ordered Lean module plan

The following proposed paths are relative to `HadwigerLean/`. Reuse the
checked `Graph/Finite.lean`, `Graph/Minor.lean`,
`Graph/MinorFree.lean`, `Graph/TouchingQuotient.lean`,
`Bootstrap/Definitions.lean`, `Bootstrap/Palette.lean`, and
`Deduction/ExternalInputs.lean`. The endpoint declarations must prove
the existing universe-polymorphic `Deduction.Theorem4Statement` and
`Deduction.Corollary24Statement` without changing their statements.

| Order | Proposed modules | Checked output and dependencies |
| --- | --- | --- |
| 1. Finite graph API | `Graph/VertexConnectivity.lean`, `Graph/IndexedLinkage.lean`, `Graph/FiniteFlow.lean` -> `Graph/SetMenger.lean`; `Graph/Contraction.lean`, `Graph/RootedMinor.lean`, `Graph/DensityBasic.lean`, `Graph/MassedPair.lean`, `Probability/FiniteSampling.lean` | Vertex deletion and separations; indexed paths including singleton paths; terminal-permitting Menger and minimum-cut saturation; contraction and minor-model lifting; edge-incidence counts and finite averaging. Rooted models extend the existing `MinorModel`. |
| 2. Common proved inputs | `Graph/ChromaticConnectivity/{Template,Theorem}.lean`, `Graph/DensityConnectivity.lean`, `Graph/RootedCliqueMinor.lean`, `Graph/Linkedness/{Massed,Core,Theorem}.lean`, `Graph/CliqueDensity/{Reduction,SmallOrders,RandomBranches,Theorem}.lean` | Prove additive Girão--Narayanan (GN), the needed Mader form, Kawarabayashi's rooted clique-minor theorem (KR), `16k`-connected implies `k`-linked (L), and the coefficient-30 clique-minor density theorem (KT). The modules within each brace group are ordered as listed. These close Appendices A, B, D, and E. |
| 3. Shared woven induction | `Woven/Basic.lean` -> `Woven/CommonLemmas.lean` -> `Woven/OuterScales.lean` -> `Woven/OuterInduction.lean` | Define `W(a,b;X)` for at most `b` indexed terminal pairs. Prove normalized rooted-minor construction, double and mixed fans, rerouting, three-child assembly, integer scale recurrence, and Section 4's induction under explicit hub, separation, base, and numerical-budget hypotheses. Import GN, L, KR, KT, and Menger; do not import SC or CI. |
| 4. Corollary 24 | `Deduction/Corollary24Proof.lean` | Specialize the shared induction using `OuterSeparation`, `K=10000`, `A=2000`, `B=10^6(d+1)`, the GN hub of cost `980a`, and the normalized KT base. Prove `Corollary24Statement` with its strict bound. |
| 5. Theorem 4 auxiliaries | `Graph/UnbalancedBipartite/{NearComplete,Bound}.lean` -> `Graph/SmallConnected/{Trimming,Theorem}.lean`; in parallel `Graph/RootedDensity/{Massed,ColoredMatching,RigidTruncation,Extremal,Numerical}.lean` -> `Woven/Uniform.lean`; `Woven/Knitting.lean` | KT feeds the Norin--Postle bound (NP); NP, KT, and Mader feed the small connected subgraph theorem (SC). The rooted-density chain proves Appendix F's generic density-forces-target-minor result, including massed pairs and rigid truncation; KT instantiates it to uniform wovenness. Knitting follows from L. |
| 6. Chromatic inseparability | `Inseparability/{SmallPieces,CheapTree,Stages,Theorem}.lean` | Derive CI from SC, uniform wovenness, GN, Menger, knitting, and common rerouting. Prove the empty initial stage and treat the first stage separately: its connector needs a rooted clique model to supply adjacency. |
| 7. Theorem 4 | `Deduction/Theorem4Scale.lean` -> `Deduction/SubgraphRatioBridge.lean` -> `Deduction/Theorem4Proof.lean` | Feed CI into the same outer induction. Compare with `theorem4RatioSet`, including the `q <= t` and `q > t` cases for arbitrary subgraphs. Use `C=3^9 D` for both the coefficient and order cutoff, and prove `Theorem4Statement`. |
| 8. Unconditional assembly | `Deduction/UnconditionalTheorem1.lean`; extend `Deduction/Audit.lean` and root imports | Apply the two endpoint proofs to the checked `linear_of_theorem4_corollary24` and its Mathlib-facing companion. |

The woven predicate must allow roots that are terminals, coincident
roles, and singleton pairs, with exact model--linkage intersection. The
rooted-minor base is tested after deleting occupied original roles,
with the distinct proxies retained as roots. The hub contract applies
after deleting the proxies. Rerouted paths lie in the original paths
**union** woven child graphs. Corollary 24's separation premise concerns induced subgraphs;
Theorem 4's maximum ranges over arbitrary subgraphs. Keep these as
proof obligations rather than weakening either endpoint statement.

Implementation mapping recorded during the staged proof work:

- Stage 1's finite integral-flow construction proves the terminal-permitting
  set Menger statement in `Graph/SetMengerTheorem.lean`; its indexed paths
  include singleton paths. The edge-contraction model uses `none` for the
  contracted pair and singleton blocks for all other vertices.
- Stage 2's clique-density reduction uses the exact edge-loss identity in
  `Graph/ContractionEdges.lean`; adjoining a vertex complete to a neighborhood
  minor is proved in `Graph/UniversalVertexMinor.lean`. The rooted-minor
  dichotomy uses the completed-root graph, and the far-shore restriction and
  edge-contraction separation pullback are checked in
  `Graph/RootedCliqueMinor/{SeparatorRestriction,SeparationPullback}.lean`.
- Stage 3's up-to-budget `Woven` uses `Fin j` with `j <= b` and exact
  model/linkage intersection. `WovenSolution.reindex` proves dummy path
  removal, `Graph/NeighborProxies.lean` assigns distinct proxies to repeated
  roles using Hall's theorem, and `Woven/DistinctRoles.lean` constructs a
  woven solution from a rooted clique model when all role slots are distinct.
  The scales in `Woven/OuterScales.lean` satisfy `3 * child = 2 * parent`.
Deep inputs may temporarily appear as explicit theorem parameters while
the modules are developed; each must eventually be discharged by a
proof. Completion requires both endpoint declarations without `sorry`,
`admit`, or new axioms, focused `lake env lean` checks, a root
`lake build`, and `assert_no_sorry`/`#print axioms` checks of both
endpoints and unconditional Theorem 1.

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
induction with (K=10000), (B=10^6(d+1)), (U=2000T),
(h(a)=980a), and (sigma(a)=14da).
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


## Checked sharp rooted-density and woven input (Stage 5, 2026-09-25)

The Appendix F rooted-density argument is checked in
Graph/RootedDensity/Final.lean. Its unconditional endpoints are
massedUniversal_sharp and rootedDensity_sharp for targets of order
at least three. The order-two case has a separate direct argument in
Graph/RootedDensity/TwoLabels.lean. The reverse direction uses the
checked colored torso lift in TorsoColoredLift.lean to transfer a
rooted torso model to an ambient model. The adhesion bound depends on
the target order, not on the number of roots. Partial ambient labels
record branches that meet the near shore before the lift is complete.

The small connected subgraph theorem is checked in
Graph/SmallConnected/Theorem.lean. The knitting and sparse-target
arguments culminate in Woven/UniformSparseFinal.lean, whose theorem
woven_of_sharp_connectivity gives the sharp uniform woven input under
the checked bound of one million times the clique-matching scale.
These results use finite simple graphs and explicit induced-subgraph
transport throughout. Focused Lake builds and axiom audits show no
placeholders or new axioms.


## Checked chromatic inseparability (Stage 6, 2026-09-25)

Inseparability/CIComplete.lean proves
chromatic_separable_of_local_bound_complete unconditionally. The
local chromatic hypothesis is imposed on induced vertex sets of size
at most ciCoefficient times t times (log t)^4, where
ciCoefficient = 943718400000000. The output is chromatic separability
at ciChromaticBudget t s = ciCoefficient times t times (1+s).

The checked CI construction uses r = ceiling(sqrt(log t)) stages,
x = ceiling(t/sqrt(log t)) roots per stage, piece connectivity
9000000 t, and a piece order bound from the small connected subgraph
theorem. The initial stage has its own rooted-clique connector; the
later stages use sharp uniform wovenness on each packed piece.
StageSharpBudget.lean verifies the required one-million-times
clique-matching scale bound for every stage, and CIComplete.lean
applies woven_of_sharp_connectivity to discharge that last premise.
The checked stage invariant records the disjoint child pieces,
linkage rerouting, model assembly, and color reserve.

