# Theorem 2 implementation plan and resume log

Source: paper/main.tex, Theorem 2 (thm:quantitative, lines 184-190) and proof
(lines 278-946). The checked target is the same explicit real bound

  (chromatic G : Real) <= 4 * (cliqueMinorNumber G : Real)
    + epsilon * (graphOrder G : Real) + (100 / epsilon) ^ (2000 / epsilon ^ 2)

for every finite simple graph and real 0 < epsilon <= 1. The exact Lean
declaration may change as interfaces are developed; record any such change
here and in docs/blueprint.md. Preserve the explicit real exponent.

## Baseline and dependencies

- Baseline on 2026-09-24: git status --short clean and lake build succeeds.
- Coloring/PairLoad.lean supplies attained pair-constrained primal and dual
  optima. Coloring/FractionalLP.lean supplies attained fractional dual weights.
  ReedSeymour/Theorem.lean proves the unconditional fractional bound.
- No Theorem 2 modules exist at baseline. Do not mark Theorem 2 checked until
  its exact statement compiles from the root library without sorry, admit,
  or new axioms.
- Critical chain: indexed hypergraphs and finite probability -> almost-perfect
  matching (paper 316-498) -> low-codegree rounding (506-600) ->
  augmentation (608-703) -> final assembly (860-946).
- Independent chain: independent transversal and weighted matching (722-814)
  -> matching contraction and robust fractional bound (712-720, 816-856).
  Constants and stable-set removal (860-946) can be developed separately.

## First wave: four nonoverlapping lanes

1. Hypergraph lane, agent A: own Hypergraph/Indexed.lean, then deterministic
   definitions and trimming/iteration framework in
   Hypergraph/AlmostPerfectMatching.lean. Represent a multihypergraph by a
   finite edge-copy index type and an edge map to finite vertex sets; preserve
   repeated edges. Coordinate the arbitrary finite edge-index interface with
   the probability lane before either lane commits to an API.
2. Probability lane, agent B: own Probability/FiniteBernoulli.lean. Prove
   finite independent marking, joint survival and moment formulas, and a
   mean-sensitive exponential Bernoulli concentration bound. Mathlib's generic
   MGF/Chernoff lemmas are available; Hoeffding in terms of the number of edge
   copies is too weak for the paper's rounding union bound.
3. Graph lane, agent C: own Graph/WeightedMatching.lean, then
   Coloring/RobustFractional.lean. Prove the independent transversal,
   bounded weight-loss matching, a concrete contraction minor, dual-weight
   transfer, and the robust bound. Use SimpleGraph.edist for the greedy
   exclusion rule: unreachable vertices have distance top under edist but
   distance zero under dist. A simple quotient of auxiliary components can
   hide two parallel matching edges; account for that in the transversal.
4. Coordinator: own Coloring/ExactLoad.lean and Coloring/Augmentation.lean,
   then Quantitative/Constants.lean and Quantitative/Theorem2.lean. First prove
   that a pair-constrained optimum can have all vertex loads exactly one.
   Prove as much of augmentation as possible from an explicit rounding
   hypothesis, so it is a checked conditional theorem, not a placeholder axiom.

The first small checked milestone is exact-load normalization. Other lanes
should continue while that theorem is proved.

## Second wave and integration

- Combine indexed-hypergraph and probability results into the almost-perfect
  matching lemma. A possible simplification is one-round expectation
  inequalities for each deterministic residual hypergraph, followed by a
  backward potential and a favorable finite outcome each round. Verify the
  numerical constants before using this route.
- Build token/dummy rounding from matching. Its concentration bound must be
  strong enough for the union bound over all degrees and codegrees.
- Instantiate conditional augmentation with rounding. Finish the robust
  fractional bound, constants, bounded-independence case, and stable-set
  removal. Preserve the paper's exact A_epsilon.
- Give each file a single owner. Use focused lake env lean checks while
  developing; run lake build from the repository root after Lean changes and
  at integration checkpoints. Import Quantitative/Theorem2.lean into
  HadwigerLean.lean only after it checks.

## Resume procedure and progress log

On resumption, read this file and docs/blueprint.md, inspect git status
--short, list new modules, and run lake build. Compare each module with its
paper lemma and record checked declarations and remaining gaps below. Do not
infer completion from a file's existence or from an agent report alone.

- 2026-09-24: plan recorded; implementation starting. Baseline build passes.

- 2026-09-24 checkpoint 1: `Coloring/ExactLoad.lean` checks
  `exists_pairConstrained_exact_minimizer`, proving an optimum with exact
  vertex loads. `Coloring/Augmentation.lean` checks the pair-dual penalty
  bound, incident-penalty double counting, heavy-vertex count, and the
  penalty graph's nonedge property. These are imported by `HadwigerLean.lean`;
  full `lake build` passed (1765 jobs). Augmentation still lacks the degree
  bound and dual-weight transfer.
- Parallel reports, subsequently checked by focused builds: hypergraph
  indexed/trimming and deterministic round partitions; finite Bernoulli
  survival/MGF/mean-sensitive Chernoff; matching contraction and a robust
  fractional bound conditional on a matching certificate. The full matching
  lemma, low-codegree rounding, independent transversal, weighted matching
  construction, robust proposition, constants, and Theorem 2 remain open.
- 2026-09-24 checkpoint 2: All six parallel support modules were imported by
  HadwigerLean.lean and a full lake build passed (1850 jobs). A search found
  no sorry, admit, or axiom in the new proof modules. Hypergraph/Indexed
  checks indexed uniform hypergraphs, degree trimming, and codegree bounds.
  Hypergraph/AlmostPerfectMatching checks sampled rounds, matching and waste
  partitions, and survivor probability/expectation infrastructure; the
  quantitative one-round waste bound and final almost-perfect matching are
  pending. Probability/FiniteBernoulli checks the finite Bernoulli product
  space, exact survival, MGF, mean-sensitive concentration, and a union
  bound. Coloring/LowCodegreeRounding checks sampled degree/codegree
  formulas, concentration infrastructure, and the token/dummy uniformity;
  coloring extraction and the rounding theorem are pending.
- The graph lane now checks an independent transversal under the exact
  no-matching-edge-cycle condition, cycle-length/cardinality bridges,
  matching contraction, dual-weight transfer, and a robust fractional bound
  conditional on a weighted matching certificate. The greedy certificate
  construction remains pending. Coloring/Augmentation now checks the
  penalty graph degree bound and max-degree ceiling in addition to
  checkpoint 1; dual-weight transfer and combination with rounding remain
  pending. Local linter warnings remain in several new modules, but there
  are no Lean errors.

- 2026-09-24 checkpoint 3: Coloring/Augmentation.lean focused-Lean checks
  the full conditional augmentation theorem
  exists_boundedDegree_augmentation_from_rounding. Its sole remaining
  hypothesis is the paper's low-pair-load rounding inequality for every
  exact-load pair-constrained coloring. The checked proof constructs the
  heavy-vertex set and nonedge penalty graph, bounds its maximum degree,
  transfers the pair-LP dual to a fractional-coloring dual, and derives
  chromatic(G) - 3 gamma n <= chi_f(G+F). The pair-count estimate uses an
  injection into the two-element subsets of a stable set. This is a
  conditional theorem with an explicit assumption, not an axiom or a
  completed proof of Theorem 2.
- Subsequent parallel progress: Probability/FiniteBernoulli has checked
  two-mark collision probabilities; Hypergraph/AlmostPerfectMatching has
  checked exact expected survivor cardinality, private-mark waste, and
  collision charging infrastructure. Coloring/LowCodegreeRounding has
  checked proper coloring extraction from a token/dummy matching hypothesis.
  Graph/WeightedMatching has checked extended-distance ball cardinality,
  matching-edge degree one, and degree bound after graph union.

- 2026-09-24 checkpoint 4: The user authorized restructuring intermediate
  lemmas and dropping unnecessary floors/ceilings. Augmentation now checks
  exists_boundedDegree_augmentation_of_cap, which takes any integer d above
  the real degree bound. Quantitative/Constants.lean focused-Lean checks
  the paper's parameter definitions, positivity and simple ceiling bounds,
  the exact algebraic degree-ratio identity, and a conditional augmentation
  corollary with the paper's d. Quantitative/Peeling.lean focused-Lean
  checks one-step stable-set deletion and the more flexible coloring lemma
  for a stable-set cover plus a colored residual graph. The maximal packing
  and count bound for the full peeling step remain pending.
- Hypergraph/AlmostPerfectMatching now checks the one-round expected waste
  bound in the paper's simplified form and joint-survival/expected-edge
  infrastructure. Coloring/LowCodegreeRounding now checks a conditional
  chromatic inequality with the exact augmentation interface plus token
  weight normalization and expected original degree. WeightedMatching now
  checks crossing-set counts and the layer-cake weight-loss implication.
  The final matching existence, rounding sampling bridge, and greedy
  weighted matching trace remain open.

- 2026-09-24 checkpoint 5: The second full lake build passed (3335 jobs)
  after importing Quantitative/Constants.lean and
  Quantitative/Peeling.lean into HadwigerLean.lean. The root build includes
  all currently checked parallel modules. Constants and Peeling each passed
  focused Lean checks without warnings before integration. The conditional
  augmentation theorem and its flexible degree-cap form check without
  warnings. Agent modules still emit linter warnings but no Lean errors.
  Theorem 2 itself has not been stated or proved in Lean.

- 2026-09-24 checkpoint 6: Quantitative/Peeling.lean now focused-Lean
  checks exists_stable_peeling and chromatic_bound_of_bounded_induced.
  A maximum-cardinality disjoint family of stable sets of size m+1
  leaves a residual induced graph with independence number at most m;
  its block count times (m+1) is at most the original graph order.
  A stable-cover coloring lemma gives the chromatic comparison, and
  induced-minor monotonicity completes the generic εn/2 peeling loss.
  Quantitative/Constants.lean focused-Lean checks
  quantitative_bound_of_bounded_induced, deriving the exact final
  Theorem 2 inequality from the bounded-independence estimate on
  induced subgraphs. It also checks mu>0 and mu≤1. This final
  implication is conditional; the bounded-independence estimate
  remains unproved. No proof placeholders or new axioms are present
  in new modules (the text search only matched the word "axioms" in
  a comment). A full build after these latest additions is pending.

- 2026-09-24 checkpoint 7: A full `lake build` passed (3335 jobs) after
  the probability lane added a finite Bernoulli Cauchy–Schwarz estimate,
  the hypergraph lane added centered second-moment infrastructure, the graph
  lane added finite greedy-state preservation, and the rounding lane added
  token/dummy codegree cases. Quantitative/Constants.lean now checks
  `bounded_independence_from_rounding_and_robust` and
  `quantitative_bound_of_bounded_induced_A`, which assemble the small-order
  case, conditional augmentation, robust fractional bound, and peeling.
  It also checks `d_add_one_le_coarse`, `mu_inv_le_power`, and
  `d_add_one_le_power`, reaching `(d+1 : Real) <= (100/epsilon)^(304/epsilon)`.
  Remaining gates: full almost-perfect matching iteration; sampling and
  matching bridge for low-codegree rounding; actual finite greedy matching
  trace for the robust proposition; and `A <= Aepsilon`. None is a checked
  Theorem 2 proof yet.

- 2026-09-24 checkpoint 8: The third full `lake build` passed (3339 jobs)
  after importing Quantitative/Recurrence, BackwardPotential, UnionBound,
  and Theorem2 into the root library. `Constants.lean` checks the complete
  explicit numerical comparison `A_le_Aepsilon`; the two intermediate
  bounds are `n0 <= R^(1208/epsilon^2)` and
  `robustAdditive <= R^(1826/epsilon^2)`, with `R=100/epsilon`. Theorem2.lean
  checks `quantitative_bound_of_rounding_and_robust`: given the exact
  low-codegree rounding and robust-fractional inequalities for finite
  bounded-independence graphs, it proves the paper's exact Theorem 2
  inequality for every graph. Its assumptions are explicit, not axioms.
  The generic recurrence and backward-potential modules check the round
  summation and favorable-selection coefficients; UnionBound proves
  `8*r^2*n^2*exp(-mu^2*n/256)<1` under the paper-scale order hypothesis.
  In parallel, hypergraph now checks one-round normalized deficit and
  weighted favorable-outcome selection, rounding checks simultaneous
  sampled degree/codegree bounds and all six token/dummy pair cases, and
  the graph lane checks an actual finite greedy matching with the sorted
  orientation and exact unmatched set. Final combinatorial iteration,
  sampling-to-matching rounding bridge, and greedy trace/short-cycle
  certificate remain open. No new proof placeholders or axioms are present.

- 2026-09-24 checkpoint 9: The robust fractional lane is now unconditional.
  `Graph/WeightedMatching.lean` checks the finite greedy matching, its
  quantitative weight and cardinality bounds, and short-cycle exclusion.
  `Coloring/RobustFractional.lean` and `Quantitative/RobustBridge.lean`
  check the robust fractional proposition with exactly the additive term
  used by Theorem 2. `Quantitative/Theorem2.lean` now checks
  `quantitative_bound_of_rounding`, whose only remaining assumption is
  the universal low-codegree rounding inequality.

  The finite hypergraph iteration, its initial potential budget, and
  its floor-schedule wrapper check in `Hypergraph/AlmostPerfectMatching.lean`.
  `Quantitative/MatchingConstants.lean` checks the paper parameters
  without carrying floors through most estimates: q^T <= xi/4,
  cumulative floor loss, a positive degree/codegree invariant,
  the small one-round error, and the total potential budget.
  `Quantitative/MatchingApplication.lean` checks
  `exists_almostPerfectMatching_of_degree_bounds`: a uniform indexed
  hypergraph with the concrete initial degree/codegree caps has a
  matching covering at least (1-xi) of its vertices. Its latest focused
  build passed (3109 jobs).

  The probability lane checks a simultaneous Bernoulli sample with the
  required degree and codegree concentration and is connecting those
  bounds to the concrete matching theorem. An attempted full root build
  compiled MatchingApplication and Theorem2 but stopped at a transient
  `dsimp` error in the concurrently edited LowCodegreeRounding module.
  That source error was fixed and the module passed a focused Lean check;
  rerun `lake build` after the rounding bridge is stable. No new
  `sorry`, `admit`, or axioms are being used as a completed proof.
- 2026-09-24 checkpoint 10 (complete): The universal low-codegree rounding
  lemma `Theorem2.low_codegree_rounding` is checked in
  `Quantitative/RoundingBridge.lean`. It chooses the actual ceiling
  counts for color tokens and dummy vertices, obtains one simultaneous
  Bernoulli sample, applies the concrete almost-perfect matching theorem
  with actual sampled maximum degree and codegree, and extracts the
  ordinary coloring. `Quantitative/MatchingParameterBridge.lean`
  checks the exact identity
  `mu epsilon = matchingMu (r epsilon) (matchingXi epsilon)`, the
  `n0` sampling scale, and the remaining color budget.

  `Quantitative/Theorem2FinalBridge.lean` checks
  `Theorem2.quantitative_bound` unconditionally for every finite
  simple graph and real `0 < epsilon <= 1`:
  `chromatic G <= 4 * cliqueMinorNumber G + epsilon * |V| +
  (100/epsilon)^(2000/epsilon^2)`. The additive term is `Aepsilon`,
  whose definition is this exact real expression. The root
  `HadwigerLean.lean` imports the final theorem. The required full
  `lake build` passed (3436 jobs). A scan of the new Theorem 2 modules
  found no `sorry`, `admit`, `axiom`, or `constant` declarations
  (two `admit` text hits in robust-module comments are ordinary prose).
  An independent semantic audit confirmed the sampled hypergraph retains
  its full vertex set, counts edge copies, uses distinct-pair codegrees,
  and lifts matching coverage correctly. Existing nonfatal linter
  warnings remain.

## Resume after this checkpoint

Theorem 2 is complete. If a future tool or build failure occurs, first
run `lake build` from the repository root. The final declaration is
`HadwigerLean.Theorem2.quantitative_bound` in
`HadwigerLean/Quantitative/Theorem2FinalBridge.lean`; its imports
trace the rounding and robust branches. Continue toward Theorem 1 from
`docs/blueprint.md`, keeping any new theorem changes separate from
this checked Theorem 2 milestone.