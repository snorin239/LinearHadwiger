# Formalization of *A proof of the Linear Hadwiger's conjecture*

This document describes the Lean 4 + Mathlib formalization of Theorem 1 of
Sergey Norin's [paper](paper/main.pdf). Statement numbers refer to that
bundled PDF. The paper supplies the mathematical intent; the declarations
accepted by Lean are the checked statements.

## Target and checked endpoints

Theorem 1 states that there is an absolute constant $C$ such that every
finite simple graph with no $K_t$ minor has chromatic number at most $Ct$,
for every integer $t\ge 2$.

The internal endpoint in the namespace `HadwigerLean.Deduction`, with
universe parameter `u`, is:

```lean
theorem theorem1_proved :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t → ¬ HadwigerLean.HasCliqueMinor G t →
        HadwigerLean.chromatic G ≤ C * t :=
  linear_of_theorem4_corollary24 theorem4_proved corollary24_proved
```

Its companion `theorem1_mathlib_proved`, displayed in the
[README](README.md#the-statement-formalized), expands the branch-set
condition and concludes `G.Colorable (C * t)`. Neither theorem has an
unproved mathematical input.

| Result | Fully qualified Lean declaration | Source |
|---|---|---|
| Theorem 1, internal form | `HadwigerLean.Deduction.theorem1_proved` | [UnconditionalTheorem1](HadwigerLean/Deduction/UnconditionalTheorem1.lean) |
| Theorem 1, Mathlib-facing form | `HadwigerLean.Deduction.theorem1_mathlib_proved` | [UnconditionalTheorem1](HadwigerLean/Deduction/UnconditionalTheorem1.lean) |
| Theorem 2 | `HadwigerLean.Theorem2.quantitative_bound` | [Theorem2FinalBridge](HadwigerLean/Quantitative/Theorem2FinalBridge.lean) |
| Theorem 4 | `HadwigerLean.Deduction.theorem4_proved` | [Theorem4Proof](HadwigerLean/Deduction/Theorem4Proof.lean) |
| Corollary 24 | `HadwigerLean.Deduction.corollary24_proved` | [Corollary24Complete](HadwigerLean/Deduction/Corollary24Complete.lean) |

The earlier `linear_of_theorem4_corollary24` remains useful as a modular
deduction. Its two explicit hypotheses are discharged by the checked
proofs shown above. The filename `ExternalInputs.lean` records that
earlier interface; its propositions are not global axioms.

## Graphs, minors, and coloring

Graphs are `SimpleGraph V` on an arbitrary finite vertex type
`[Fintype V]`. The public Theorem 1 statements require no decidable
adjacency or equality arguments; classical instances are supplied inside
the proofs.

In [Graph/Finite.lean](HadwigerLean/Graph/Finite.lean),
`chromatic G` is `ENat.toNat G.chromaticNumber`. A finite graph is
colorable with its number of vertices, so Mathlib's extended-natural
chromatic number is finite. The proved equivalence
`chromatic_le_iff_colorable` identifies `chromatic G ≤ n` with
`G.Colorable n`. The empty graph has chromatic number zero.

In [Graph/Minor.lean](HadwigerLean/Graph/Minor.lean), `MinorModel H G`
consists of one connected branch set for each vertex of `H`, pairwise
disjointness, and an edge of `G` between the corresponding branch sets
for every edge of `H`. Connectedness includes nonemptiness. Additional
edges are allowed, as in the ordinary graph-minor relation.
`HasCliqueMinor G t` is the existence of such a model for the complete
graph on `Fin t`. The development proves composition, transport, and
monotonicity of minor models.

The largest complete-minor order is `cliqueMinorNumber G`, with value
zero for the empty graph. In
[Graph/MinorFree.lean](HadwigerLean/Graph/MinorFree.lean),
`not_hasCliqueMinor_iff_cliqueMinorNumber_lt` proves
`¬ HasCliqueMinor G t ↔ cliqueMinorNumber G < t`, and
`hasCliqueMinor_iff_branchSets` proves the equivalence with the expanded
condition in the public theorem. The final
[coloring bridge](HadwigerLean/Deduction/PublicLinearBridge.lean) uses
these equivalences to obtain the Mathlib-facing statement.

## Proof architecture

### 1. Fractional coloring and Reed--Seymour

The `Coloring` modules represent fractional colorings by nonnegative
weights on stable sets, together with the dual vertex weights. The
`Optimization` module proves attainment and the primal-dual equality
needed by ordinary and pair-constrained fractional coloring, using the
vendored finite strong-duality theorem.

[ReedSeymour/Theorem.lean](HadwigerLean/ReedSeymour/Theorem.lean) proves
$\chi_f(G)\le 2h(G)$. Here $\chi_f(G)$ is the fractional chromatic number,
and $h(G)$ is the largest complete-minor order. The construction follows
the maximal-support egg decomposition: connected pieces contain
independent sets carrying at least half their weight, and their touching
quotient has a simplicial elimination ordering. Coloring that quotient
and applying LP duality gives the fractional bound. The empty graph is
included.

### 2. The quantitative coloring bound

Theorem 2 states, for every finite graph and $0<\varepsilon\le 1$,

$$
\chi(G)\le 4h(G)+\varepsilon |V(G)|+A_\varepsilon,
\qquad A_\varepsilon=(100/\varepsilon)^{2000/\varepsilon^2}.
$$

The proof has four stages. First, finite random marking and a controlled
iteration produce an almost-perfect matching in a nearly regular
multihypergraph with small codegrees. Second, a hypergraph with token and
dummy vertices turns this matching into an ordinary coloring when the
fractional coloring has small pair loads. Third, a linear program with
pair constraints selects a bounded-degree graph of added nonedges.
Finally, a weighted matching contraction and the Reed--Seymour bound
control the augmented graph's fractional chromatic number. Removing
large stable sets extends the bounded-independence argument to every
finite graph.

The explicit constant is retained, with its real exponent implemented
by `Real.rpow`. The unconditional theorem is
`HadwigerLean.Theorem2.quantitative_bound`;
[PublicStatements.lean](HadwigerLean/Deduction/PublicStatements.lean)
also exposes Mathlib-facing versions, including
`quantitative_bound_mathlib_at_minor_number` for the exact $h(G)$ form.

### 3. Connectivity, linkages, and the outer recursion

The `Graph` modules prove finite set Menger, additive chromatic
connectivity, a quantitative linkedness theorem, rooted clique minors,
and the coefficient-30 complete-minor density bound. These supply the
paths and connected pieces needed by the recursion.

A graph is represented as `Woven G a b` when every choice of $a$
distinct roots and at most $b$ disjoint terminal pairs admits both a
rooted $K_a$ model and a linkage, meeting exactly at roots that are
terminals. The `Woven` modules normalize coincident roles, construct
fans to a hub of bounded chromatic number, reroute paths through three
smaller woven pieces, and assemble their models.

The integer scales are $2^i3^{m-i}$ for $0\le i\le m$, so a child
scale satisfies $3a'=2a$. At low scales, density supplies the base
models; at higher scales, chromatic separation supplies the three
children. Specializing this induction proves Corollary 24 with the
paper's strict bound

$$
\chi(G)<3\bigl(10^6(d+1)+62000\bigr)t.
$$

Here $t\ge100$, $d\ge1$, $G$ has no $K_t$ minor, and $T$ is the least
power of three at least $t$. The separation hypothesis ranges over every
integer scale $a=(2/3)^iT>T/\sqrt{\log T}$: every induced
$K_{14a}$-minor-free subgraph $Y$ with $\chi(Y)>28da$ must contain two
vertex-disjoint induced subgraphs, each requiring at least
$\chi(Y)-14da$ colors. These hypotheses are recorded by
`Bootstrap.OuterSeparation` and retained by `Corollary24Statement`.

### 4. The small-graph reduction

The proof of Theorem 4 adds three ingredients to the common outer
recursion: small highly connected subgraphs, a rooted density theorem
giving uniform wovenness, and the chromatic-inseparability construction.
The latter assembles a clique minor in stages unless the graph splits
into two disjoint induced subgraphs retaining enough chromatic number.
This supplies the separation input to the same outer induction.

The endpoint retains the exact maximum-ratio form of Theorem 4: for an
absolute integer $C_{\rm DP}\ge1$, every $K_t$-minor-free graph with
$t\ge3$ satisfies

$$
\chi(G)\le C_{\rm DP}t(1+f(G,t)),
$$

where $f(G,t)$ is the maximum of zero and $\chi(H)/a$ over arbitrary
subgraphs $H\subseteq G$ and integers
$t/\sqrt{\log t}\le a\le t$ such that $H$ has no $K_a$ minor and
$|V(H)|\le C_{\rm DP}a(\log a)^4$. The same constant occurs in the
coefficient and the order cutoff. Lean represents the maximum by
`theorem4MaxRatio`; finiteness and attainment are proved in
[ExternalInputs.lean](HadwigerLean/Deduction/ExternalInputs.lean).

### 5. Packing, localization, and exponent improvement

`Bootstrap.LocalLinearBound α` means that some constants $D,t_0$ give
$\chi(G)\le Dt$ for every $t\ge t_0$ and every $K_t$-minor-free graph
of order at most $t(\log t)^\alpha$.

The packing lemma contracts disjoint connected induced bipartite pieces.
Their quotient is smaller, and a quotient coloring lifts using twice as
many colors. The remainder contains no large connected induced bipartite
subgraph. Path localization and $|V(J)|\le2\alpha(J)h(J)$ then show
that a local coloring bound forces the remainder to be chromatically
separable; here $\alpha(J)$ is the independence number. Corollary 24
converts this separation into the required coloring bound.

The checked bootstrap
`Bootstrap.local_linear_bound_step_of_path` takes a local bound at
$\alpha>0$ to one at $4\alpha/3$. It is written with explicit
Corollary 24 and path-localization arguments. The final deduction supplies
`corollary24_proved` and `Bootstrap.path_localization`, respectively.

### 6. Theorem 1

[InitialLocal.lean](HadwigerLean/Deduction/InitialLocal.lean) applies
Theorem 2 with $\varepsilon=(\log t)^{-1/3}$. For sufficiently large
$t$, the additive term is at most $t$; the order hypothesis bounds
$\varepsilon |V(G)|$ by $t$. This gives the initial local bound $6t$.

[Iteration.lean](HadwigerLean/Deduction/Iteration.lean) performs nine
bootstrap steps and checks $(4/3)^9/3>4$. The resulting order range
eventually contains every subgraph in Theorem 4's window, giving a
linear bound for all sufficiently large $t$.
[FiniteOrders.lean](HadwigerLean/Deduction/FiniteOrders.lean) enlarges
the coefficient to cover the remaining orders. The final proof applies
the proved Theorem 4 and Corollary 24 to this deduction.

## Paper-to-Lean map

The entries below identify the principal implementations. They include
sufficient variants where the development does not expose a literal
translation of an intermediate statement. Declaration names are relative
to `HadwigerLean` unless another namespace is shown.

| Result in `main.pdf` | Lean declaration or module | Role or difference |
|---|---|---|
| Theorem 1 | `Deduction.theorem1_proved`, `Deduction.theorem1_mathlib_proved` | Unconditional final bounds. |
| Theorem 2 | `Theorem2.quantitative_bound` | Preserves the explicit additive constant and the full range $0<\varepsilon\le1$. |
| Theorem 3 | [Bootstrap/Step](HadwigerLean/Bootstrap/Step.lean), `Bootstrap.local_linear_bound_step_of_path` | Exponent improvement; its explicit inputs are discharged in the final deduction. |
| Theorem 4 | `Deduction.theorem4_proved` | Small-graph reduction over arbitrary subgraphs, with one constant in both places. |
| Theorem 5 | [Graph/CliqueDensity/Theorem](HadwigerLean/Graph/CliqueDensity/Theorem.lean), `hasCliqueMinor_of_edgeDensity_ge` | Density $30r\sqrt{\log r}$ forces a $K_r$ minor for $r\ge2$. |
| Reed--Seymour, equation (4) | [ReedSeymour/Theorem](HadwigerLean/ReedSeymour/Theorem.lean), `ReedSeymour.reed_seymour_bound` | Fractional chromatic bound, proved internally. |
| Lemma 6 | [Quantitative/MatchingApplication](HadwigerLean/Quantitative/MatchingApplication.lean), `Theorem2.exists_almostPerfectMatching_of_degree_bounds` | Indexed hypergraph matching with explicit degree and codegree caps. |
| Lemma 7 | [Quantitative/RoundingBridge](HadwigerLean/Quantitative/RoundingBridge.lean), `Theorem2.low_codegree_rounding` | Rounding at the parameter values needed for Theorem 2. |
| Lemma 8 | [Coloring/Augmentation](HadwigerLean/Coloring/Augmentation.lean), `exists_boundedDegree_augmentation_of_cap` | Augmentation from rounding, with any adequate integer degree cap. |
| Proposition 9 | [Coloring/RobustFractional](HadwigerLean/Coloring/RobustFractional.lean), `robust_fractional_bound` | Fractional bound after bounded-degree perturbation. |
| Lemmas 10--11 | [Graph/WeightedMatching](HadwigerLean/Graph/WeightedMatching.lean) | Independent transversals and a finite greedy matching with weight-loss and short-cycle guarantees. |
| Lemma 12 | [Bootstrap/Packing](HadwigerLean/Bootstrap/Packing.lean), `Bootstrap.exists_packing` | Bipartite packing, quotient minor, and remainder. |
| Lemma 13 | [Bootstrap/Path](HadwigerLean/Bootstrap/Path.lean), `Bootstrap.path_localization` | Numerical localization conclusions under the strict exclusion supplied by packing. |
| Lemma 14 | [Bootstrap/SeparationFromPath](HadwigerLean/Bootstrap/SeparationFromPath.lean), `Bootstrap.chromatic_separable_of_path_localization` | Converts localization and a local coloring bound into separation. |
| Theorem 15 | [Graph/ChromaticConnectivity/Theorem](HadwigerLean/Graph/ChromaticConnectivity/Theorem.lean), `exists_chromatic_connected_induced` | Additive connectivity theorem, with an induced output. |
| Theorem 16 | [Graph/Linkedness/Final](HadwigerLean/Graph/Linkedness/Final.lean), `Linkedness.kLinked_of_sixteen_mul_vertexConnected` | Sufficient replacement: $16k$-connectivity implies $k$-linkedness; the printed theorem uses $10k$. |
| Lemma 17 | [Graph/RootedCliqueMinor/Dichotomy](HadwigerLean/Graph/RootedCliqueMinor/Dichotomy.lean), `rootedCliqueMinor_of_connected_cliqueMinor` | Rooted clique minor at prescribed distinct vertices. |
| Lemmas 18--20 | [Corollary24Hub](HadwigerLean/Deduction/Corollary24Hub.lean), [RedundantMenger](HadwigerLean/Woven/RedundantMenger.lean), and the `Woven/MixedFan` modules | Bounded-chromatic hub and disjoint fan constructions. |
| Lemmas 21--22 | [Woven/Rerouting](HadwigerLean/Woven/Rerouting.lean), [Woven/ManyChildRerouting](HadwigerLean/Woven/ManyChildRerouting.lean) | Rerouting with explicit containment and model-intersection guarantees. |
| Lemma 23 | [Woven/OuterInductionMixed](HadwigerLean/Woven/OuterInductionMixed.lean), `Deduction.cor24_outerAt_top` | Shared recursion with a density base at every scale below the cutoff; specialized to the top scale for Corollary 24. |
| Corollary 24 | `Deduction.corollary24_proved` | Preserves the strict inequality and the complete separation premise. |

Theorem 4's additional chain ends in
[`small_connected_subgraph_of_density`](HadwigerLean/Graph/SmallConnected/Theorem.lean),
[`RootedDensity.rootedDensity_sharp`](HadwigerLean/Graph/RootedDensity/Final.lean),
[`Woven.woven_of_sharp_connectivity`](HadwigerLean/Woven/UniformSparseFinal.lean),
and
[`Inseparability.chromatic_separable_of_local_bound_complete`](HadwigerLean/Inseparability/CIComplete.lean).
These provide checked proofs for ingredients cited from the literature
in the main paper's small-graph reduction.

## Main proof-route differences

- **Finite probability and multiplicities.** Hyperedges have a separate
  index type, so repeated copies remain distinct. Independent Bernoulli
  marks represent the zero/nonzero Poisson events used by the paper.
  Probability identities, concentration estimates, and the matching
  iteration are proved in Lean.
- **Linear programming.** The finite strong-duality proof is vendored
  from EconCSLib and compiled with the project. Fractional colorings and
  their pair-constrained variants have explicit maps to these finite
  programs. No external LP solver supplies proof evidence.
- **Localization.** The checked interface excludes a connected bipartite
  induced set of exactly $k$ vertices, as guaranteed by packing. It keeps
  the independence-number and complement-coloring conclusions needed by
  separation. It does not assert the full printed path-witness statement
  under the weaker hypothesis of Lemma 13.
- **Wovenness and routing.** The formal predicate allows *at most* $b$
  terminal pairs, including singleton pairs and roots that are terminals.
  This avoids implicit padding. Normalization assigns distinct neighbor
  proxies to coincident roles and applies rooted-minor results after the
  required deletions. Rerouted paths stay in the union of the original
  paths and the woven pieces.
- **Linkedness.** The proved $16k$ theorem suffices for the recursion's
  connectivity budgets. The sharper $10k$ assertion of Theorem 16 is not
  a formalized target.
- **The initial coefficient.** Lean uses $\varepsilon=(\log t)^{-1/3}$
  and obtains $6t$. The paper uses half this value of $\varepsilon$ and
  obtains a bound below $5t$. Both establish the same required local
  linear-bound property at exponent $1/3$.
- **Small excluded-clique orders.** If the large-order bound starts at
  $T$, a graph with no $K_t$ minor for $t<T$ also has no $K_T$ minor.
  The bound at $T$, followed by an increase of the universal coefficient,
  handles these cases. This replaces the paper's final appeal to the
  density-based coloring estimate; the density theorem is still used
  elsewhere in the development.

These changes preserve the hypotheses and conclusion of Theorem 1.
They do not claim a literal formalization of every intermediate statement
or of every result mentioned in the introduction. The development proves
existence of the universal constant without optimizing it or extracting
an executable coloring procedure.

## Verification and provenance

Lean and Mathlib are pinned to `v4.32.1`. The root module
[HadwigerLean.lean](HadwigerLean.lean) imports the complete proof of the
public target and its audits. On September 25, 2026, the local
`lake build` completed successfully with 3,948 jobs, and the final audit
was rerun using:

```sh
lake env lean HadwigerLean/Deduction/Audit.lean
```

The project Lean sources contain no `sorry` proofs, `admit` tactics, or
user-declared axioms. The audit applies `assert_no_sorry` to the final
endpoints and their principal bridges. For `theorem1_proved`,
`theorem1_mathlib_proved`, `theorem4_proved`, and `corollary24_proved`,
`#print axioms` lists exactly:

```text
propext, Classical.choice, Quot.sound
```

Thus no unproved graph-theoretic assumption remains in either public
form of Theorem 1. The build can emit linter warnings; these do not
represent unfinished proofs.

The three vendored linear-programming files retain their Apache-2.0
license and upstream attribution; see their
[README](HadwigerLean/Vendor/EconCSLib/README.md) for the exact source
commit and import changes. The main paper records the provenance of the
mathematical ideas and its AI disclosure. The
[blueprint](docs/blueprint.md) and
[auxiliary proof manuscript](docs/theorem4-corollary24-proof.md) retain
the development history and additional mathematical explanations;
historical conditional checkpoints in those documents are superseded by
the checked endpoints listed here.
