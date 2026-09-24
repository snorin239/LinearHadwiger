# Theorem 4 and Corollary 24: proof and formalization plan

Status (2026-09-24): this is a dependency and implementation plan, **not** a
self-contained proof or a checked Lean proof. The completed mathematical
proof manuscript is [the companion document](theorem4-corollary24-proof.md);
its results still await Lean formalization. The endpoint propositions are
already defined in `HadwigerLean/Deduction/ExternalInputs.lean` as
`Theorem4Statement` and `Corollary24Statement`; neither has been proved.

## Endpoints and sources

* Main paper Theorem 4 (`paper/main.tex`, `thm:dp`, lines 212–227) is
  [Delcourt–Postle Theorem 1.6](https://arxiv.org/pdf/2108.01633v5).
  Its one constant occurs in both the global coloring coefficient and the
  small-subgraph order cutoff. The maximization is over arbitrary subgraphs,
  not just induced subgraphs. The existing Lean proposition preserves this.
* Main paper Corollary 24 (`cor:outer`, lines 1382–1398) is the explicit
  bound at the least power-of-three scale, conditional on `OuterSeparation`.
  It follows from main paper Lemma 23 (`lem:outer`, lines 1232–1380).
  The existing Lean proposition preserves the strict bound and all scale
  quantifiers.

The main paper's Lemma 23 adapts Delcourt–Postle Theorem 7.1, not merely
its conclusion. Theorem 7.1 is a descending induction on integer scales
`a = (2/3)^i T` proving `(a,3a)`-wovenness. Its top-scale instance yields
Theorem 1.6 after a final scale and ratio comparison.

## Shared recursion

Formalize the following construction once, with explicit hypotheses for its
three variable inputs: a hub with a bounded chromatic cost, a separation
rule with a bounded loss, and a base-scale woven or minor witness.

1. Make the `a` roots and `3a` terminal pairs disjoint by choosing proxies.
   If a `K_(14a)` minor is present, use the rooted-minor theorem and finish.
2. In the minor-free case, find a highly connected hub; attach two paths
   from each proxy; delete their vertices at a controlled chromatic cost;
   and extract a highly connected remainder.
3. Reduce the outer woven problem to finding a rooted `K_a` model in the
   remainder. This uses Menger fans, the redundant-path lemma, and a
   prescribed-pair linkage through the hub.
4. Delete the proposed roots and their neighbors. Split the residual
   chromatic number twice to get three disjoint children, restore their
   connectivity, and recurse at `a' = 2a/3`.
5. Reroute one linkage through three child rooted models and join pairs of
   branches. The fact that any two two-element subsets of three children
   intersect makes the resulting `a` branch sets pairwise adjacent.

The common theorem should expose numerical *budget conditions* rather than
hard-code either paper's constants. Specialize it as follows.

| Input | Main paper Lemma 23 | Delcourt–Postle Theorem 7.1 |
| --- | --- | --- |
| Hub | Girão–Narayanan extraction gives a `140a`-connected hub with chromatic number at most `980a`. | The same Girão–Narayanan hub works; Theorem 2.3 remains needed upstream for chromatic inseparability. |
| Separation | Assumed at every eligible scale, costing `14da` at each split. | Derived by contraposition from Lemma 2.5, the chromatic-inseparable minor theorem. |
| Base | The explicit Kostochka–Thomason density bound forces a `K_(14a)` minor. | The same Kostochka–Thomason base repairs the printed Theorem 7.1 base case. |
| Constants | Preserve `K=10000`, `A=2000`, `B=10^6(d+1)` and the strict Corollary 24 bound. | Existential absolute constants may be enlarged, but the same constant must also control the small-subgraph cutoff in Theorem 1.6. |

## Dependency closure

These are the substantial leaves in the displayed proofs. A fully
self-contained writeup must prove them (possibly by new arguments); a
document that cites them is source-audited but not fully self-contained.

| Ingredient | Used for | Endpoint |
| --- | --- | --- |
| Menger's theorem, prescribed fans, redundant-path lemma (DP 5.2–5.3) | Link proxies and the residual graph to the hub | Both |
| Girão–Narayanan chromatic connectivity theorem (DP 5.1) | Hub/child extraction and final outer bound | Both |
| Thomas–Wollan `10ℓ`-connectivity implies `ℓ`-linked (DP 5.6) | Hub and child linkages | Both |
| Kawarabayashi rooted clique-minor theorem (DP 5.14) | `K_(14a)` branch | Both |
| Kostochka clique-minor density bound (DP 4.3) | Base case; also DP 2.3 and 5.13 | Both |
| Norin–Postle unbalanced bipartite edge bound (DP 4.1) and Mader density-to-connectivity lemma (DP 4.4) | DP small highly connected subgraph theorem 2.3 | Theorem 4 |
| Wollan rooted-minor theorem (DP 5.9) | DP 5.11 and 5.13 | Theorem 4 |
| DP 2.5/6.4 and auxiliaries 6.1–6.2 | Obtain separation in Theorem 7.1 | Theorem 4 |

A quantitative linkedness factor of at most 35 suffices for the exact
Corollary 24 constants. Thomas–Wollan gives factor 16 through its easier
edge-density theorem, and its stronger theorem gives factor 10.

Two source-to-formal-statement checks belong in the proof document:

* DP 5.11 is printed with `ℓ ≥ s ≥ 2`, while DP 5.13 invokes it with
  `b` potentially smaller than `a`. Check and prove the broader version
  directly from DP 5.9 and 5.10 before using that application.
* DP 5.15 applies `(a,b)`-wovenness to only `|I| ≤ b` paths. Define the
  formal predicate for *up to* `b` pairs, or prove the required
  monotonicity by padding and then deleting unused paths. Allow singleton
  pairs and roots that are terminals, as in the paper's convention.

## Order of work

1. **First milestone: a proof contract.** Create a companion proof
   document that states both endpoints, the shared woven recursion,
   every leaf above, and every parameter translation in full. Prove the
   common combinatorial steps there; expand external leaves in a
   tracked order. Label every remaining cited leaf explicitly. Audit the
   two parameter issues above before declaring any part self-contained.
2. Add a finite graph API for vertex connectivity, vertex deletion,
   indexed linkages (including length-zero paths), rooted minor models,
   and wovenness. Reuse the existing `MinorModel` and
   `ChromaticSeparable` interfaces. Prove the proxy, fan, rerouting, and
   three-child assembly lemmas independently of chromatic estimates.
3. Prove the shared recursion under explicit hub, separation, base, and
   numerical hypotheses. Keep temporary deep inputs as *theorem
   hypotheses*; do not introduce axioms or `sorry`.
4. Specialize first to main paper Lemma 23 and Corollary 24. This tests
   the common engine with the shorter dependency branch and preserves
   its exact constants.
5. Formalize DP 2.3, 5.13, and 2.5 through their source dependencies;
   then specialize the same engine to DP 7.1 and derive Theorem 1.6.
   Bridge the result to the existing `Theorem4Statement`.
6. Update `docs/blueprint.md` as proofs land. Use focused
   `lake env lean` checks for modules, then `lake build` and a no-sorry
   axiom audit for both endpoints and the now unconditional Theorem 1.

The first milestone is complete only when the proof contract identifies
every unresolved leaf and reproduces the shared recursion with checked
hypotheses and budgets. Call the document *self-contained* only after
every leaf it uses has a proof in that document, including its appendices.
If it relies on earlier verified project writeups, state those dependencies
and describe the document as complete relative to them.
