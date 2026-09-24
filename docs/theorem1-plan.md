# Conditional Theorem 1 milestone

This plan covers a Lean proof of paper Theorem 1 (`thm:linear`,
`paper/main.tex:80-83`) from the already checked Theorem 2, assuming exactly
paper Theorem 4 (`thm:dp`, lines 212-227) and Corollary 24 (`cor:outer`,
lines 1382-1398). It does not prove either assumed input. Paper Theorem 5
(`thm:density`) is not needed for this conditional deduction: its use inside
the paper's proof of Corollary 24 is covered by assuming that corollary.

## Certificate and public statements

Do **not** declare Theorem 4 or Corollary 24 as global Lean axioms. Define
faithful propositions `Theorem4Statement` and `Corollary24Statement` and prove
`linear_of_theorem4_corollary24 (h4 : Theorem4Statement)
(h24 : Corollary24Statement)`. The hypotheses must be visible in the theorem
type. After the two inputs are proved later, apply this theorem to obtain the
unconditional result. Do not describe the conditional milestone as an
unconditional formalization of Theorem 1.

The readable internal theorem may use `HasCliqueMinor` and `chromatic`.
Publish a companion theorem whose *graph conclusion* uses only Lean/Mathlib
terminology: `G.Colorable (C * t)` for every finite `SimpleGraph V` and
`t >= 2` with no family `B : Fin t -> Set V` of pairwise disjoint connected
induced branch sets such that every distinct pair touches by an edge. Prove
the equivalence of this expanded hypothesis with `¬ HasCliqueMinor G t`.
Connectedness already includes nonemptiness. Mathlib currently has no graph
minor predicate; expanding the branch-set condition avoids an opaque
project-specific predicate at the public boundary. No `DecidableEq V` should
appear in the public theorem type merely because an internal proof needs it.

Likewise add a Mathlib-facing form of checked Theorem 2. A convenient
equivalent family quantifies `h : ℕ`, assumes no branch-set model of
`K_(h+1)`, and concludes
`(ENat.toNat G.chromaticNumber : ℝ) <= 4*h + ε*Fintype.card V +
(100/ε)^(2000/ε²)` for `0 < ε <= 1`. Prove it from
`HadwigerLean.Theorem2.quantitative_bound`, and prove that taking
`h = cliqueMinorNumber G` recovers the exact paper form. This exposes
Mathlib's chromatic number and the actual numeric expression rather than
the internal `chromatic` and `Aepsilon` aliases.

Theorem 4's input proposition should retain the paper's `C_DP` both as
coefficient and in the small-order cutoff, the integer window
`t/sqrt(log t) <= a <= t`, and **arbitrary subgraphs** `H ⊆ G` (not only
induced subgraphs). Its pointwise elimination form is convenient: if every
eligible `H` has `χ(H) <= D*a`, then `χ(G) <= C_DP*(1+D)*t`.
This is the direct consequence of the displayed maximum `f(G,t)` and can be
used as the formal statement if its equivalence to that maximum formulation
is proved in Lean in the interface module. Corollary 24's proposition
must retain its power-of-three scale condition, induced `Y ⊆ G`, separation
premise, and stated coefficient. Prove any broad-window interface used by
the bootstrap *from* this exact proposition.

## Dependency order and four work lanes

| Phase | Owner | Modules | Deliverable |
| --- | --- | --- | --- |
| 0 | Main agent | `Graph/MinorFree.lean`, `Bootstrap/Definitions.lean`, `Deduction/ExternalInputs.lean` | Freeze the common signatures: clique-minor order monotonicity and `¬ HasCliqueMinor G t ↔ cliqueMinorNumber G < t`; local-bound, separability, and no-large-connected-bipartite predicates; faithful input propositions. Add a shared disjoint-palette coloring lemma if both graph lanes need it. |
| 1A, parallel | Agent 1 | `Bootstrap/Packing.lean` | Paper Lemma 12 (`lem:packing`, lines 968-987): a packing gives `W,R,Q`, `Q` a minor of `G`, `|Q| <= |G|/k`, no connected bipartite induced `k`-set in `G[R]`, and `χ(G[W]) <= 2χ(Q)`. Reuse `ConnectedPartition.touchingQuotient` where suitable. |
| 1B, parallel | Agent 2 | `Bootstrap/Path.lean`, `Bootstrap/Separation.lean` | Paper Lemmas 13-14 (lines 992-1071): induced-path localization, `|J| <= α(J)χ_f(J) <= 2α(J)h(J)` using the checked Reed--Seymour theorem, then the two-subgraph separation result. The predicate from phase 0 is inherited by induced subgraphs. |
| 1C, parallel | Agent 3 | `Deduction/Asymptotics.lean`, `Deduction/InitialLocal.lean` | Eventual real-log/rpow estimates and Theorem 2's initial local bound; the uniform `k` and `u=14a` inequalities for the bootstrap; the Theorem 4 window comparison after the ninth iteration. An existential threshold is enough; explicit huge thresholds are unnecessary. |
| 2 | Main agent | `Bootstrap/Step.lean` | Combine 1A-1C and Corollary 24 into `LocalLinearBound α -> LocalLinearBound (4*α/3)` for `α>0`. At each scale, Lemma 14 verifies precisely Corollary 24's separation premise. |
| 3 | Main agent | `Deduction/Theorem1.lean`, `Deduction/PublicStatements.lean`, `Deduction/Audit.lean` | Iterate phase 2 nine times, apply Theorem 4, extend the large-`t` result to every `t>=2`, publish Mathlib-facing Theorems 1 and 2, and run the audits. Update the root imports and blueprint. |

Freeze phase-0 statements before parallel implementation. Each agent owns
only its listed files and uses focused `lake env lean` checks. The main agent
resolves any signature changes, integrates the branches, and runs `lake build`.
Intermediate lemmas may be strengthened or replaced to make the proof easier,
provided the input propositions and public conclusions keep their paper
meaning.

## Mathematical assembly

1. From Theorem 2 take, for example, `ε = (log t)^(-1/3)`. Eventually
   `0 < ε <= 1` and `Aε <= t`; on `|G| <= t*(log t)^(1/3)` this gives a local
   `6t` coloring bound. The paper's `5t` choice is optional.
2. For a local bound at exponent `α>0`, use
   `k = ceil((log t)^(α/3))`. Packing colors `W` via the quotient `Q`.
   The order bound from Reed--Seymour and the path lemma supply separation
   on the remainder at each Corollary 24 scale. This yields a local bound
   at `4*α/3`, with the paper's coefficient
   `2D + 3*(10^6*(D+1)+62000)` or a checked larger one.
3. Nine iterations from `α=1/3` reach `(4/3)^9/3 > 4`.
   For sufficiently large `t`, every `a` in Theorem 4's window exceeds
   the local threshold and satisfies
   `C_DP*(log a)^4 <= (log a)^α`. Theorem 4 then gives a linear bound
   for all sufficiently large `t`.
4. Fix a large threshold `T`. For `2 <= t < T`, a `K_T` minor would
   contain a `K_t` minor, so a `K_t`-minor-free graph is also
   `K_T`-minor-free. Apply the large-`T` bound and enlarge the absolute
   constant by `T`. This avoids Theorem 5 entirely in this milestone.

## Acceptance checks

- `lake build` succeeds from the repository root, and all new declarations
  have proofs without `sorry`, `admit`, or new placeholder `axiom`s.
- `#check`/`#print` show the conditional theorem has exactly the two named
  mathematical inputs; inspect the printed definitions of those inputs.
- `assert_no_sorry` (from `Mathlib.Util.AssertNoSorry`) succeeds for the
  conditional theorem and both public wrappers. `#print axioms` shows no
  project-specific assumed theorem. These are complementary checks: explicit
  theorem hypotheses are not reported by `#print axioms`.
- The public statement uses the expanded branch-set condition and
  `SimpleGraph.Colorable`; the public Theorem 2 form uses Mathlib's
  `chromaticNumber`. Proved bridges connect both to internal APIs.
- The blueprint records the final paper-to-Lean mapping and labels the
  result **conditional on Theorem 4 and Corollary 24**.
