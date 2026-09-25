# Linear Hadwiger's conjecture in Lean

This repository contains a Lean 4 + Mathlib formalization of Theorem 1 of
Sergey Norin, [*A proof of the Linear Hadwiger's conjecture*](paper/main.pdf).
The bundled PDF is the source for the statement wording and numbering below.
The final theorem is unconditional: the graph-theoretic inputs used in its
proof are also supplied by checked Lean proofs.

## The statement formalized

**Theorem 1.** There is an absolute constant $C$ such that, for every integer
$t\ge 2$, every finite simple graph $G$ with no $K_t$ minor satisfies

$$
\chi(G)\le Ct.
$$

Here $\chi(G)$ is the chromatic number of $G$, and $K_t$ is the complete graph
on $t$ vertices. A $K_t$ minor is represented by $t$ nonempty, connected,
pairwise disjoint branch sets, with an edge between every two distinct
branch sets.

The public statement uses Mathlib's graph and coloring definitions and
expands the minor obstruction explicitly. In the namespace
`HadwigerLean.Deduction`, with universe parameter `u`, it is:

```lean
theorem theorem1_mathlib_proved :
    ∃ C : ℕ,
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (t : ℕ),
        2 ≤ t →
        (¬ ∃ B : Fin t → Set V,
          (∀ i, (G.induce (B i)).Connected) ∧
          (Pairwise fun i j => Disjoint (B i) (B j)) ∧
          (∀ i j : Fin t, i ≠ j →
            ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)) →
        G.Colorable (C * t)
```

The constant is chosen before the graph and $t$, so it is uniform over
both. Taking $C$ to be a natural number preserves the paper's existential
statement. Mathlib's `Connected` includes nonemptiness, and
`G.Colorable (C * t)` means that a proper coloring with at most $Ct$ colors
exists. The theorem includes the empty graph.

Both this statement and the equivalent version using the project's
`HasCliqueMinor` and `chromatic` definitions are in
[UnconditionalTheorem1.lean](HadwigerLean/Deduction/UnconditionalTheorem1.lean).
See [FORMALIZATION.md](FORMALIZATION.md) for the definitions, paper-to-Lean
map, and proof-route differences.

## Structure of the proof

1. **Fractional coloring and minors.** Finite linear-programming duality and
   a formalization of Reed and Seymour's theorem give
   $\chi_f(G)\le 2h(G)$, where $\chi_f$ is the fractional chromatic number
   and $h(G)$ is the largest order of a complete minor.
2. **Quantitative ordinary coloring.** An almost-perfect hypergraph matching
   theorem rounds fractional colorings with small pair loads. A
   bounded-degree augmentation and a weighted matching contraction yield
   Theorem 2:

   $$
   \chi(G)\le 4h(G)+\varepsilon |V(G)|+
   (100/\varepsilon)^{2000/\varepsilon^2}
   \qquad (0<\varepsilon\le 1).
   $$

3. **The initial local bound.** Theorem 2 gives $\chi(G)\le 6t$ for all
   sufficiently large $t$ when $G$ has no $K_t$ minor and
   $|V(G)|\le t(\log t)^{1/3}$.
4. **Recursive minor construction.** Connectivity, disjoint-path, density,
   and rooted-minor arguments assemble three smaller models into a larger
   one while preserving prescribed linkages. This proves the outer
   recursion and Corollary 24. A further chromatic-inseparability argument
   supplies the Delcourt--Postle small-graph reduction, Theorem 4.
5. **Exponent improvement.** Packing connected induced bipartite subgraphs
   and localizing chromatic number near a short path turn a local linear
   bound at exponent $\alpha>0$ into one at exponent $4\alpha/3$.
6. **Final assembly.** Nine improvements from $1/3$ give
   $(4/3)^9/3>4$, enough to apply Theorem 4. Enlarging the absolute constant
   handles all remaining values $t\ge 2$.

Intermediate results are sometimes strengthened, generalized, or replaced
by sufficient variants. The formalization preserves Theorem 1 and the
explicit bound in Theorem 2.

## Scope

The public target is Theorem 1. The development also proves Theorem 2,
the bootstrap used for Theorem 3, Theorem 4, Corollary 24, and the
supporting results needed to discharge their dependencies. In particular,
Reed--Seymour and the small-graph reduction are proved within the
development rather than left as theorem assumptions.

The result asserts the existence of an absolute constant. It does not
optimize that constant or provide an executable coloring algorithm.

## Building

The project pins Lean and Mathlib to `v4.32.1`; exact dependency revisions
are recorded in [lake-manifest.json](lake-manifest.json). With Elan and Git
installed, run from the repository root:

```sh
lake exe cache get
lake build
```

The cache command retrieves precompiled Mathlib dependencies and can be
omitted when they are already available. The root target
[HadwigerLean.lean](HadwigerLean.lean) imports the final theorem and its
dependency audits. Import `HadwigerLean` to use the development.

To rerun the final audit directly after building:

```sh
lake env lean HadwigerLean/Deduction/Audit.lean
```

## Verification

A local `lake build` completed successfully on September 25, 2026
(3,948 Lake jobs). The source contains no proof placeholders or
user-declared axioms. The final
[audit](HadwigerLean/Deduction/Audit.lean) checks the endpoints with
`assert_no_sorry`; `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for both forms of Theorem 1, Theorem 4,
and Corollary 24. These are Lean's standard logical axioms.

## Sources and attribution

This formalization, including its documentation, was produced by OpenAI
Codex versions 6 Sol and Astra, following guidance from the paper's authors.

The mathematical source is the [bundled paper](paper/main.pdf); its
introduction includes the disclosure about AI assistance in developing
the mathematical proof. The Lean development uses Mathlib and three
vendored EconCSLib files for Fourier--Motzkin elimination, Farkas' lemma,
and linear-programming strong duality. Their source revision and
Apache-2.0 attribution are recorded in the
[vendored README](HadwigerLean/Vendor/EconCSLib/README.md).
