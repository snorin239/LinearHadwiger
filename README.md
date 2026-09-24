# Proof of linear Hadwiger's conjecture in Lean

This project aims to formalize the paper in [paper/main.pdf](paper/main.pdf),
with [paper/main.tex](paper/main.tex) as its source. The main target is Theorem 1
(`thm:linear`): there is an absolute constant `C` such that every finite simple
graph with no `K_t` minor has chromatic number at most `C t`, for `t ≥ 2`.

The project uses Lean 4.32.1 and Mathlib v4.32.1, matching the adjacent
RamseyLean project. The pinned dependency revisions are in `lake-manifest.json`.

## Layout

- `paper/`: the supplied TeX source and PDF; these are reference material.
- `HadwigerLean/`: Lean modules.
- `HadwigerLean.lean`: root library module.
- `docs/blueprint.md`: paper-to-Lean result map and dependency status.
- `FORMALIZATION.md`: short status and scope record.

Run `lake build` at the project root to check the library. On this computer,
`.lake/packages` is a local junction to RamseyLean's already downloaded
dependencies. The entire `.lake` directory is ignored by Git.
