# Repository instructions

## Objective

Formalize the paper in `paper/main.tex` in Lean 4 with Mathlib. The main target
is Theorem 1 (`thm:linear`). Treat the paper as the source for mathematical
intent and Lean as the source for the checked formal statement.

## Start a mathematical task

1. Read the relevant paper passage and `docs/blueprint.md`.
2. Inspect nearby Lean modules and search Mathlib for existing definitions.
3. Record significant modeling choices and paper-to-Lean mappings in the
   blueprint.

## Verification

- Run `lake build` from the repository root after Lean changes.
- Use focused `lake env lean` checks while developing a module.
- Do not present `sorry`, `admit`, or new placeholder axioms as a completed
  formalization. Distinguish an unformalized result from a checked proof.
- Do not edit the paper source unless the task explicitly asks for it.
- Keep dependency and toolchain changes separate from proof changes, and do
  not download dependencies when the existing local cache can be used.

## Mathematical skill routing

- For a nontrivial new proof, use `$mathematical-research`.
- For a mathematical manuscript, proof document, LaTeX source, or PDF, use
  `$mathematical-writeups`.
- For proofreading a mathematical paper or proof, use
  `$mathematical-proofreading` and announce its use.
- Subagent provisions inside these skills apply only when the user explicitly requests multiagent work.
