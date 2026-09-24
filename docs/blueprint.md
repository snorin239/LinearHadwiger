# Formalization blueprint

Source: `paper/main.tex` and `paper/main.pdf`.

| Paper label | Result | Lean declaration | Status |
| --- | --- | --- | --- |
| `thm:linear` | Linear Hadwiger bound (Theorem 1) | To be chosen | Unformalized |
| `thm:quantitative` | Quantitative coloring bound | To be chosen | Unformalized |
| `thm:bootstrap` | Improvement of the local exponent | To be chosen | Unformalized |

## Modeling decisions

None yet. In particular, the representation of graph minors, chromatic
number, and the local bound predicate remains to be selected after inspecting
the relevant Mathlib interfaces.

## External results and dependencies

The paper invokes results of Reed–Seymour and Delcourt–Postle, among others.
Their precise formal statements and proof or import strategy remain to be
determined. No such result has been assumed as an axiom in the Lean source.
