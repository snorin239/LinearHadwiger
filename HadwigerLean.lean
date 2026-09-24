import HadwigerLean.Basic
import HadwigerLean.Graph.Finite
import HadwigerLean.Graph.Minor
import HadwigerLean.Graph.TouchingQuotient
import HadwigerLean.Optimization.FiniteLP
import HadwigerLean.Coloring.Fractional
import HadwigerLean.Coloring.FractionalLP
import HadwigerLean.Coloring.IntegralComparison
import HadwigerLean.Coloring.PairLoad

/-!
Root module for the formalization of `paper/main.tex`.
The checked foundation modules are imported here. Theorem 2 remains the first
major proof target; this file imports it only when its formal proof checks.
-/
