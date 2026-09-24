import HadwigerLean.Basic
import HadwigerLean.Graph.Finite
import HadwigerLean.Graph.Minor
import HadwigerLean.Graph.TouchingQuotient
import HadwigerLean.Graph.SimplicialElimination
import HadwigerLean.Graph.CliqueMinor
import HadwigerLean.Optimization.FiniteLP
import HadwigerLean.Coloring.Fractional
import HadwigerLean.Coloring.FractionalLP
import HadwigerLean.Coloring.IntegralComparison
import HadwigerLean.Coloring.PairLoad
import HadwigerLean.ReedSeymour.Bound
import HadwigerLean.ReedSeymour.Maximal
import HadwigerLean.ReedSeymour.Strategy
import HadwigerLean.ReedSeymour.Conclusion
import HadwigerLean.ReedSeymour.Theorem

/-!
Root module for the formalization of `paper/main.tex`.
The checked Reed--Seymour lemmas and conditional bound are imported here.
The unconditional Reed--Seymour theorem and Theorem 2 remain proof targets.
-/
