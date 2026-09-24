import HadwigerLean.Basic
import HadwigerLean.Graph.Finite
import HadwigerLean.Graph.Minor
import HadwigerLean.Graph.TouchingQuotient
import HadwigerLean.Graph.SimplicialElimination
import HadwigerLean.Graph.CliqueMinor
import HadwigerLean.Graph.WeightedMatching
import HadwigerLean.Optimization.FiniteLP
import HadwigerLean.Hypergraph.Indexed
import HadwigerLean.Hypergraph.AlmostPerfectMatching
import HadwigerLean.Probability.FiniteBernoulli
import HadwigerLean.Coloring.Fractional
import HadwigerLean.Coloring.FractionalLP
import HadwigerLean.Coloring.IntegralComparison
import HadwigerLean.Coloring.PairLoad
import HadwigerLean.Coloring.ExactLoad
import HadwigerLean.Coloring.Augmentation
import HadwigerLean.Coloring.LowCodegreeRounding
import HadwigerLean.Coloring.RobustFractional
import HadwigerLean.Quantitative.Recurrence
import HadwigerLean.Quantitative.BackwardPotential
import HadwigerLean.Quantitative.UnionBound
import HadwigerLean.Quantitative.MatchingConstants
import HadwigerLean.Quantitative.MatchingApplication
import HadwigerLean.Quantitative.MatchingParameterBridge
import HadwigerLean.Quantitative.RoundingBridge
import HadwigerLean.Quantitative.Constants
import HadwigerLean.Quantitative.RobustBridge
import HadwigerLean.Quantitative.Theorem2
import HadwigerLean.Quantitative.Theorem2FinalBridge
import HadwigerLean.Quantitative.Peeling
import HadwigerLean.ReedSeymour.Bound
import HadwigerLean.ReedSeymour.Maximal
import HadwigerLean.ReedSeymour.Strategy
import HadwigerLean.ReedSeymour.Conclusion
import HadwigerLean.ReedSeymour.Theorem

/-!
Root module for the formalization of `paper/main.tex`.
The checked Reed--Seymour lemmas and conditional bound are imported here.
The unconditional Reed--Seymour theorem remains a proof target; Theorem 2 is checked.
-/
