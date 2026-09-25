import HadwigerLean.Woven.OuterInductionComplete
import Mathlib.Util.AssertNoSorry

/-! Proof audit for the shared outer woven recursion. -/

assert_no_sorry HadwigerLean.Woven.exists_solution_of_three_child_nonbase
assert_no_sorry HadwigerLean.Woven.woven_nonbase_of_hub_separation
assert_no_sorry HadwigerLean.Woven.outerAt_top_of_contracts

#print axioms HadwigerLean.Woven.outerAt_top_of_contracts