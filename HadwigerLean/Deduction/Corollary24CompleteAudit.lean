import HadwigerLean.Deduction.Corollary24Complete
import Mathlib.Util.AssertNoSorry

/-! Proof audit for the unconditional Corollary 24 endpoint. -/

assert_no_sorry HadwigerLean.Deduction.cor24_base_woven
assert_no_sorry HadwigerLean.Deduction.cor24_hub_contract
assert_no_sorry HadwigerLean.Deduction.cor24_sep_contract
assert_no_sorry HadwigerLean.Deduction.cor24_outerAt_top
assert_no_sorry HadwigerLean.Deduction.corollary24_proved

#print axioms HadwigerLean.Deduction.corollary24_proved