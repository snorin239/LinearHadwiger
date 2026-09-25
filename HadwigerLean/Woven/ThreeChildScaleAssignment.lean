import HadwigerLean.Woven.ThreeChildAssembly

/-!
# Arithmetic of the three-child connector assignment

At successive outer scales `3c = 2a`, the two connectors of one parent
root land in different child blocks.
-/

namespace HadwigerLean
namespace Woven

/-- Integers differing by at least `c` lie in different length-`c` blocks. -/
private theorem div_ne_of_gap {c q r : ℕ} (hc : 0 < c)
    (hgap : q + c ≤ r) : q / c ≠ r / c := by
  intro heq
  have hq := Nat.mod_lt q hc
  have hr := Nat.mod_lt r hc
  have hqdiv := Nat.mod_add_div q c
  have hrdiv := Nat.mod_add_div r c
  rw [← heq] at hrdiv
  omega

/-- The first coordinate of the canonical assignment is its child block. -/
private theorem scaleAssignment_first_val {a c : ℕ}
    (hscale : 2 * a = 3 * c) (q : Fin (2 * a)) :
    ((scaleAssignment hscale q).1 : ℕ) = q.val / c := by
  rfl

/-- The two connectors of every parent root enter different children. -/
theorem scaleAssignment_different_children {a c : ℕ}
    (hscale : 2 * a = 3 * c) (hc : 0 < c)
    (i : Fin a) :
    (scaleAssignment hscale (firstConnector i)).1 ≠
      (scaleAssignment hscale (secondConnector i)).1 := by
  have hca : c ≤ a := by omega
  intro heq
  have hval := congrArg Fin.val heq
  rw [scaleAssignment_first_val, scaleAssignment_first_val] at hval
  apply div_ne_of_gap hc (q := i.val) (r := a + i.val) (by omega)
  simpa [firstConnector, secondConnector] using hval

end Woven
end HadwigerLean
