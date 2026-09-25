import HadwigerLean.Woven.UniformLinkage

/-! The sharp-order zero-root case of the uniform woven assertion. -/

namespace HadwigerLean.Woven

/-- Connectivity linear in the pair budget supplies wovenness with no
clique roots. Singleton terminal pairs are allowed. -/
theorem woven_empty_of_thirtytwo_mul_connected
    {V : Type*} [Fintype V] (G : SimpleGraph V) (b : ℕ)
    (hconn : VertexConnected G (32 * b)) : Woven G 0 b := by
  intro root _ j hj P hP
  obtain ⟨L⟩ := indexed_linkage_of_thirtytwo_mul_connected G b j hconn hj P hP
  let M : RootedMinorModel (SimpleGraph.completeGraph (Fin 0)) G root := {
    branch := Fin.elim0
    connected := by intro i; exact i.elim0
    disjoint := by intro i; exact i.elim0
    adjacent := by intro i; exact i.elim0
    root_mem := by intro i; exact i.elim0
  }
  refine ⟨{ model := M, linkage := L, exact_intersection := ?_ }⟩
  have hempty : M.toMinorModel.vertices = (∅ : Set V) := by
    simp [MinorModel.vertices, M]
  simp [hempty]

end HadwigerLean.Woven
