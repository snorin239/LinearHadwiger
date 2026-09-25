import HadwigerLean.Graph.SmallConnected.PackedVertices
import HadwigerLean.Graph.SmallConnected.ConnectedSetContraction
import Mathlib.Tactic

/-!
# Vertex equivalence between a second contraction and an enlarged family
-/

namespace HadwigerLean

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} (F : ConnectedBlockFamily G)

private abbrev PackedSecondVertex (H : Finset V) :=
  ConnectedSetContractionVertex (F.singletonLift H : Set F.Vertex)

noncomputable def ConnectedBlockFamily.secondToAdded
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    PackedSecondVertex F H → (F.add H hconn hdisj).Vertex
  | none => .inl ⟨H, Finset.mem_insert_self H F.blocks⟩
  | some ⟨q, hq⟩ => by
      cases q with
      | inl B =>
          exact .inl ⟨B.1, Finset.mem_insert_of_mem B.2⟩
      | inr x =>
          have hxH : x.1 ∉ H := by
            intro hx
            exact hq ((F.mem_singletonLift_inr H x).mpr hx)
          have hxoutside : x.1 ∉ (F.add H hconn hdisj).covered := by
            rw [F.covered_add]
            intro hv
            rcases Finset.mem_union.mp hv with hvH | hvF
            · exact hxH hvH
            · exact x.2 hvF
          exact .inr ⟨x.1, hxoutside⟩

noncomputable def ConnectedBlockFamily.addedToSecond
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    (F.add H hconn hdisj).Vertex → PackedSecondVertex F H
  | .inl B => by
      by_cases hBH : B.1 = H
      · exact none
      · have hBold : B.1 ∈ F.blocks :=
          (Finset.mem_insert.mp B.2).resolve_left hBH
        exact some ⟨.inl ⟨B.1, hBold⟩,
          F.not_mem_singletonLift_inl H ⟨B.1, hBold⟩⟩
  | .inr x => by
      have hx : x.1 ∉ H ∪ F.covered := by
        simpa only [← F.covered_add H hconn hdisj] using x.2
      let y : {v : V // v ∉ F.covered} :=
        ⟨x.1, by intro hv; exact hx (Finset.mem_union.mpr (Or.inr hv))⟩
      exact some ⟨.inr y, by
        intro hy
        exact hx (Finset.mem_union.mpr
          (Or.inl ((F.mem_singletonLift_inr H y).mp hy)))⟩

noncomputable def ConnectedBlockFamily.secondAddedEquiv
    (H : Finset V) (hconn : (G.induce (H : Set V)).Connected)
    (hdisj : Disjoint H F.covered) :
    PackedSecondVertex F H ≃ (F.add H hconn hdisj).Vertex where
  toFun := F.secondToAdded H hconn hdisj
  invFun := F.addedToSecond H hconn hdisj
  left_inv := by
    intro q
    cases q with
    | none =>
        simp [ConnectedBlockFamily.secondToAdded,
          ConnectedBlockFamily.addedToSecond]
    | some q =>
        rcases q with ⟨q, hq⟩
        cases q with
        | inl B =>
            have hBH : B.1 ≠ H := by
              intro h
              have hH : H.Nonempty := by
                obtain ⟨v⟩ := hconn.nonempty
                exact ⟨v.1, v.2⟩
              exact F.not_mem_blocks_of_disjoint_covered H hH hdisj (h ▸ B.2)
            simp [ConnectedBlockFamily.secondToAdded,
              ConnectedBlockFamily.addedToSecond, hBH]
        | inr x =>
            simp [ConnectedBlockFamily.secondToAdded,
              ConnectedBlockFamily.addedToSecond]
  right_inv := by
    intro q
    cases q with
    | inl B =>
        by_cases hBH : B.1 = H
        · simp [ConnectedBlockFamily.secondToAdded,
            ConnectedBlockFamily.addedToSecond, hBH]
          exact Subtype.ext hBH.symm
        · simp [ConnectedBlockFamily.secondToAdded,
            ConnectedBlockFamily.addedToSecond, hBH]
    | inr x =>
        simp [ConnectedBlockFamily.secondToAdded,
          ConnectedBlockFamily.addedToSecond]

end HadwigerLean
