import HadwigerLean.Inseparability.CheapTreeStep

/-!
# Cheap connected piece through prescribed vertices

Every nonempty set of prescribed vertices in a connected graph lies in a
connected induced vertex set whose chromatic number falls to at most two
after marking at most three vertices per prescribed vertex.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- The cheap-tree lemma of Section 7.2, in finite induced-set form. -/
theorem exists_cheap_tree
    (hconn : G.Connected) (S : Finset V) (hS : S.Nonempty) :
    ∃ Q T : Finset V,
      S ⊆ T ∧ T ⊆ Q ∧ T.card ≤ 3 * S.card ∧
      (G.induce (Q : Set V)).Connected ∧
      chromatic (G.induce ((Q \ T : Finset V) : Set V)) ≤ 2 := by
  classical
  have aux : ∀ S : Finset V, S.Nonempty →
      ∃ Q T : Finset V,
        S ⊆ T ∧ T ⊆ Q ∧ T.card ≤ 3 * S.card ∧
        (G.induce (Q : Set V)).Connected ∧
        chromatic (G.induce ((Q \ T : Finset V) : Set V)) ≤ 2 := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hS
    obtain ⟨v,hvS⟩ := hS
    let S₀ := S.erase v
    by_cases hS₀ : S₀.Nonempty
    · have hS₀sub : S₀ ⊂ S :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.erase_subset v S,by
            intro heq
            have : v ∈ S₀ := heq ▸ hvS
            simpa [S₀] using this⟩
      obtain ⟨Q₀,T₀,hS₀T,hTQ,hTcard,hQconn,hχ⟩ :=
        ih S₀ hS₀sub hS₀
      have hScard : S₀.card + 1 = S.card := by
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨v,hvS⟩
        simp [S₀, Finset.card_erase_of_mem hvS]
        omega
      have hcover (T : Finset V) (hT₀ : T₀ ⊆ T) (hvT : v ∈ T) :
          S ⊆ T := by
        intro z hzS
        by_cases hzv : z = v
        · subst z
          exact hvT
        · exact hT₀ (hS₀T (Finset.mem_erase.mpr ⟨hzv,hzS⟩))
      by_cases hvQ : v ∈ Q₀
      · let T : Finset V := insert v T₀
        have hTQ' : T ⊆ Q₀ := by
          intro z hz
          rcases Finset.mem_insert.mp hz with h | h
          · exact h ▸ hvQ
          · exact hTQ h
        have hTcard' : T.card ≤ 3 * S.card := by
          have hle := Finset.card_insert_le v T₀
          dsimp [T]
          omega
        have hrem : Q₀ \ T ⊆ Q₀ \ T₀ := by
          intro z hz
          exact Finset.mem_sdiff.mpr
            ⟨(Finset.mem_sdiff.mp hz).1,by
              intro hzT₀
              exact (Finset.mem_sdiff.mp hz).2
                (Finset.mem_insert_of_mem hzT₀)⟩
        refine ⟨Q₀,T,hcover T (Finset.subset_insert v T₀)
          (Finset.mem_insert_self v T₀),hTQ',hTcard',hQconn,?_⟩
        exact (chromatic_induce_mono_finset G hrem).trans hχ
      · obtain ⟨Q,T,hQsub,hvQ,hTsub,hvT,hTQ',hTcard',hQconn',hχ'⟩ :=
          cheap_tree_add_outside hconn Q₀ T₀ v hQconn hTQ hχ hvQ
        refine ⟨Q,T,hcover T hTsub hvT,hTQ',?_,hQconn',hχ'⟩
        omega
    · have hS₀empty : S₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS₀
      have hSsing : S = {v} := by
        have hrestore := Finset.insert_erase hvS
        simpa [S₀,hS₀empty] using hrestore.symm
      subst S
      have hχempty :
          chromatic (G.induce ((({v} : Finset V) \ {v} : Finset V) : Set V)) ≤ 2 := by
        haveI : IsEmpty (↥((∅ : Finset V) : Set V)) := by
          refine ⟨fun z => ?_⟩
          simpa using z.property
        have hzero : chromatic (G.induce ((∅ : Finset V) : Set V)) = 0 :=
          (chromatic_eq_zero_iff _).mpr inferInstance
        have hset : ((({v} : Finset V) \ {v} : Finset V) : Set V) =
            (∅ : Set V) := by
          ext z
          simp
        rw [hset]
        have hFinsetEmpty : ((∅ : Finset V) : Set V) = (∅ : Set V) := by
          ext z
          simp
        rw [hFinsetEmpty] at hzero
        omega
      exact ⟨{v},{v},Finset.Subset.rfl,Finset.Subset.rfl,
        by simp,by
          have hset : (({v} : Finset V) : Set V) = ({v} : Set V) := by
            ext z
            simp
          rw [hset]
          simp,hχempty⟩
  exact aux S hS

end Inseparability
end HadwigerLean





