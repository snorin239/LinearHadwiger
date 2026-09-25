import HadwigerLean.Inseparability.StageRawGeometry
import HadwigerLean.Inseparability.StageSourcePieces

/-!
# The nonzero raw CI stage with sources determined by the pieces

The source set consists exactly of the old tangencies and two selected
roots per child. Its canonical enumeration is constructed before the
double fan and the woven child models are formed.
-/

namespace HadwigerLean.Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ci_nonzero_raw_stage_from_pieces
    (G : SimpleGraph V) (p x k m b N oldBound coreBound : ℕ)
    (hp : 0 < p)
    (R Z U D : Finset V) (J : Fin p → Finset V)
    (oldRoot : Fin p × Fin x → V)
    (A : RootedMinorModel
      (SimpleGraph.completeGraph (Fin p × Fin x)) G oldRoot)
    (oldCore : Finset V)
    (childRoot : Fin p → Fin 2 × Fin x → V)
    (hZ : Z = Finset.univ.image (ciSourceValue p x oldRoot childRoot))
    (hrootinj : ∀ i, Function.Injective (childRoot i))
    (hrootJ : ∀ i z, childRoot i z ∈ J i)
    (hJdis : ∀ i j, i ≠ j →
      Disjoint (J i : Set V) (J j : Set V))
    (hJD : ∀ i, Disjoint (J i : Set V) (D : Set V))
    (hJU : ∀ i, Disjoint (J i : Set V) (U : Set V))
    (hAJ : ∀ i, Disjoint A.toMinorModel.vertices (J i : Set V))
    (htangent : ∀ z, A.branch z ∩ (R : Set V) = {oldRoot z})
    (hOldWitness : ∀ z w, z ≠ w →
      ∃ a ∈ A.branch z, ∃ c ∈ A.branch w,
        a ∈ oldCore ∧ c ∈ oldCore ∧ G.Adj a c)
    (hOldCard : oldCore.card ≤ oldBound)
    (hJcard : ∀ i, (J i).card ≤ N)
    (hDcardBound : D.card ≤ N)
    (hCoreBudget : oldBound + p * N + N + (p + 1) * x ≤ coreBound)
    (hWoven : ∀ i, Woven (G.induce (J i : Set V)) (2 * x) b)
    (hb : (4 * p + 1) * x ≤ b)
    (F : Woven.DoubleFan G Z D)
    (hFR : F.vertexFinset ⊆ R)
    (hconn : VertexConnected (G.induce (R : Set V)) k)
    (hZR : Z ⊆ R)
    (hbudget : Z.card + 2 * ((p + 1) * x) ≤ k)
    (hU : U ⊆ R \ Z) (hD : D ⊆ R \ Z)
    (hUcard : 2 * ((p + 1) * x) ≤ U.card)
    (hDcard : 2 * ((p + 1) * x) ≤ D.card)
    (hFU : Disjoint F.vertexFinset U)
    (hDU : Disjoint D U)
    (hDconn : VertexConnected (G.induce (D : Set V))
      (33 * ((4 * p + 1) * x)))
    (hUconn : VertexConnected (G.induce (U : Set V)) k)
    (hReserve : chromatic G ≤ chromatic (G.induce (U : Set V)) + m) :
    Nonempty (StageState G ((p + 1) * x) k m coreBound) := by
  classical
  subst Z
  let Z : Finset V :=
    Finset.univ.image (ciSourceValue p x oldRoot childRoot)
  let source : Fin (3 * p * x) ≃ Z :=
    ciSourceEquivOfPieces p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ
  have hOldSource : ∀ i r,
      (source (ciSourceBlock p x ⟨i.val, by omega⟩ r)).1 =
        oldRoot (i,r) := by
    intro i r
    exact ciSourceEquivOfPieces_old p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ i r
  have hChildOldSource : ∀ i r,
      (source (ciSourceBlock p x ⟨p + 2 * i.val, by omega⟩ r)).1 =
        childRoot i (0,r) := by
    intro i r
    exact ciSourceEquivOfPieces_child p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ i 0 r
  have hChildNewSource : ∀ i r,
      (source (ciSourceBlock p x
        ⟨p + 2 * i.val + 1, by omega⟩ r)).1 =
        childRoot i (1,r) := by
    intro i r
    exact ciSourceEquivOfPieces_child p x G oldRoot A J childRoot
      hrootinj hrootJ hJdis hAJ i 1 r
  have hOldZ : ∀ z, oldRoot z ∈ Z := by
    rintro ⟨i,r⟩
    exact Finset.mem_image.mpr
      ⟨ciSourceBlock p x ⟨i.val, by omega⟩ r,
        Finset.mem_univ _,
        ciSourceValue_old p x oldRoot childRoot i r⟩
  exact ci_nonzero_raw_stage_from_geometry G p x k m b N
    oldBound coreBound hp R Z Z U D J oldRoot A oldCore
    childRoot source hOldSource hChildOldSource hChildNewSource
    hrootinj hrootJ hJdis hJD hJU hAJ htangent hOldZ
    hOldWitness hOldCard hJcard hDcardBound hCoreBudget
    hWoven hb F hFR hconn hZR (Finset.Subset.rfl) hbudget
    hU hD hUcard hDcard hFU hDU hDconn hUconn hReserve

end HadwigerLean.Inseparability
