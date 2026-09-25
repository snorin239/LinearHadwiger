import HadwigerLean.Graph.RootedDensity.FanExtension
import Mathlib.Tactic

/-! An induced universal core accepts a clean fan at arbitrary labelled arrivals. -/

namespace HadwigerLean.RootedDensity

universe u v

/-- Restrict a full-target rooted model to selected target labels. -/
def rootedMinorModel_restrictFullTarget
    {W : Type u} [Fintype W] {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    {root : ↥((Finset.univ : Finset W) : Set W) → V}
    (M : RootedMinorModel (H.induce ((Finset.univ : Finset W) : Set W)) G root)
    (Y : Finset W) :
    RootedMinorModel (H.induce (Y : Set W)) G
      (fun i => root ⟨i, Finset.mem_univ _⟩) where
  branch := fun i => M.branch ⟨i, Finset.mem_univ _⟩
  connected := fun i => M.connected ⟨i, Finset.mem_univ _⟩
  disjoint := by
    intro i j hij
    apply M.disjoint
    intro heq
    have hval : (i : W) = (j : W) :=
      congrArg (fun z : ↥((Finset.univ : Finset W) : Set W) => (z : W)) heq
    exact hij (Subtype.ext hval)
  adjacent := by
    intro i j hij
    exact M.adjacent hij
  root_mem := fun i => M.root_mem ⟨i, Finset.mem_univ _⟩

/-- Universality of the induced core supplies a rooted model at the
arrivals of a clean fan, even when the fan uses fewer than all target labels.
The unused labels are assigned to additional core vertices. -/
theorem rootedMinor_of_universal_induced_and_clean_fan
    {W : Type u} [Fintype W] {V : Type v} [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (J : Finset V)
    (hcore : Universal (G.induce (J : Set V)) H)
    (hW : 0 < Fintype.card W)
    (Y : Finset W) (P : IndexedPairs ↥(Y : Set W) V)
    (L : IndexedLinkage G P)
    (hfinish : ∀ i, P.finish i ∈ J)
    (hfirst : ∀ i x, x ∈ pathVertexSet (L.path i) →
      x ∈ J → x = P.finish i) :
    Nonempty (RootedMinorModel (H.induce (Y : Set W)) G P.start) := by
  classical
  let J' : Type v := ↥(J : Set V)
  let arrival : ↥(Y : Set W) → J' := fun i => ⟨P.finish i, hfinish i⟩
  have harrinj : Function.Injective arrival := by
    intro i j heq
    exact L.finish_injective (congrArg Subtype.val heq)
  let A : Finset J' := Finset.univ.image arrival
  have hAcard : A.card ≤ Fintype.card W := by
    calc
      A.card ≤ (Finset.univ : Finset ↥(Y : Set W)).card := Finset.card_image_le
      _ = Y.card := by simp
      _ ≤ Fintype.card W := by
        simpa using Finset.card_le_card (Finset.subset_univ Y)
  have hJcard : Fintype.card W ≤ (Finset.univ : Finset J').card := by
    simpa [J'] using hcore.1
  obtain ⟨T, hAT, _, hT⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ A) hAcard hJcard
  have hJnonempty : Nonempty J' :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le hW hJcard)
  let default : J' := Classical.choice hJnonempty
  let f : W → J' := fun i => if hi : i ∈ Y then arrival ⟨i, hi⟩ else default
  have hfimage : Y.image f ⊆ T := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply hAT
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by simp [f, hi]⟩
  have hfinj : Set.InjOn f (Y : Set W) := by
    intro i hi j hj heq
    have hi' : (⟨i, hi⟩ : ↥(Y : Set W)) = ⟨j, hj⟩ := by
      apply harrinj
      have hiY : i ∈ Y := hi
      have hjY : j ∈ Y := hj
      have hfi : f i = arrival ⟨i, hi⟩ := by simp [f, hiY]
      have hfj : f j = arrival ⟨j, hj⟩ := by simp [f, hjY]
      exact hfi.symm.trans (heq.trans hfj)
    exact congrArg Subtype.val hi'
  obtain ⟨e, he⟩ :=
    Finset.exists_equiv_extend_of_card_eq hT.symm hfimage hfinj
  let rootFull : ↥((Finset.univ : Finset W) : Set W) → J' :=
    fun i => (e (i : W) : J')
  have hrootInj : Function.Injective rootFull := by
    intro i j hij
    apply Subtype.ext
    exact e.injective (Subtype.ext hij)
  have hrange : Set.range rootFull = (T : Set J') := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact (e (i : W)).property
    · intro hz
      obtain ⟨i, hi⟩ := e.surjective ⟨z, hz⟩
      exact ⟨⟨i, Finset.mem_univ _⟩, congrArg Subtype.val hi⟩
  obtain ⟨M⟩ := hcore.2 T hT Finset.univ rootFull hrootInj hrange
  let R := rootedMinorModel_restrictFullTarget M Y
  have hrootEq : (fun i : ↥(Y : Set W) =>
      rootFull ⟨i, Finset.mem_univ _⟩) = arrival := by
    funext i
    simpa [rootFull, f, i.property] using he (i : W) i.property
  have hM : Nonempty (RootedMinorModel (H.induce (Y : Set W))
      (G.induce (J : Set V)) arrival) := by
    rw [← hrootEq]
    exact ⟨R⟩
  exact rootedMinor_of_induced_rootedMinor_and_clean_fan L
    (J : Set V) hfinish hfirst hM

end HadwigerLean.RootedDensity





