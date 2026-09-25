import HadwigerLean.Graph.RootedDensity.RigidUnion
import Mathlib.Tactic

/-!
# Gluing one-boundary torso branches to a rigid shore

When every branch of a torso model meets the adhesion at most once, the
branches that meet it can be joined to a rooted model in the far shore.
-/

namespace HadwigerLean.RootedDensity

universe u v

/-- A rooted torso model with at most one adhesion vertex per branch lifts
through a rooted model on the far shore, indexed by the branches that touch
the adhesion. -/
theorem rooted_model_lift_torso_one_boundary
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (T : Set I) (b : T → S.left) (r : T → S.right)
    (hb : ∀ i : T, b i ∈ M.branch i.1)
    (hbr : ∀ i : T, ((b i : S.left) : V) = (r i : V))
    (hcover : ∀ i : I, ∀ x ∈ M.branch i,
      (x : V) ∈ S.right → i ∈ T)
    (hunique : ∀ i : I, ∀ x ∈ M.branch i, ∀ y ∈ M.branch i,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y)
    (N : RootedMinorModel (H.induce T) (G.induce S.right) r) :
    Nonempty (RootedMinorModel H G (Subtype.val ∘ root)) := by
  classical
  let near : I → Set V := fun i => Subtype.val '' M.branch i
  let far : I → Set V := fun i =>
    if hi : i ∈ T then Subtype.val '' N.branch ⟨i, hi⟩ else ∅
  have hnear_conn (i : I) : (G.induce (near i)).Connected := by
    exact connected_induce_subtype_image G S.left (M.branch i)
      (torso_branch_connected_near_of_unique_boundary G S (M.branch i)
        (hunique i) (M.connected i))
  have hnear_disj {i j : I} (hij : i ≠ j) : Disjoint (near i) (near j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with ⟨a, ha, rfl⟩
    rcases hxj with ⟨b, hb, hab⟩
    have heq : a = b := Subtype.ext hab.symm
    subst b
    exact (Set.disjoint_left.mp (M.disjoint hij)) ha hb
  have hfar_disj {i j : I} (hij : i ≠ j) : Disjoint (far i) (far j) := by
    by_cases hi : i ∈ T
    · by_cases hj : j ∈ T
      · simp only [far, dif_pos hi, dif_pos hj]
        apply Set.disjoint_left.mpr
        intro x hxi hxj
        rcases hxi with ⟨a, ha, rfl⟩
        rcases hxj with ⟨b, hb, hab⟩
        have heq : a = b := Subtype.ext hab.symm
        subst b
        exact (Set.disjoint_left.mp (N.disjoint (by
          intro heqij
          exact hij (congrArg Subtype.val heqij)))) ha hb
      · simp [far, hj]
    · simp [far, hi]
  have hcross {i j : I} (hij : i ≠ j) : Disjoint (near i) (far j) := by
    by_cases hj : j ∈ T
    · rw [show far j = Subtype.val '' N.branch ⟨j, hj⟩ from dif_pos hj]
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      rcases hxi with ⟨a, ha, rfl⟩
      rcases hxj with ⟨c, hc, hca⟩
      have hi : i ∈ T := hcover i a ha (hca ▸ c.2)
      have hba : a = b ⟨i, hi⟩ :=
        hunique i a ha (b ⟨i, hi⟩) (hb ⟨i, hi⟩)
          (hca ▸ c.2) (by rw [hbr]; exact (r ⟨i, hi⟩).2)
      have hrc : r ⟨i, hi⟩ = c := by
        apply Subtype.ext
        calc
          (r ⟨i, hi⟩ : V) = (b ⟨i, hi⟩ : V) := (hbr ⟨i,hi⟩).symm
          _ = (a : V) := congrArg Subtype.val hba.symm
          _ = (c : V) := hca.symm
      exact (N.other_root_not_mem (by
        intro heqij
        exact hij (congrArg Subtype.val heqij).symm)) (hrc ▸ hc)
    · simp [far, hj]
  let branch : I → Set V := fun i => near i ∪ far i
  have hbranch_conn (i : I) : (G.induce (branch i)).Connected := by
    by_cases hi : i ∈ T
    · change (G.induce (near i ∪ far i)).Connected
      rw [show far i = Subtype.val '' N.branch ⟨i, hi⟩ from dif_pos hi]
      apply connected_induce_near_far_union G S (M.branch i)
        (N.branch ⟨i, hi⟩)
        (torso_branch_connected_near_of_unique_boundary G S (M.branch i)
          (hunique i) (M.connected i)) (N.connected ⟨i, hi⟩)
      refine ⟨(b ⟨i, hi⟩ : V), ?_, ?_⟩
      · exact ⟨b ⟨i, hi⟩, hb ⟨i, hi⟩, rfl⟩
      · exact ⟨r ⟨i, hi⟩, N.root_mem ⟨i, hi⟩, (hbr ⟨i, hi⟩).symm⟩
    · change (G.induce (near i ∪ far i)).Connected
      rw [show far i = ∅ from dif_neg hi]
      rw [Set.union_empty]
      exact hnear_conn i
  have hbranch_disj : Pairwise fun i j => Disjoint (branch i) (branch j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with hni | hfi
    · rcases hxj with hnj | hfj
      · exact (Set.disjoint_left.mp (hnear_disj hij)) hni hnj
      · exact (Set.disjoint_left.mp (hcross hij)) hni hfj
    · rcases hxj with hnj | hfj
      · exact (Set.disjoint_left.mp (hcross hij.symm)) hnj hfi
      · exact (Set.disjoint_left.mp (hfar_disj hij)) hfi hfj
  have hbranch_adj : ∀ ⦃i j⦄, H.Adj i j →
      ∃ x ∈ branch i, ∃ y ∈ branch j, G.Adj x y := by
    intro i j hij
    by_cases hi : i ∈ T
    · by_cases hj : j ∈ T
      · obtain ⟨x, hx, y, hy, hxy⟩ := N.adjacent (show (H.induce T).Adj
            ⟨i, hi⟩ ⟨j, hj⟩ from hij)
        refine ⟨x.1, Or.inr ?_, y.1, Or.inr ?_, hxy⟩
        ·
          rw [show far i = Subtype.val '' N.branch ⟨i, hi⟩ from dif_pos hi]
          exact ⟨x, hx, rfl⟩
        ·
          rw [show far j = Subtype.val '' N.branch ⟨j, hj⟩ from dif_pos hj]
          exact ⟨y, hy, rfl⟩
      · rcases torso_model_edge_real_or_boundary G S M hij with hreal | hboundary
        · obtain ⟨x, hx, y, hy, hxy⟩ := hreal
          exact ⟨x.1, Or.inl ⟨x,hx,rfl⟩,
            y.1, Or.inl ⟨y,hy,rfl⟩, hxy⟩
        · obtain ⟨x,hx,y,hy,_,hyS⟩ := hboundary
          exact (hj (hcover j y hy hyS)).elim
    · rcases torso_model_edge_real_or_boundary G S M hij with hreal | hboundary
      · obtain ⟨x, hx, y, hy, hxy⟩ := hreal
        exact ⟨x.1, Or.inl ⟨x,hx,rfl⟩,
          y.1, Or.inl ⟨y,hy,rfl⟩, hxy⟩
      · obtain ⟨x,hx,y,hy,hxS,_⟩ := hboundary
        exact (hi (hcover i x hx hxS)).elim
  refine ⟨{
    toMinorModel := {
      branch := branch
      connected := hbranch_conn
      disjoint := hbranch_disj
      adjacent := hbranch_adj
    }
    root_mem := ?_
  }⟩
  intro i
  exact Or.inl ⟨root i, M.root_mem i, rfl⟩


/-- A full injective labeling of the rigid adhesion lifts any torso model
whose branches meet the adhesion at most once, provided it assigns each
used boundary vertex the label of its torso branch. -/
theorem rooted_model_lift_torso_one_boundary_of_rigid
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (huni : UniversalAtRightShore H S)
    (T : Set I) (b : T → S.left)
    (hb : ∀ i : T, b i ∈ M.branch i.1)
    (hcover : ∀ i : I, ∀ x ∈ M.branch i,
      (x : V) ∈ S.right → i ∈ T)
    (hunique : ∀ i : I, ∀ x ∈ M.branch i, ∀ y ∈ M.branch i,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y)
    (φ : ↥(Linkedness.separationBoundaryFinset S : Set S.right) ↪ I)
    (hφ : ∀ i : T, ∃ z : ↥(Linkedness.separationBoundaryFinset S : Set S.right),
      φ z = i.1 ∧ ((b i : S.left) : V) = (z.1 : V)) :
    Nonempty (RootedMinorModel H G (Subtype.val ∘ root)) := by
  classical
  obtain ⟨Y, q, ⟨N⟩, hq⟩ := rigid_shore_model_of_labels G S H huni φ
  have hTY : T ⊆ (Y : Set I) := by
    intro i hi
    obtain ⟨z, hz, _⟩ := hφ ⟨i, hi⟩
    change i ∈ Y
    simpa only [hz] using (hq z).choose
  let r : T → S.right := fun i => q ⟨i.1, hTY i.2⟩
  have hbr (i : T) : ((b i : S.left) : V) = (r i : V) := by
    obtain ⟨z, hz, hbz⟩ := hφ i
    obtain ⟨hy, hqz⟩ := hq z
    have heq : (⟨i.1, hTY i.2⟩ : ↥(Y : Set I)) = ⟨φ z, hy⟩ :=
      Subtype.ext hz.symm
    change ((b i : S.left) : V) = (q ⟨i.1, hTY i.2⟩ : V)
    rw [heq, hqz]
    exact hbz
  exact rooted_model_lift_torso_one_boundary G S H root M T b r hb hbr
    hcover hunique (rooted_model_restrict_to_subset N T hTY)


/-- The one-boundary case of reverse rigid truncation needs no prior
labeling: disjoint torso branches supply an injective partial labeling of
used adhesion vertices, which extends over the whole adhesion. -/
theorem rooted_model_lift_torso_one_boundary_rigid
    {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (S : VertexSeparation G)
    (H : SimpleGraph I) (root : I → S.left)
    (M : RootedMinorModel H (Linkedness.torsoGraph G S) root)
    (huni : UniversalAtRightShore H S)
    (hsize : (Linkedness.separationBoundaryFinset S).card ≤ Fintype.card I)
    (T : Set I) (b : T → S.left)
    (hb : ∀ i : T, b i ∈ M.branch i.1)
    (hbS : ∀ i : T, ((b i : S.left) : V) ∈ S.right)
    (hcover : ∀ i : I, ∀ x ∈ M.branch i,
      (x : V) ∈ S.right → i ∈ T)
    (hunique : ∀ i : I, ∀ x ∈ M.branch i, ∀ y ∈ M.branch i,
      (x : V) ∈ S.right → (y : V) ∈ S.right → x = y) :
    Nonempty (RootedMinorModel H G (Subtype.val ∘ root)) := by
  classical
  let Z := Linkedness.separationBoundaryFinset S
  have hbinj : Function.Injective b := by
    intro i j heq
    apply Subtype.ext
    by_contra hne
    exact (Set.disjoint_left.mp (M.disjoint hne)) (hb i) (heq ▸ hb j)
  let q : T → S.right := fun i => ⟨(b i : V), hbS i⟩
  have hqinj : Function.Injective q := by
    intro i j heq
    apply hbinj
    apply Subtype.ext
    exact congrArg (fun z : S.right => (z : V)) heq
  let A : Finset S.right := Finset.univ.image q
  have hAZ : A ⊆ Z := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Linkedness.mem_separationBoundaryFinset S (q i)).mpr (b i).2
  have hA : (A : Set S.right) = Set.range q := by
    ext z
    simp [A]
  let e₀ := Equiv.ofInjective q hqinj
  let e : T ≃ ↥(A : Set S.right) :=
    e₀.trans (Equiv.setCongr hA.symm)
  let f : ↥(A : Set S.right) → I := fun a => (e.symm a).1
  have hf : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  obtain ⟨φ, hφ⟩ := extend_adhesion_labels Z A hAZ f hf hsize
  have hmatch (i : T) :
      φ ⟨q i, hAZ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩ = i.1 := by
    have hiA : q i ∈ A := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have he : e i = ⟨q i, hiA⟩ := by
      apply Subtype.ext
      rfl
    calc
      φ ⟨q i, hAZ hiA⟩ = f ⟨q i, hiA⟩ := hφ ⟨q i, hiA⟩
      _ = i.1 := by
        change (e.symm ⟨q i, hiA⟩).1 = i.1
        rw [← he]
        simp
  apply rooted_model_lift_torso_one_boundary_of_rigid G S H root M huni
    T b hb hcover hunique φ
  intro i
  refine ⟨⟨q i, hAZ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩,
    hmatch i, ?_⟩
  rfl
end HadwigerLean.RootedDensity
