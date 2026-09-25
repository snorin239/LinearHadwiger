import HadwigerLean.Graph.SmallConnected.ContractionLoss
import HadwigerLean.Graph.SmallConnected.EdgePartition
import HadwigerLean.Graph.ContractionEdges
import Mathlib.Tactic

/-!
# Exact edge count of a connected-set contraction
-/

namespace HadwigerLean

universe u
variable {V : Type u}

/-- The singleton quotient vertices are equivalent to the original
vertices outside the contracted set. -/
noncomputable def connectedSetOutsideEquiv (H : Set V) :
    {x : V // x ∉ H} ≃
      {q : ConnectedSetContractionVertex H //
        q ∈ ({none} : Set (ConnectedSetContractionVertex H))ᶜ} where
  toFun x := ⟨some x, by simp⟩
  invFun q := by
    cases h : q.1 with
    | none => exact False.elim (q.2 (by simpa [h]))
    | some x => exact x
  left_inv := by intro x; rfl
  right_inv := by
    rintro ⟨q, hq⟩
    cases q with
    | none => exact False.elim (hq (by simp))
    | some x => rfl

/-- Away from the contracted vertex, the quotient is the old graph
induced on its outside vertices. -/
noncomputable def connectedSetContractionOutsideIso
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected) :
    (G.induce Hᶜ) ≃g
      ((connectedSetContractionGraph G H hconn).induce
        ({none} : Set (ConnectedSetContractionVertex H))ᶜ) where
  toEquiv := connectedSetOutsideEquiv H
  map_rel_iff' := by
    intro x y
    change (connectedSetContractionGraph G H hconn).Adj
      (some x) (some y) ↔ G.Adj x y
    exact connectedSetContraction_adj_some_some G H hconn x y


/-- The quotient vertex has one neighbor for every outside vertex touched
by the contracted set. -/
theorem connectedSetContraction_degree_none
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    [DecidableRel (connectedSetContractionGraph G (S : Set V) hconn).Adj] :
    (connectedSetContractionGraph G (S : Set V) hconn).degree none =
      (contractedNeighborFinset G S).card := by
  classical
  let Q := connectedSetContractionGraph G (S : Set V) hconn
  let T : Finset {x : V // x ∉ (S : Set V)} :=
    Finset.univ.filter (fun x => ∃ y ∈ S, G.Adj y x.1)
  have hmap : Q.neighborFinset none = T.map Function.Embedding.some := by
    ext q
    cases q with
    | none => simp [Q]
    | some x =>
        simp [T, Q, connectedSetContraction_adj_none_some,
          SimpleGraph.mem_neighborFinset]
  have himage : T.image Subtype.val = contractedNeighborFinset G S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, T]
    constructor
    · rintro ⟨y, ⟨z, hzS, hzy⟩, rfl⟩
      simp only [contractedNeighborFinset, Finset.mem_filter,
        Finset.mem_compl]
      refine ⟨y.2, Finset.card_pos.mpr ?_⟩
      exact ⟨z, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y.1 z).mpr hzy.symm, hzS⟩⟩
    · intro hx
      have hxS : x ∉ S := by
        exact (Finset.mem_filter.mp hx).1 |> Finset.mem_compl.mp
      have hpos : 0 < (G.neighborFinset x ∩ S).card :=
        (Finset.mem_filter.mp hx).2
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      have hz' := Finset.mem_inter.mp hz
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      exact ⟨z, hz'.2, ((G.mem_neighborFinset x z).mp hz'.1).symm⟩
  rw [← Q.card_neighborFinset_eq_degree, hmap, Finset.card_map]
  rw [← himage]
  exact (Finset.card_image_of_injective T Subtype.val_injective).symm

/-- Internal edges and duplicated outside incidences are exactly the
simple-edge loss under connected-set contraction. -/
theorem connectedSetContraction_edgeCount_add_loss
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    [DecidableRel (connectedSetContractionGraph G (S : Set V) hconn).Adj] :
    edgeCount (connectedSetContractionGraph G (S : Set V) hconn) +
      connectedSetContractionLoss G S = edgeCount G := by
  classical
  let Q := connectedSetContractionGraph G (S : Set V) hconn
  have hset : (((Sᶜ : Finset V) : Set V)) = (S : Set V)ᶜ := by
    ext x
    simp
  have hpartition := edgeCount_eq_inside_add_outside_add_cross G S
  rw [hset] at hpartition
  have houtside :
      edgeCount (G.induce (S : Set V)ᶜ) =
        edgeCount (Q.induce
          ({none} : Set (ConnectedSetContractionVertex (S : Set V)))ᶜ) :=
    edgeCount_eq_of_iso (connectedSetContractionOutsideIso
      G (S : Set V) hconn)
  have hdelete :
      edgeCount (Q.induce
        ({none} : Set (ConnectedSetContractionVertex (S : Set V)))ᶜ) +
      Q.degree none = edgeCount Q :=
    edgeCount_induce_compl_singleton_add_degree Q none
  have hdegree : Q.degree none = (contractedNeighborFinset G S).card :=
    connectedSetContraction_degree_none G S hconn
  have hduplicate := contractionDuplicateCost_add_neighborCount G S
  have hreal : (contractionDuplicateCost G S : ℝ) +
      (Q.degree none : ℝ) =
        ∑ w ∈ Sᶜ, ((G.neighborFinset w ∩ S).card : ℝ) := by
    rw [hdegree]
    exact_mod_cast hduplicate
  dsimp only [connectedSetContractionLoss]
  have houtsideR : (edgeCount (G.induce (S : Set V)ᶜ) : ℝ) +
      (Q.degree none : ℝ) = (edgeCount Q : ℝ) := by
    exact_mod_cast (by omega :
      edgeCount (G.induce (S : Set V)ᶜ) + Q.degree none = edgeCount Q)
  have hnat : edgeCount Q +
      (edgeCount (G.induce (S : Set V)) + contractionDuplicateCost G S) =
        edgeCount G := by
    exact_mod_cast (by linarith [hpartition, hreal, houtsideR] :
      (edgeCount Q : ℝ) +
        ((edgeCount (G.induce (S : Set V)) : ℝ) +
          (contractionDuplicateCost G S : ℝ)) = (edgeCount G : ℝ))
  exact hnat
end HadwigerLean