import HadwigerLean.Graph.ChromaticSlice
import HadwigerLean.Graph.VertexConnectivityIso
import HadwigerLean.Graph.ChromaticConnectivity.Theorem
import Mathlib.Tactic

/-!
# The low chromatic connected hub for Corollary 24
-/

namespace HadwigerLean.Deduction

/-- The GN theorem applied to an exact `980a` chromatic slice gives a
`140a`-connected induced hub with chromatic cost at most `980a`. -/
theorem exists_cor24_hub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : ℕ) (ha : 0 < a)
    (hχ : 980 * a ≤ HadwigerLean.chromatic G) :
    ∃ H : Finset V,
      HadwigerLean.VertexConnected (G.induce (H : Set V)) (140 * a) ∧
      HadwigerLean.chromatic (G.induce (H : Set V)) ≤ 980 * a := by
  classical
  obtain ⟨S, hSχ⟩ := HadwigerLean.exists_induced_chromatic_eq G (980 * a) hχ
  let J := G.induce (S : Set V)
  have hJχ : 7 * (140 * a) ≤ HadwigerLean.chromatic J := by
    simpa [J, hSχ] using (show 7 * (140 * a) ≤ 980 * a by omega)
  obtain ⟨U, hUconn, _hUχ⟩ :=
    HadwigerLean.exists_chromatic_connected_induced J (140 * a) (by omega) hJχ
  let H : Finset V := U.image Subtype.val
  have hset : (H : Set V) = Subtype.val '' (U : Set (S : Set V)) := by
    ext v
    simp [H]
  let e : (J.induce (U : Set (S : Set V))) ≃g
      G.induce (H : Set V) := {
    toEquiv := ((Equiv.Set.image (fun x : (S : Set V) => (x : V))
      (U : Set (S : Set V)) Subtype.val_injective).trans
      (Equiv.setCongr hset.symm))
    map_rel_iff' := by
      intro x y
      rfl
  }
  have hHconn : HadwigerLean.VertexConnected (G.induce (H : Set V)) (140 * a) := by
    exact HadwigerLean.VertexConnected.of_iso e _ hUconn
  have hUupper : HadwigerLean.chromatic (J.induce (U : Set (S : Set V))) ≤ 980 * a := by
    calc
      HadwigerLean.chromatic (J.induce (U : Set (S : Set V))) ≤
          HadwigerLean.chromatic (J.induce ((Finset.univ : Finset (S : Set V)) : Set (S : Set V))) :=
        HadwigerLean.chromatic_induce_mono_finset J (Finset.subset_univ U)
      _ = HadwigerLean.chromatic J := HadwigerLean.chromatic_induce_univ_finset J
      _ = 980 * a := hSχ
  have hχeq : HadwigerLean.chromatic (J.induce (U : Set (S : Set V))) =
      HadwigerLean.chromatic (G.induce (H : Set V)) := by
    unfold HadwigerLean.chromatic
    exact congrArg ENat.toNat (SimpleGraph.chromaticNumber_congr e)
  exact ⟨H, hHconn, hχeq ▸ hUupper⟩

end HadwigerLean.Deduction
