import HadwigerLean.Woven.DoubleFanTransport
import HadwigerLean.Woven.DoubleFanCost
import Mathlib.Tactic

/-!
# A chromatically cheap double fan inside an induced connected region

The clone construction runs on the induced region. Graph-embedding transport
and chordless shortening return an ambient fan, still supported in that
region, with four colors per source.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_double_fan_inside_connected_region
    (G : SimpleGraph V) (R Z D : Finset V) (k : ℕ)
    (hR : VertexConnected (G.induce (R : Set V)) k)
    (hZR : Z ⊆ R) (hDR : D ⊆ R)
    (hcount : 3 * Z.card ≤ k)
    (hDcard : 2 * Z.card ≤ D.card)
    (hdis : Disjoint Z D) :
    ∃ F : DoubleFan G Z D,
      F.vertexFinset ⊆ R ∧
      chromatic (G.induce (F.vertexFinset : Set V)) ≤ 4 * Z.card := by
  classical
  let Z' : Finset (R : Set V) :=
    Finset.univ.filter (fun z : (R : Set V) => (z : V) ∈ Z)
  let D' : Finset (R : Set V) :=
    Finset.univ.filter (fun z : (R : Set V) => (z : V) ∈ D)
  have hZimage : Z'.image Subtype.val = Z := by
    ext v
    constructor
    · intro hv
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2
    · intro hv
      exact Finset.mem_image.mpr
        ⟨⟨v,hZR hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hDimage : D'.image Subtype.val = D := by
    ext v
    constructor
    · intro hv
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2
    · intro hv
      exact Finset.mem_image.mpr
        ⟨⟨v,hDR hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hZcard : Z'.card = Z.card := by
    rw [← hZimage]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hDcard' : D'.card = D.card := by
    rw [← hDimage]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hdis' : Disjoint Z' D' := by
    apply Finset.disjoint_left.mpr
    intro z hzZ hzD
    exact (Finset.disjoint_left.mp hdis)
      (Finset.mem_filter.mp hzZ).2
      (Finset.mem_filter.mp hzD).2
  obtain ⟨F₀⟩ := exists_double_fan_of_vertexConnected
    (G.induce (R : Set V)) Z' D' k hR
    (by rw [hZcard]; exact hcount)
    (by rw [hZcard,hDcard']; exact hDcard) hdis'
  let e : (G.induce (R : Set V)) ↪g G :=
    SimpleGraph.Embedding.induce (R : Set V)
  let F₁ := F₀.map e
  have hZimageE : Z'.image e = Z := hZimage
  have hDimageE : D'.image e = D := hDimage
  have hmap : ∃ F : DoubleFan G (Z'.image e) (D'.image e),
      ∀ slot, pathVertexSet (F.path slot) ⊆ (R : Set V) := by
    refine ⟨F₁,?_⟩
    intro slot v hv
    obtain ⟨u,rfl⟩ := F₀.map_path_subset_range e slot hv
    exact u.property
  rw [hZimageE,hDimageE] at hmap
  obtain ⟨F₁,hF₁R⟩ := hmap
  obtain ⟨F,hchord,hsub⟩ := F₁.exists_chordless_subfan
  have hFR : F.vertexFinset ⊆ R := by
    intro v hv
    obtain ⟨slot,_,hslot⟩ := Finset.mem_biUnion.mp hv
    have hvpath : v ∈ pathVertexSet (F.path slot) :=
      List.mem_toFinset.mp hslot
    exact hF₁R slot (hsub slot hvpath)
  exact ⟨F,hFR,F.chromatic_vertexFinset_le_four_mul hchord⟩

end Woven
end HadwigerLean
