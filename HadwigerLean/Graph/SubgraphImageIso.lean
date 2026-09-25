import HadwigerLean.Graph.Minor
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! An injective graph homomorphism identifies a subgraph with its image. -/

namespace HadwigerLean

universe u v

noncomputable def subgraphMapIso
    {V : Type u} {W : Type v} {G : SimpleGraph V} {J : SimpleGraph W}
    (f : G ↪g J) (H : G.Subgraph) :
    H.coe ≃g (H.map f.toHom).coe := by
  classical
  let g : H.verts → (H.map f.toHom).verts :=
    fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
  have hgi : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val hxy)
  have hgs : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hfx⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hfx
  let e : H.verts ≃ (H.map f.toHom).verts := Equiv.ofBijective g ⟨hgi, hgs⟩
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro x y
  change (H.map f.toHom).Adj (f x.1) (f y.1) ↔ H.Adj x.1 y.1
  constructor
  · rintro ⟨a, b, hab, hax, hby⟩
    have ha : a = x.1 := f.injective hax
    have hb : b = y.1 := f.injective hby
    simpa [ha, hb] using hab
  · intro hxy
    exact ⟨x.1, y.1, hxy, rfl, rfl⟩

end HadwigerLean


