import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Coloring an induced path

A chordless path induces precisely a path graph on its support, so its
vertices admit a Boolean coloring. Odd path length makes the two endpoint
colors different.
-/

namespace HadwigerLean
namespace ReedSeymour

variable {V : Type*} {G : SimpleGraph V} {a b : V}

/-- An induced path has a bipartite induced support graph. -/
noncomputable def chordless_path_support_bicoloring
    (p : G.Walk a b) (hp : p.IsPath) (hchord : p.IsChordless) :
    (G.induce {v | v ∈ p.support}).Coloring Bool := by
  classical
  have hInduced : p.toSubgraph.IsInduced :=
    SimpleGraph.Walk.isInduced_toSubgraph.mpr hchord
  let e : (G.induce {v | v ∈ p.support}) ≃g p.toSubgraph.coe := {
    toEquiv := {
      toFun := fun v => ⟨v.1, p.mem_verts_toSubgraph.mpr v.2⟩
      invFun := fun v => ⟨v.1, p.mem_verts_toSubgraph.mp v.2⟩
      left_inv := by intro v; exact Subtype.ext rfl
      right_inv := by intro v; exact Subtype.ext rfl
    }
    map_rel_iff' := by
      intro x y
      change p.toSubgraph.Adj x.1 y.1 ↔ G.Adj x.1 y.1
      exact ⟨p.toSubgraph.adj_sub, hInduced
        (p.mem_verts_toSubgraph.mpr x.2) (p.mem_verts_toSubgraph.mpr y.2)⟩
  }
  exact ((SimpleGraph.pathGraph.bicoloring (p.length + 1)).comap
    hp.pathGraphIsoToSubgraph.symm.toHom).comap e.toHom

/-- Restricting a walk to an induced graph preserves its length. -/
theorem walk_induce_length {s : Set V}
    (p : G.Walk a b) (hs : ∀ v, v ∈ p.support → v ∈ s) :
    (p.induce s hs).length = p.length := by
  revert hs
  induction p with
  | nil => intro hs; rfl
  | @cons u v w huv p ih =>
      intro hs
      have hs' : ∀ z, z ∈ p.support → z ∈ s := by
        intro z hz
        exact hs z (by simp [hz])
      simpa only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.length_cons]
        using congrArg Nat.succ (ih hs')
/-- For an odd induced path, the endpoint colors in its induced-support
bicoloring are opposite. -/
theorem chordless_odd_path_end_colors_ne
    (p : G.Walk a b) (hp : p.IsPath) (hchord : p.IsChordless)
    (hodd : Odd p.length) :
    let c := chordless_path_support_bicoloring p hp hchord
    c ⟨a, p.start_mem_support⟩ ≠
      c ⟨b, p.end_mem_support⟩ := by
  let c := chordless_path_support_bicoloring p hp hchord
  let q := p.induce {v | v ∈ p.support} (fun _ h => h)
  have hlen : q.length = p.length :=
    walk_induce_length p (fun _ h => h)
  have hoddq : Odd q.length := hlen ▸ hodd
  have hflip := (c.odd_length_iff_not_congr q).mp hoddq
  change c ⟨a, p.start_mem_support⟩ ≠
    c ⟨b, p.end_mem_support⟩
  cases hca : c ⟨a, p.start_mem_support⟩ <;>
    cases hcb : c ⟨b, p.end_mem_support⟩ <;>
    simp_all
/-- An odd induced path has a Boolean coloring of its induced support
with different colors at its endpoints. -/
theorem exists_chordless_odd_path_bicoloring
    (p : G.Walk a b) (hp : p.IsPath) (hchord : p.IsChordless)
    (hodd : Odd p.length) :
    ∃ c : (G.induce {v | v ∈ p.support}).Coloring Bool,
      c ⟨a, p.start_mem_support⟩ ≠
        c ⟨b, p.end_mem_support⟩ :=
  ⟨chordless_path_support_bicoloring p hp hchord,
    chordless_odd_path_end_colors_ne p hp hchord hodd⟩
end ReedSeymour
end HadwigerLean