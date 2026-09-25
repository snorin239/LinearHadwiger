import HadwigerLean.ReedSeymour.Parity
import Mathlib.Tactic

/-!
# A shortest stem into a connected piece

A minimum-length path from a vertex to a nonempty target set meets that set
only at its finish. Every earlier vertex except the penultimate has no edge
to the target set; otherwise its prefix and that edge would be shorter.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A shortest vertex-to-set path with the exact cross-edge property needed
for the cheap-tree construction. -/
theorem exists_shortest_stem_to_set
    (hconn : G.Connected) (Q : Finset V) (hQ : Q.Nonempty)
    (v : V) :
    ∃ (b : V) (p : G.Walk v b), b ∈ Q ∧ p.IsPath ∧
      p.IsChordless ∧
      (∀ z, z ∈ p.support → z ∈ Q → z = b) ∧
      (∀ z, z ∈ p.support → z ≠ b → z ≠ p.penultimate →
        ∀ y ∈ Q, ¬ G.Adj z y) := by
  classical
  let P (n : ℕ) : Prop :=
    ∃ b : V, b ∈ Q ∧ ∃ p : G.Walk v b, p.length = n
  have hP : ∃ n, P n := by
    obtain ⟨b,hb⟩ := hQ
    let q : G.Walk v b := (hconn v b).some
    exact ⟨q.length,b,hb,q,rfl⟩
  obtain ⟨b,hb,p,hpn⟩ := (Nat.find_spec hP : P (Nat.find hP))
  have hmin (y : V) (hy : y ∈ Q) (q : G.Walk v y) :
      p.length ≤ q.length := by
    rw [hpn]
    exact Nat.find_min' hP ⟨y,hy,q,rfl⟩
  have hshort : p.length = G.dist v b := by
    obtain ⟨q,hq⟩ := (hconn v b).exists_walk_length_eq_dist
    have hle := hmin b hb q
    have hge := G.dist_le p
    omega
  have hmeet (z : V) (hz : z ∈ p.support) (hzQ : z ∈ Q) :
      z = b := by
    by_contra hne
    have hlt := p.length_takeUntil_lt_length hz hne
    have hle := hmin z hzQ (p.takeUntil z hz)
    omega
  refine ⟨b,p,hb,p.isPath_of_length_eq_dist hshort,
    ReedSeymour.shortest_walk_isChordless p hshort,hmeet,?_⟩
  intro z hz hzb hzpen y hy hzy
  have hlt : (p.takeUntil z hz).length < p.length :=
    p.length_takeUntil_lt_length hz hzb
  have hne : (p.takeUntil z hz).length ≠ p.length - 1 := by
    intro heq
    have hget := p.getVert_length_takeUntil hz
    rw [heq] at hget
    exact hzpen hget.symm
  have hshorter : (p.takeUntil z hz).length + 1 < p.length := by
    omega
  have hle := hmin y hy ((p.takeUntil z hz).concat hzy)
  simp only [SimpleGraph.Walk.length_concat] at hle
  omega

end Inseparability
end HadwigerLean
