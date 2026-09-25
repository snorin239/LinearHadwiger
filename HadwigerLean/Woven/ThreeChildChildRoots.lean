import HadwigerLean.Woven.ThreeChildConnectedBridge

/-!
# Selecting child target roots

An order lower bound on each child supplies the independent target-root
enumerations required by the three-child assembly.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Select `c` distinct target roots inside each of the three child sets. -/
theorem exists_child_roots_of_card_ge
    {c : ℕ} (H : Fin 3 → Finset V)
    (hcard : ∀ k, c ≤ (H k).card) :
    ∃ childRoot : Fin 3 → Fin c → V,
      (∀ k, Function.Injective (childRoot k)) ∧
      (∀ k u, childRoot k u ∈ H k) := by
  classical
  have hex (k : Fin 3) :
      ∃ e : Fin c ↪ V, Set.range e ⊆ (H k : Set V) := by
    exact Function.Embedding.exists_of_card_le_finset (by simpa using hcard k)
  choose e he using hex
  refine ⟨fun k u => e k u, ?_, ?_⟩
  · intro k
    exact (e k).injective
  · intro k u
    exact he k ⟨u, rfl⟩

/-- The connectivity-based three-child theorem with target roots selected
from each child by cardinality. -/
theorem rooted_minor_of_three_woven_children_connected_of_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a c b κ : ℕ}
    (hapos : 0 < a) (hscale : 2 * a = 3 * c)
    (H : Fin 3 → Finset V)
    (hH : Pairwise fun k l : Fin 3 =>
      Disjoint (H k : Set V) (H l : Set V))
    (hW : ∀ k, Woven (G.induce (H k : Set V)) c b)
    (hcard : ∀ k, c ≤ (H k).card)
    (root : Fin a → V) (hroot : Function.Injective root)
    (start : Fin (2 * a) → V)
    (hstartinj : Function.Injective start)
    (hstartOutsideRoots : ∀ q i, start q ≠ root i)
    (hstartOutsideH : ∀ q k, start q ∉ H k)
    (hrootOutsideH : ∀ i k, root i ∉ H k)
    (hconn : VertexConnected G κ)
    (hκ : a + 16 * (2 * a) ≤ κ)
    (hbudget : 2 * a ≤ b)
    (hfirst : ∀ i, G.Adj (root i) (start (firstConnector i)))
    (hsecond : ∀ i, G.Adj (root i) (start (secondConnector i))) :
    HasRootedCliqueMinor G root := by
  obtain ⟨childRoot, hinj, hmem⟩ := exists_child_roots_of_card_ge H hcard
  exact rooted_minor_of_three_woven_children_connected G
    hapos hscale H hH hW root hroot childRoot hinj hmem
    start hstartinj hstartOutsideRoots hstartOutsideH
    hrootOutsideH hconn hκ hbudget hfirst hsecond

end Woven
end HadwigerLean
