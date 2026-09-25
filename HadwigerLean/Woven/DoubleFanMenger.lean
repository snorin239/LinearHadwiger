import HadwigerLean.Woven.DoubleFanSeparator

/-!
# Two disjoint clone-to-hub paths per source
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite Menger on the double-clone graph produces a full
family of 2|Z| mutually vertex-disjoint clone-to-hub paths. -/
theorem exists_double_clone_linkage
    (G : SimpleGraph V) (Z H : Finset V) (r : ℕ)
    (hconn : VertexConnected G r)
    (hr : 3 * Z.card ≤ r)
    (hH : 2 * Z.card ≤ H.card)
    (hdis : Disjoint Z H) :
    ∃ (P : IndexedPairs (Fin (2 * Z.card))
        (DoubleCloneVertex V Z))
      (L : IndexedLinkage (doubleCloneGraph G Z) P),
      SetMenger.IsABLinkage L
        (doubleCloneSources Z) (doubleCloneTargets Z H hdis) := by
  classical
  apply SetMenger.exists_linkage_of_separator_lower_bound
    (doubleCloneGraph G Z)
    (doubleCloneSources Z) (doubleCloneTargets Z H hdis)
    (2 * Z.card)
  intro Q hQ
  exact doubleClone_separator_card_ge G Z H r hconn hr hH hdis Q hQ

end Woven
end HadwigerLean
