import HadwigerLean.Graph.Linkedness.PairPadding
import HadwigerLean.Graph.Linkedness.LinkageAvoid
import Mathlib.Tactic

/-!
# Upgrading k-linkedness to rooted linkedness by terminal padding
-/

namespace HadwigerLean
namespace Linkedness

/-- If the graph has room for `2k` distinct terminals, ordinary
`k`-linkedness links every pairing inside any root set of at most `2k`
vertices while avoiding all unused roots. -/
theorem rootedLinked_of_kLinked_and_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hlinked : KLinked G k)
    (horder : 2 * k ≤ Fintype.card V)
    (Y : Finset V) (hY : Y.card ≤ 2 * k) :
    RootedLinked G Y := by
  classical
  by_cases hk : k = 0
  · have hsmall : Y.card ≤ 1 := by omega
    exact rootedLinked_of_card_le_one G Y hsmall
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  intro n Q hQ hne hQY
  obtain ⟨hn, P, hP, hPne, hstart, hfinish, hcover⟩ :=
    exists_padded_pairs k n hkpos Q hQ hne Y hQY hY horder
  obtain ⟨L⟩ := hlinked P hP hPne
  let e : Fin n ↪ Fin k := Fin.castLEEmb hn
  let q (i : Fin n) : G.Path (Q.start i) (Q.finish i) :=
    ⟨(L.path (e i) : G.Walk (P.start (e i)) (P.finish (e i))).copy
        (hstart i) (hfinish i),
      by simpa using (L.path (e i)).property⟩
  have hsupport (i : Fin n) :
      pathVertexSet (q i) = pathVertexSet (L.path (e i)) := by
    ext v
    simp [q, pathVertexSet, SimpleGraph.Walk.support_copy]
  let L' : IndexedLinkage G Q := {
    path := q
    disjoint := by
      intro i j hij
      rw [hsupport i, hsupport j]
      exact L.disjoint (e.injective.ne hij)
  }
  have havoid : InteriorsAvoid L Y :=
    IndexedLinkage.interiorsAvoid_terminal_cover L Y hcover
  refine ⟨L', ?_⟩
  intro i v hv hvY
  have hv' : v ∈ pathVertexSet (L.path (e i)) := by
    rw [← hsupport i]
    exact hv
  have hterm := havoid (e i) v hv' hvY
  rcases hterm with hs | ht
  · exact Or.inl (hs.trans (hstart i))
  · exact Or.inr (ht.trans (hfinish i))

end Linkedness
end HadwigerLean
