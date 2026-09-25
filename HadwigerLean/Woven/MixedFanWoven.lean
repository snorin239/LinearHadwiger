import HadwigerLean.Woven.HubMatching

import HadwigerLean.Woven.MixedFanTrim

/-!
# Proxy woven solution from the mixed fan

This combines the paired-source mixed Menger linkage with the linked hub
and an arbitrary rooted clique model in the residual graph.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {a j : ℕ}
  {Z U H : Finset V}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- Proxy root vertices indexed by the root roles. -/
def hubProxyRoots (proxy : HubProxyRole a j ≃ Z) : Fin a → V :=
  fun i => (proxy (Sum.inl i)).1

/-- Proxy terminal pairs indexed by the terminal roles. -/
def hubProxyPairs (proxy : HubProxyRole a j ≃ Z) :
    IndexedPairs (Fin j) V where
  start := fun k => (proxy (Sum.inr (k,0))).1
  finish := fun k => (proxy (Sum.inr (k,1))).1

/-- The mixed fan, a linked hub, and a rooted model for every `a`
residual vertices give a proxy `(a,j)` woven solution. -/
theorem exists_proxy_woven_of_mixed_fan
    (F : DoubleFan G Z H) (C : IndexedLinkage G P)
    (hU : ∀ slot, P.start slot ∈ U)
    (hfinish : ∀ slot, P.finish slot ∈ H)
    (havoidZ : ∀ slot v, v ∈ pathVertexSet (C.path slot) → v ∉ Z)
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hZU : Disjoint Z U) (hHU : Disjoint H U)
    (hZH : Disjoint Z H)
    (proxy : HubProxyRole a j ≃ Z)
    (hresidual : ∀ (r : Fin a → V), Function.Injective r →
      (∀ i, r i ∈ U) →
      ∃ M : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G r,
        ∀ i, M.branch i ⊆ (U : Set V))
    (hlinked : Linkedness.KLinked (G.induce (H : Set V)) (a+j))
    (horder : 2 * (a+j) ≤ Fintype.card (↥(H : Set V))) :
    Nonempty (WovenSolution G (hubProxyRoots proxy)
      (hubProxyPairs proxy)) := by
  obtain ⟨R,N,hproxy,hpair,hAB,hclean⟩ :=
    exists_mixed_linkage_clean_of_untrimmed F C hU hfinish
      havoidZ hfanU hZU hHU
  let r : Fin a → V := fun i => R.start (.inr i)
  have hrinj : Function.Injective r := by
    intro i k h
    exact Sum.inr_injective (N.start_injective h)
  have hrU : ∀ i, r i ∈ U := by
    intro i
    obtain ⟨b,hUb,_⟩ := hpair i
    exact hUb
  obtain ⟨M,hMsubset⟩ := hresidual r hrinj hrU
  let slot := hubRoleMatching proxy
  let rootSlot := hubRootSlot a j
  let terminalSlot := hubTerminalSlot a j
  have hfinishH : ∀ x, R.finish x ∈ H := hAB.2
  have hNhub : ∀ x v, v ∈ pathVertexSet (N.path x) →
      v ∈ H → v = R.finish x := by
    intro x v hv hvH
    have hvbig : v ∈ Z ∪ U ∪ H := Finset.mem_union_right _ hvH
    rcases hclean x v hv hvbig with hs | ht
    · have hsZU : R.start x ∈ Z ∪ U := hAB.1 x
      rcases Finset.mem_union.mp hsZU with hz | hu
      · exact False.elim ((Finset.disjoint_left.mp hZH)
          hz (hs ▸ hvH))
      · exact False.elim ((Finset.disjoint_left.mp hHU)
          (hs ▸ hvH) hu)
    · exact ht
  have hNU : ∀ x v, v ∈ pathVertexSet (N.path x) →
      v ∈ U → v = R.start x ∨ v = R.finish x := by
    intro x v hv hvU
    exact hclean x v hv (by simp [hvU])
  have hfirstOutside : ∀ k,
      R.start (slot (k,0)) ∉ U := by
    intro k
    obtain ⟨z,hz⟩ := hubRoleMatching_first_proxy proxy k
    rw [hz, hproxy z]
    exact Finset.disjoint_left.mp hZU z.2
  have hterminalSecondOutside : ∀ k : Fin j,
      R.start (slot (terminalSlot k,1)) ∉ U := by
    intro k
    rw [show slot (terminalSlot k,1) =
      Sum.inl (proxy (Sum.inr (k,1))) from
        hubRoleMatching_terminal proxy k 1,
      hproxy (proxy (Sum.inr (k,1)))]
    exact Finset.disjoint_left.mp hZU (proxy (Sum.inr (k,1))).2
  have hrootEq :
      ((hubSplicedPairs R slot).finish ∘ rootSlot) = r := by
    funext i
    simp [hubSplicedPairs, slot, rootSlot, r]
  let M' : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G
      ((hubSplicedPairs R slot).finish ∘ rootSlot) :=
    hrootEq.symm ▸ M
  have hMsubset' : ∀ i, M'.branch i ⊆ (U : Set V) := by
    have transport {r₁ r₂ : Fin a → V} (heq : r₁ = r₂)
        (T : RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G r₁)
        (hT : ∀ i, T.branch i ⊆ (U : Set V)) :
        ∀ i, (heq ▸ T).branch i ⊆ (U : Set V) := by
      cases heq
      exact hT
    exact transport hrootEq.symm M hMsubset
  have hsol := exists_woven_solution_of_hub_splice G H U R N slot
    rootSlot terminalSlot (hubRootSlot_ne_hubTerminalSlot a j)
    M' hMsubset' hfinishH hNhub hNU hfirstOutside
    hterminalSecondOutside hHU.symm hlinked horder
  have hroots :
      ((hubSplicedPairs R slot).start ∘ rootSlot) =
        hubProxyRoots proxy := by
    funext i
    simp [hubSplicedPairs, slot, rootSlot, hubProxyRoots, hproxy]
  have hpairs :
      (hubSplicedPairs R slot).reindex terminalSlot =
        hubProxyPairs proxy := by
    have hs : ((hubSplicedPairs R slot).reindex terminalSlot).start =
        (hubProxyPairs proxy).start := by
      funext k
      simp [IndexedPairs.reindex, hubSplicedPairs,
        terminalSlot, slot, hubProxyPairs, hproxy]
    have ht : ((hubSplicedPairs R slot).reindex terminalSlot).finish =
        (hubProxyPairs proxy).finish := by
      funext k
      simp [IndexedPairs.reindex, hubSplicedPairs,
        terminalSlot, slot, hubProxyPairs, hproxy]
    cases e₁ : (hubSplicedPairs R slot).reindex terminalSlot with
    | mk s t =>
        cases e₂ : hubProxyPairs proxy with
        | mk s' t' =>
            have hs' : s = s' := by simpa [e₁, e₂] using hs
            have ht' : t = t' := by simpa [e₁, e₂] using ht
            cases hs'
            cases ht'
            rfl
  simpa [hroots, hpairs] using hsol

end Woven
end HadwigerLean
