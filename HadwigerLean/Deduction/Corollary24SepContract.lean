import HadwigerLean.Deduction.Corollary24Transport
import HadwigerLean.Woven.OuterContracts
import Mathlib.Tactic

/-!
# Corollary 24 chromatic separation contract
-/

namespace HadwigerLean.Deduction

private theorem cor24_sep_inside_minorfree
    {V : Type*} [Fintype V] [DecidableEq V]
    (N : SimpleGraph V) (T d a : ℕ)
    (hscale : Bootstrap.IsOuterScale T a)
    (hcut : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ))
    (hsepN : Bootstrap.OuterSeparation N T d)
    (hminor : ¬ HasCliqueMinor N (14 * a))
    (X : Finset V)
    (hχ : 2 * (14 * d * a) < chromatic (N.induce (X : Set V))) :
    Bootstrap.ChromaticSeparable
      (N.induce (X : Set V)) (14 * d * a) := by
  have hminorX : ¬ HasCliqueMinor (N.induce (X : Set V)) (14 * a) := by
    intro hminor'
    let e : N.induce (X : Set V) ↪g N := SimpleGraph.Embedding.induce _
    exact hminor (hasCliqueMinor_map e.toHom e.injective hminor')
  have hχlarge : 28 * d * a < chromatic (N.induce (X : Set V)) := by
    nlinarith [hχ]
  exact hsepN a hscale hcut (X : Set V) hminorX hχlarge

theorem cor24_sep_contract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T d a : ℕ)
    (hscale : Bootstrap.IsOuterScale T a)
    (hcut : (T : ℝ) / Real.sqrt (Real.log (T : ℝ)) < (a : ℝ))
    (hsep : Bootstrap.OuterSeparation G T d) :
    Woven.OuterSepContract G a (14 * d * a) := by
  classical
  intro j hj root P hminor X hχ
  let N := G.induce (Woven.normalizedSet root P)
  have hsepN : Bootstrap.OuterSeparation N T d :=
    outerSeparation_induce G T d hsep (Woven.normalizedSet root P)
  exact cor24_sep_inside_minorfree N T d a hscale hcut
    hsepN hminor X hχ

end HadwigerLean.Deduction