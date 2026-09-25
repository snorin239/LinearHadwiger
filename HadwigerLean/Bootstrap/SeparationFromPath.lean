import HadwigerLean.Bootstrap.Path
import HadwigerLean.Bootstrap.Separation
import HadwigerLean.Bootstrap.Palette
import HadwigerLean.Graph.MinorFree

/-! Deduce chromatic separation from induced-path localization and equation (5). -/

namespace HadwigerLean.Bootstrap

universe u

/-- Paper Lemma 14, conditional only on the path-localization statement for
the graph under consideration. -/
theorem chromatic_separable_of_path_localization
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u d k : ℕ) (hu : 0 < u) (hk : 2 ≤ k)
    (hlocal : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      ¬ HadwigerLean.HasCliqueMinor H u →
      Fintype.card W ≤ 2 * u * k ^ 2 →
      HadwigerLean.chromatic H ≤ d * u)
    (hminor : ¬ HadwigerLean.HasCliqueMinor G u)
    (hsmall : NoLargeConnectedBipartite G k)
    (hchi : d * u < HadwigerLean.chromatic G)
    (hpath : PathLocalizationStatement G k
      (HadwigerLean.chromatic G - d * u)) :
    ChromaticSeparable G (d * u) := by
  classical
  by_contra hsep
  let q := HadwigerLean.chromatic G - d * u
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hqchi : q ≤ HadwigerLean.chromatic G := Nat.sub_le _ _
  have hnosplit (A B : Set V) (hAB : Disjoint A B) :
      HadwigerLean.chromatic (G.induce A) < q ∨
        HadwigerLean.chromatic (G.induce B) < q := by
    by_contra h
    push_neg at h
    have hA : HadwigerLean.chromatic G ≤
        HadwigerLean.chromatic (G.induce A) + d * u := by
      dsimp [q] at h
      omega
    have hB : HadwigerLean.chromatic G ≤
        HadwigerLean.chromatic (G.induce B) + d * u := by
      dsimp [q] at h
      omega
    exact hsep ⟨A, B, hAB, hA, hB⟩
  obtain ⟨J, hαJ, hcomp⟩ :=
    hpath hk hq hsmall hqchi hnosplit
  have hJminor : ¬ HadwigerLean.HasCliqueMinor (G.induce J) u := by
    intro h
    let e : G.induce J ↪g G := SimpleGraph.Embedding.induce J
    exact hminor (HadwigerLean.hasCliqueMinor_map e.toHom e.injective h)
  have hind : HadwigerLean.independenceNumber (G.induce J) ≤ k ^ 2 := by
    calc
      HadwigerLean.independenceNumber (G.induce J) ≤ k * (k - 1) := hαJ
      _ ≤ k ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul_left k (Nat.sub_le k 1)
  have horder : Fintype.card J ≤ 2 * u * k ^ 2 :=
    (card_lt_two_u_k_sq (G.induce J) u k (by omega) hJminor hind).le
  have hJsmall := hlocal J (G.induce J) hJminor horder
  have hpal := chromatic_le_add_induce G J Jᶜ (Set.union_compl_self J)
  have : HadwigerLean.chromatic G ≤
      HadwigerLean.chromatic (G.induce J) +
        HadwigerLean.chromatic (G.induce Jᶜ) := hpal
  omega

end HadwigerLean.Bootstrap
