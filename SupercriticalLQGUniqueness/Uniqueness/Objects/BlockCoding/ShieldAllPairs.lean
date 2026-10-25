import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldPathConvert




 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

 

theorem shield_all_pairs (D : LSCMetric) (z : ℂ) (t : ℝ)
    (ht : 0 < t) (W : Set ℂ) (hW : ball z (3 * t) ⊆ W)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (hcheap : Objects.CorrectedEvent.around D z t (2 * t) < Objects.CorrectedEvent.acr D z (2 * t) (3 * t))
    {x y : ℂ} (hx : x ∈ closedBall z t) (hy : y ∈ closedBall z t) :
    D.internal W
      (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
       ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩) =
      D (x, y) := by
  let p : W × W :=
    (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
     ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩)
  change D.internal W p = D (x, y)
  apply le_antisymm
  · rw [D.isLengthSpace_iff_eq_iInf.mp hL x y]
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun ha => le_iInf fun hb => ?_
    by_cases hfin : D.len P a b < ⊤
    · obtain ⟨γ, hγ, hlen⟩ := exists_euclidean_path_of_finite_curve D hB hL P a b hP
      have hγfin : D.len γ.extend 0 1 < ⊤ := hlen ▸ hfin
      have hγx : P a = x := ha
      have hγy : P b = y := hb
      subst x
      subst y
      change D.internal W p ≤ D.len P a b
      by_cases hfar : ∃ s ∈ Icc (0 : ℝ) 1, 3 * t ≤ dist (γ.extend s) z
      · obtain ⟨s, hs, hsfar⟩ := hfar
        exact (internal_lt_len_of_far_path D z t ht W hW hcheap hx hy γ hγ
          hγfin hs hsfar).le.trans_eq hlen
      · have hγW : ∀ s ∈ Icc (0 : ℝ) 1, γ.extend s ∈ W := by
          intro s hs
          apply hW
          rw [mem_ball]
          exact lt_of_not_ge (fun h => hfar ⟨s, hs, h⟩)
        simpa only [γ.extend_zero, γ.extend_one] using
          (internal_le_len_curve D W γ.extend 0 1 hγ hγW).trans_eq hlen
    · exact le_trans le_top (le_of_not_gt hfin)
  · exact D.edist_le_internal W p

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
