import SupercriticalLQGUniqueness.B2.DG20Lim.CenteredAnnulusEscape
import SupercriticalLQGUniqueness.B2.DG20Lim.CompleteLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.EuclideanControlFromEscape

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.euclidean_control_of_pointwise_escape
    (R : RData)
    (hescape : ∀ u : ℂ, ∀ T : ℝ≥0∞, T ≠ ∞ →
      ∃ S : ℝ, ∀ v : ℂ, S ≤ dist v 0 → T ≤ R.DfromR u v)
    (u : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ v : ℂ,
      R.DfromR u v < ENNReal.ofReal η → dist u v < δ := by
  exact euclidean_control_of_lsc_pos_escape
    (fun p : ℂ × ℂ => R.DfromR p.1 p.2) R.lowerSemicontinuous_DfromR
    u (fun v hv => R.DfromR_pos (Ne.symm hv))
    (hescape u 1 ENNReal.one_ne_top) δ hδ

theorem RData.exists_limit_of_pointwise_escape
    (R : RData)
    (hescape : ∀ u : ℂ, ∀ T : ℝ≥0∞, T ≠ ∞ →
      ∃ S : ℝ, ∀ v : ℂ, S ≤ dist v 0 → T ≤ R.DfromR u v)
    (z : ℕ → ℂ)
    (hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, R.DfromR (z n) (z m) ≤ ε) :
    ∃ w : ℂ, Tendsto (fun n => R.DfromR (z n) w) atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := hc 1 (by norm_num)
  obtain ⟨S, hS⟩ := hescape (z N) 2 (by norm_num)
  have hzK : ∀ n, z (n + N) ∈ closedBall 0 S := by
    intro n
    apply mem_closedBall.mpr
    by_contra hnot
    have hfar : S ≤ dist (z (n + N)) 0 := le_of_lt (lt_of_not_ge hnot)
    have hlow : (2 : ℝ≥0∞) ≤ R.DfromR (z N) (z (n + N)) := hS _ hfar
    have hupp : R.DfromR (z N) (z (n + N)) ≤ 1 :=
      hN N le_rfl (n + N) (Nat.le_add_left N n)
    exact (by norm_num : ¬ (2 : ℝ≥0∞) ≤ 1) (hlow.trans hupp)
  have hcTail : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M,
        R.DfromR (z (n + N)) (z (m + N)) ≤ ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hc ε hε
    refine ⟨M, fun n hn m hm => hM _ (by omega) _ (by omega)⟩
  obtain ⟨w, _, hw⟩ := R.exists_DfromR_limit_of_compact_range
    (fun n => z (n + N)) (closedBall 0 S) (isCompact_closedBall 0 S)
    hzK hcTail
  exact ⟨w, (tendsto_add_atTop_iff_nat N).mp hw⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
