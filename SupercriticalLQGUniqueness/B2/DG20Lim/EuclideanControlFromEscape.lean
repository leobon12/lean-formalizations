import SupercriticalLQGUniqueness.B2.DG20Lim.CompleteLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.Positivity

 


set_option autoImplicit false
noncomputable section

open Set Metric Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem euclidean_control_of_lsc_pos_escape
    (d : ℂ × ℂ → ℝ≥0∞) (hd : LowerSemicontinuous d)
    (u : ℂ) (hpos : ∀ v, v ≠ u → 0 < d (u, v))
    (hesc : ∃ R : ℝ, ∀ v, R ≤ dist v 0 → (1 : ℝ≥0∞) ≤ d (u, v))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ v, d (u, v) < ENNReal.ofReal η → dist u v < δ := by
  obtain ⟨R, hR⟩ := hesc
  let K : Set ℂ := closedBall 0 R \ ball u δ
  have hK : IsCompact K := (isCompact_closedBall 0 R).diff isOpen_ball
  have hd_u : LowerSemicontinuous (fun v => d (u, v)) := by
    have hc : Continuous (fun v : ℂ => (u, v)) := continuous_const.prodMk continuous_id
    exact hd.comp hc
  by_cases hne : K.Nonempty
  · obtain ⟨w, hw, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK (hd_u.lowerSemicontinuousOn K)
    have hwu : w ≠ u := by
      intro heq
      subst w
      exact hw.2 (mem_ball.mpr (by simpa using hδ))
    have hwp : 0 < d (u, w) := hpos w hwu
    obtain ⟨η, hη, hηw⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η < d (u, w) := by
      by_cases htop : d (u, w) = ∞
      · exact ⟨1, by norm_num, by simp [htop]⟩
      · have ht : 0 < (d (u, w)).toReal := ENNReal.toReal_pos hwp.ne' htop
        refine ⟨(d (u, w)).toReal / 2, by positivity, ?_⟩
        exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop).2 (by linarith)
    refine ⟨min η 1, lt_min hη (by norm_num), ?_⟩
    intro v hv
    by_contra hnot
    have hvδ : δ ≤ dist u v := le_of_not_gt hnot
    by_cases hvR : R ≤ dist v 0
    · have hle : (1 : ℝ≥0∞) ≤ d (u, v) := hR v hvR
      have hlt : d (u, v) < 1 := lt_of_lt_of_le hv (by simpa using (ENNReal.ofReal_le_ofReal (min_le_right η (1 : ℝ))))
      exact (not_lt_of_ge hle) hlt
    · have hvK : v ∈ K := ⟨mem_closedBall.mpr (le_of_not_ge hvR), by
        simpa only [mem_ball, dist_comm] using (not_lt_of_ge hvδ)⟩
      have hminv : d (u, w) ≤ d (u, v) := hmin hvK
      have hlt : d (u, v) < ENNReal.ofReal η :=
        lt_of_lt_of_le hv (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      exact (not_lt_of_ge hηw.le) (lt_of_le_of_lt hminv hlt)
  · refine ⟨1, by norm_num, ?_⟩
    intro v hv
    by_contra hnot
    have hvδ : δ ≤ dist u v := le_of_not_gt hnot
    by_cases hvR : R ≤ dist v 0
    · exact (not_lt_of_ge (hR v hvR)) (by simpa using hv)
    · exact hne ⟨v, mem_closedBall.mpr (le_of_not_ge hvR), by
        simpa only [mem_ball, dist_comm] using (not_lt_of_ge hvδ)⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
