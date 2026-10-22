import HigherDimLQGMetric.Routing.Collector
import HigherDimLQGMetric.Metric.Partition

/-!
# Trimming a routing witness arc

The middle of a rectifiable witness arc retains a strict shortcut ratio after sufficiently
small pieces are removed from its ends. The cut times are chosen by endpoint continuity.
-/

set_option autoImplicit false

open Set LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

/-- The quantitative marked-arc step in Lemma 4.1′. -/
theorem lemma41_trim {X : Type*} [MetricSpace X] (E : X → X → ℝ≥0∞)
    (γ : ℝ → X) (hγ : ContinuousOn γ (Icc 0 1))
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : a₁ ≤ dist (γ 0) (γ 1))
    (hE : curveLengthWith E γ 0 1 ≤ ENNReal.ofReal (c₂ * dist (γ 0) (γ 1))) :
    ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 1 ∧
      a₁ / 2 < dist (γ s) (γ t) ∧
      curveLengthWith E γ s t < ENNReal.ofReal (c₃ * dist (γ s) (γ t)) := by
  have hc₃ : 0 < c₃ := lt_of_le_of_lt hc₂ hc₂₃
  let ε : ℝ := min (a₁ / 8) ((c₃ - c₂) * a₁ / (8 * c₃))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hε₁ : ε ≤ a₁ / 8 := min_le_left _ _
  have hε₂ : ε ≤ (c₃ - c₂) * a₁ / (8 * c₃) := min_le_right _ _
  obtain ⟨δ₀, hδ₀, hδ₀γ⟩ := (Metric.continuousOn_iff.mp hγ) 0
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) ε hε
  obtain ⟨δ₁, hδ₁, hδ₁γ⟩ := (Metric.continuousOn_iff.mp hγ) 1
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) ε hε
  let s : ℝ := min (δ₀ / 2) (1 / 4)
  let t : ℝ := 1 - min (δ₁ / 2) (1 / 4)
  have hs₀ : 0 < s := lt_min (by positivity) (by norm_num)
  have hs₁ : s ≤ 1 / 4 := min_le_right _ _
  have ht₁ : t < 1 := by
    dsimp [t]
    have h : 0 < min (δ₁ / 2) (1 / 4 : ℝ) := lt_min (by positivity) (by norm_num)
    linarith
  have ht₀ : 3 / 4 ≤ t := by dsimp [t]; have := min_le_right (δ₁ / 2) (1 / 4 : ℝ); linarith
  have hst : s < t := by linarith
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs₀.le, by linarith⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht₁.le⟩
  have hds : dist (γ s) (γ 0) < ε := by
    apply hδ₀γ s hs
    have hsd : s ≤ δ₀ / 2 := min_le_left _ _
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs₀.le] using
      (show |s| < δ₀ by rw [abs_of_nonneg hs₀.le]; linarith)
  have hdt : dist (γ t) (γ 1) < ε := by
    apply hδ₁γ t ht
    have htd : 1 - t ≤ δ₁ / 2 := by dsimp [t]; linarith [min_le_left (δ₁ / 2) (1 / 4 : ℝ)]
    simp only [Real.dist_eq]
    rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    linarith
  have htrim : dist (γ 0) (γ 1) < dist (γ s) (γ t) + 2 * ε := by
    have htri₁ := dist_triangle (γ 0) (γ s) (γ 1)
    have htri₂ := dist_triangle (γ s) (γ t) (γ 1)
    rw [dist_comm (γ 0) (γ s)] at htri₁
    linarith
  have hsep' : a₁ / 2 < dist (γ s) (γ t) := by linarith
  have hratio : c₂ * dist (γ 0) (γ 1) < c₃ * dist (γ s) (γ t) := by
    have hgap : 2 * c₃ * ε < (c₃ - c₂) * a₁ := by
      have h := mul_le_mul_of_nonneg_left hε₂ hc₃.le
      have hnon : 0 < (c₃ - c₂) * a₁ := mul_pos (sub_pos.mpr hc₂₃) ha₁
      field_simp at h
      nlinarith
    have hdist : 0 ≤ dist (γ 0) (γ 1) := dist_nonneg
    have hstep := mul_lt_mul_of_pos_left htrim hc₃
    have hgap' := mul_le_mul_of_nonneg_left hsep (sub_nonneg.mpr hc₂₃.le)
    nlinarith
  refine ⟨s, t, hs₀, hst, ht₁, hsep', ?_⟩
  calc
    curveLengthWith E γ s t ≤ curveLengthWith E γ 0 1 :=
      curveLengthWith_mono_interval hs.1 hst.le ht.2
    _ ≤ ENNReal.ofReal (c₂ * dist (γ 0) (γ 1)) := hE
    _ < ENNReal.ofReal (c₃ * dist (γ s) (γ t)) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc₃ (by linarith : 0 < dist (γ s) (γ t)))).2 hratio

end HigherDimLQGMetric
