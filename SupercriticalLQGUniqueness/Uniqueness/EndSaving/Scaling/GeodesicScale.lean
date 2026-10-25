import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.RegularConstantScale
import LQGMetric.Metric.WeylScaling




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling

theorem setDist_rescale
    (D E : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal k * D (x, y))
    (K₁ K₂ : Set ℂ) :
    OptimalConstants.Ratios.setDist E K₁ K₂ = ENNReal.ofReal k * OptimalConstants.Ratios.setDist D K₁ K₂ := by
  have hk0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.mpr hk).ne'
  simp only [OptimalConstants.Ratios.setDist, hscale, ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]

theorem bumpedGeodesic_rescale
    (D E : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal k * D (x, y))
    (P : ℝ → ℂ) (T : ℝ) (hP : EndSaving.Interfaces.BumpedGeodesic D P T) :
    EndSaving.Interfaces.BumpedGeodesic E (P ∘ fun t => t / k) (k * T) := by
  rcases hP with ⟨hcurve, hu, hlen, hfin⟩
  have hT : 0 ≤ T := hcurve.1
  have hu' : HasUnitSpeedOn (E.pt ∘ (P ∘ fun t => t / k)) (Icc 0 (k * T)) := by
    apply LQGMetric.MetricGeometry.hasUnitSpeedOn_rescale hk
      (F := E.pt ∘ P) (G := D.pt ∘ P)
    · intro s t
      exact hscale (P s) (P t)
    · exact hu
  have hcurve' : E.IsCurve (P ∘ fun t => t / k) 0 (k * T) :=
    ⟨mul_nonneg hk.le hT,
      LQGMetric.MetricGeometry.continuousOn_of_hasUnitSpeedOn hu'⟩
  have hDtime : D.len P 0 T = ENNReal.ofReal T := by
    simpa only [LSCMetric.len_eq_curveLength, sub_zero] using
      (LQGMetric.MetricGeometry.hasUnitSpeedOn_Icc_iff.mp hu)
        0 T (le_refl _) hT (le_refl _)
  have hEtime : E.len (P ∘ fun t => t / k) 0 (k * T) =
      ENNReal.ofReal (k * T) := by
    simpa only [LSCMetric.len_eq_curveLength, sub_zero] using
      (LQGMetric.MetricGeometry.hasUnitSpeedOn_Icc_iff.mp hu')
        0 (k * T) (le_refl _) (mul_nonneg hk.le hT) (le_refl _)
  have hends : (P ∘ fun t => t / k) 0 = P 0 ∧
      (P ∘ fun t => t / k) (k * T) = P T := by
    constructor
    · simp
    · simp [hk.ne']
  refine ⟨hcurve', hu', ?_, ?_⟩
  · rw [hEtime, hends.1, hends.2, hscale, ← hlen, hDtime]
    exact ENNReal.ofReal_mul hk.le
  · rw [hends.1, hends.2, hscale]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hfin

theorem setGeodesic_rescale
    (D E : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal k * D (x, y))
    (K₁ K₂ : Set ℂ) (P : ℝ → ℂ) (T : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T) :
    EndSaving.FiniteEvents.SetGeodesic E K₁ K₂ (P ∘ fun t => t / k) (k * T) := by
  rcases hP with ⟨hgeo, hstart, hend, hdist⟩
  have hends : (P ∘ fun t => t / k) 0 = P 0 ∧
      (P ∘ fun t => t / k) (k * T) = P T := by
    constructor
    · simp
    · simp [hk.ne']
  refine ⟨bumpedGeodesic_rescale D E k hk hscale P T hgeo,
    hends.1 ▸ hstart, hends.2 ▸ hend, ?_⟩
  rw [setDist_rescale D E k hk hscale, ← hdist]
  exact ENNReal.ofReal_mul hk.le

theorem uniqueSetGeodesic_rescale
    (D E : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal k * D (x, y))
    (K₁ K₂ : Set ℂ) (P : ℝ → ℂ) (T : ℝ)
    (hP : EndSaving.FiniteEvents.UniqueSetGeodesic D K₁ K₂ P T) :
    EndSaving.FiniteEvents.UniqueSetGeodesic E K₁ K₂
      (P ∘ fun t => t / k) (k * T) := by
  have hkinv : 0 < 1 / k := one_div_pos.mpr hk
  have hInv : ∀ x y : ℂ,
      D (x, y) = ENNReal.ofReal (1 / k) * E (x, y) := by
    intro x y
    rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul hkinv.le]
    have hmul : (1 / k) * k = 1 := by field_simp
    simp only [hmul, ENNReal.ofReal_one, one_mul]
  refine ⟨setGeodesic_rescale D E k hk hscale K₁ K₂ P T hP.1, ?_⟩
  intro P' T' hP'
  have hback := setGeodesic_rescale E D (1 / k) hkinv hInv
    K₁ K₂ P' T' hP'
  obtain ⟨hT, hEq⟩ := hP.2 _ _ hback
  have hT' : T' = k * T := by
    calc T' = k * ((1 / k) * T') := by field_simp
      _ = k * T := congrArg (k * ·) hT
  refine ⟨hT', ?_⟩
  intro t ht
  have hs : t / k ∈ Icc 0 T := by
    constructor
    · exact div_nonneg ht.1 hk.le
    · apply (div_le_iff₀ hk).2
      simpa only [mul_comm] using ht.2
  have heq := hEq hs
  have harg : (t / k) / (1 / k) = t := by field_simp
  simpa only [Function.comp_def, harg] using heq

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
