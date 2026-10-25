import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsGeometry0
import SupercriticalLQGUniqueness.B2.LscTop.Dilate
import SupercriticalLQGUniqueness.B2.PfeWeyl.WeightedPathChain

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem continuous_euclidForget_smul_dilate_of_control
    (D : LSCMetric)
    (hD : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, D (u,v) < ENNReal.ofReal η → dist u v < δ)
    (a r : Ioi (0 : ℝ)) :
    Continuous (B2.PfeWeyl.euclidForget
      (B2.LscTop.smulMetric a (B2.LscTop.dilate r D))) := by
  apply B2.PfeLocal.continuous_euclidForget_of_small_metric
  intro u δ hδ
  obtain ⟨η, hη, hclose⟩ := hD ((r : ℝ) • u) ((r : ℝ) * δ)
    (mul_pos r.property hδ)
  refine ⟨(a : ℝ) * η, mul_pos a.property hη, ?_⟩
  intro v hv
  have hv' : D ((r : ℝ) • u, (r : ℝ) • v) < ENNReal.ofReal η := by
    rw [B2.LscTop.smulMetric_apply, B2.LscTop.dilate_apply,
      ENNReal.ofReal_mul (le_of_lt a.property)] at hv
    by_contra hn
    have hge : ENNReal.ofReal η ≤ D ((r : ℝ) • u, (r : ℝ) • v) :=
      le_of_not_gt hn
    have hmul : ENNReal.ofReal a * ENNReal.ofReal η ≤
        ENNReal.ofReal a * D ((r : ℝ) • u, (r : ℝ) • v) := by
      simpa only [mul_comm] using
        (mul_le_mul_left hge (ENNReal.ofReal a))
    exact (not_lt_of_ge hmul) hv
  have hscaled := hclose ((r : ℝ) • v) hv'
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos r.property] at hscaled
  exact lt_of_mul_lt_mul_left hscaled r.property.le

end SupercriticalLQGUniqueness.B2.PfeAxioms
