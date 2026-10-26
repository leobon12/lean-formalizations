import SupercriticalConformalCovariance.Rotation.Norm
import SupercriticalLQGUniqueness.B2.WeakStrong.Field

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Rotation

/-- Complex-affine covariance of every strong LQG metric, with the field represented as
`rotDist (a/|a|) (affineComp |a| b h) + Q log |a|`. -/
theorem ae_complex_affine_covariance
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (h ω)).1 (a * u + b, a * v + b) =
        (D (addConst
          (GaussianLQG.rotDist (a / (‖a‖ : ℂ))
            (affineComp ‖a‖ b (h ω)))
          (Q * Real.log ‖a‖))).1 (u, v) := by
  let r : Set.Ioi (0 : ℝ) := ⟨‖a‖, norm_pos_iff.mpr ha⟩
  let β : ℂ := a / (‖a‖ : ℂ)
  have hβ : ‖β‖ = 1 := GaussianLQG.norm_div_norm_eq_one ha
  have hab : (‖a‖ : ℂ) * β = a := GaussianLQG.norm_mul_div_norm ha
  let g : Ω → DistC := fun ω =>
    addConst (affineComp ‖a‖ b (h ω)) (Q * Real.log ‖a‖)
  have hg : IsGFFPlusCont g P :=
    Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
      (LQGMetric.GM.isGFFPlusCont_affineComp hh r.2 b) measurable_const
  filter_upwards [hD.2.2.2.2.1 P h hh r b,
    ae_rotation_covariance ξ Q hQ D hD β hβ P g hg] with ω hc hrot u v
  have e (x : ℂ) : a * x + b = (r : ℝ) • (β * x) + b := by
    change a * x + b = (‖a‖ : ℂ) * (β * x) + b
    rw [← mul_assoc, hab]
  calc
    (D (h ω)).1 (a * u + b, a * v + b) =
        (D (addConst (scaleTranslateDist r b (h ω)) (Q * Real.log (r : ℝ)))).1
          (β * u, β * v) := by rw [e u, e v, hc]
    _ = (D (g ω)).1 (β * u, β * v) := by
      simp only [g, B2.Strong.scaleTranslateDist_eq_affineComp]
      rfl
    _ = (D (GaussianLQG.rotDist β (g ω))).1 (u, v) := hrot u v
    _ = _ := by simp only [g, rotDist_addConst hβ]; rfl


end SupercriticalConformalCovariance.Rotation
