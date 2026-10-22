import HigherDimLQGMetric.Thm13.TightBounded
import HigherDimLQGMetric.Sec10.LocalCase

/-! Weyl scaling after metric and field normalization at a fixed radius. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_normalizedAtScale_weyl
    {d : ℕ} (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (g : DistRd d) (f : C(Rd d, ℝ))
    (hD : (D g).IsLength)
    (hW : D (addFun g f) = weylMetric ξ f (D g) hD)
    {r : ℝ} (hr : 0 < r) (hc : 0 < c r)
    (hs : sphereAvg (addFun g f) r 0 =
      sphereAvg g r 0 + sphereAvg (ofCont f) r 0)
    (u v : Rd d) :
    ENNReal.ofReal (normalizedAtScale ξ D c (addFun g f) r (u, v)) =
      weylScale ξ (s8a_scaledWeight f r)
        ⟨normalizedAtScale ξ D c g r,
          s8a_normalizedAtScale_isContinuousMetric ξ D c g hr hc⟩ u v := by
  let a : ℝ := (c r)⁻¹ * Real.exp (-ξ * sphereAvg g r 0)
  let b : ℝ := sphereAvg (ofCont f) r 0
  let a' : ℝ := (c r)⁻¹ * Real.exp (-ξ * sphereAvg (addFun g f) r 0)
  have ha : 0 < a := mul_pos (inv_pos.mpr hc) (Real.exp_pos _)
  have ha' : 0 < a' := mul_pos (inv_pos.mpr hc) (Real.exp_pos _)
  let A : ContMetric d := ((D g).affine r hr.ne' 0).smul a ha
  have hA : A.1 = normalizedAtScale ξ D c g r := by
    ext p
    simp only [A, a, ContMetric.smul_apply, ContMetric.affine_apply,
      normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, smul_eq_mul, add_zero]
  have hfactor : Real.exp (ξ * -b) * a = a' := by
    dsimp only [a, a', b]
    rw [hs]
    calc
      Real.exp (ξ * -sphereAvg (ofCont f) r 0) *
          ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r 0)) =
          (c r)⁻¹ * (Real.exp (-ξ * sphereAvg g r 0) *
            Real.exp (ξ * -sphereAvg (ofCont f) r 0)) := by ring_nf
      _ = (c r)⁻¹ * Real.exp
          (-ξ * sphereAvg g r 0 + ξ * -sphereAvg (ofCont f) r 0) := by
            rw [Real.exp_add]
      _ = (c r)⁻¹ * Real.exp
          (-ξ * (sphereAvg g r 0 + sphereAvg (ofCont f) r 0)) := by
            congr 1
            ring_nf
  have hweight : s8a_scaledWeight f r =
      f.comp (ContMetric.affineMap r 0) +
        ContinuousMap.const (Rd d) (-b) := by
    ext x
    simp only [s8a_scaledWeight, ContinuousMap.sub_apply,
      ContinuousMap.add_apply, ContinuousMap.comp_apply,
      ContinuousMap.const_apply, ContMetric.affineMap_apply,
      affinePt, ContinuousMap.coe_mk, b]
    ring_nf
  let E : ContMetric d :=
    ⟨normalizedAtScale ξ D c g r,
      s8a_normalizedAtScale_isContinuousMetric ξ D c g hr hc⟩
  have hAE : A = E := Subtype.ext hA
  change ENNReal.ofReal (normalizedAtScale ξ D c (addFun g f) r (u, v)) =
    weylScale ξ (s8a_scaledWeight f r) E u v
  rw [← hAE]
  have hw : weylScale ξ (s8a_scaledWeight f r) A u v =
      ENNReal.ofReal a' * weylScale ξ f (D g) (r • u) (r • v) := by
    rw [hweight, weylScale_add_const, weylScale_smul,
      weylScale_affine hr.ne' 0, ContMetric.affineMap_apply]
    simp only [ContMetric.affineMap_apply, add_zero]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hfactor]
  rw [hw]
  simp only [normalizedAtScale, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul]
  rw [hW]
  rw [ENNReal.ofReal_mul ha'.le]
  congr 1
  exact weylMetric_spec hD (r • u) (r • v)

end HigherDimLQGMetric
