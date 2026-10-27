import MatedCRTHarmonic.GMS4cO.Rescale
import MatedCRTHarmonic.GMSCase.Defs
import MatedCRTHarmonic.GMS4b.Window
import MatedCRTHarmonic.GMS4cS.AffineAreaCertificate
import MatedCRTHarmonic.LQGCoord.Main

/-! The zero-cone GMC area under Lemma 4.9 recentering. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTPort MatedCRTHarmonic.L43O
open LQGMetric

theorem exp_affineArea_coeff (γ a r : ℝ) (hr : 0 < r) :
    Real.exp (γ * (-(a) - CellScaling.lqgQ γ * Real.log r)) =
      (timeScale γ a r)⁻¹ := by
  rw [timeScale, Real.rpow_def_of_pos hr, mul_inv_rev]
  rw [← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem ae_affine_qAreaC_zeroCone
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ), 0 < r → ∀ (z : ℂ) (A : Set ℂ),
      qAreaC γ (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)) A =
        ENNReal.ofReal (timeScale γ
          (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)⁻¹ *
          qAreaC γ (zeroConeField γ X₀ B₀ B₀' ω)
            ((fun w => (r : ℂ) * w + z) '' A) := by
  have hQ : (0 : ℝ) < CellScaling.lqgQ γ :=
    lt_trans hγ.1 (LQGCoord.lt_lqgQ hγ.1 hγ.2)
  filter_upwards [LQGCoord.ae_lqgArea_affine_coneField_holds
    hγ.1 hγ.2 hQ D.gff₀ D.bm_B₀ D.bm_B₀'] with ω hω
  intro r hr z A
  let h : MatedCRT.Field := zeroConeField γ X₀ B₀ B₀' ω
  let a : ℝ := circleAvg h r z
  have hf : IGLaw.affField r 0 z h =
      addConst (affineComp r z h) (-a) := by
    rw [IGLaw.affField, L43O.rotateField_zero]
  have hadd : CellScaling.lqgQ γ * Real.log r + (-a - CellScaling.lqgQ γ * Real.log r) =
      -a := by ring
  have hcov := hω r hr (-a - CellScaling.lqgQ γ * Real.log r) z A
  rw [hadd] at hcov
  change CellScaling.lqgArea γ (addConst (affineComp r z h) (-a)) A =
    ENNReal.ofReal (Real.exp (γ * (-a - CellScaling.lqgQ γ * Real.log r))) *
      CellScaling.lqgArea γ h ((fun w => (r : ℂ) * w + z) '' A) at hcov
  rw [← hf, exp_affineArea_coeff γ a r hr,
    LQGCone.lqgArea_eq_qAreaC, LQGCone.lqgArea_eq_qAreaC] at hcov
  exact hcov

end MatedCRTHarmonic.GMS4cS

