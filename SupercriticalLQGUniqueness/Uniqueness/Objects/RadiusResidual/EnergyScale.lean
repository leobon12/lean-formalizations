import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Family
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.ForwardTube
import LQGMetric.Papers.GM.S5.L510C7




 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual

 
theorem bumpTest_eq_dilT (P : Objects.Tube.TubeParams) (hP : P.Good)
    (r Amax : ℝ) (hr : 0 < r) (A : Set.Ioi (0 : ℝ))
    (hSmall : 100 * (A : ℝ) ≤ P.sp * P.ρ) :
    P.bumpTest r Amax A hP hr hSmall =
      LQGMetric.GM.dilT r (P.bumpTest 1 Amax A hP (by norm_num) hSmall) := by
  apply DFunLike.ext
  intro x
  rw [LQGMetric.GM.dilT_apply hr]
  change P.bump r Amax A x = P.bump 1 Amax A ((r⁻¹ : ℝ) • x)
  have hscale := P.bump_scale hr Amax A ((r⁻¹ : ℝ) • x)
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hscale
  exact hscale

 
theorem gradEnergy_bumpTest_eq_unit (P : Objects.Tube.TubeParams) (hP : P.Good)
    (r Amax : ℝ) (hr : 0 < r) (A : Set.Ioi (0 : ℝ))
    (hSmall : 100 * (A : ℝ) ≤ P.sp * P.ρ) :
    LQGMetric.gradEnergy (P.bumpTest r Amax A hP hr hSmall) =
      LQGMetric.gradEnergy (P.bumpTest 1 Amax A hP (by norm_num) hSmall) := by
  rw [bumpTest_eq_dilT P hP r Amax hr A hSmall,
    LQGMetric.GM.gradEnergy_dilT hr]

 

theorem gradEnergy_tubeDataOf_eq_unit (C : Objects.CorrectedEvent.Constants)
    (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ)
    (ρ₀ : ℝ) (X : Finset ℂ) :
    LQGMetric.gradEnergy (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X).bump =
      LQGMetric.gradEnergy
        (P.bumpTest 1 C.A_max ⟨C.A_sup, C.supPos⟩ hP (by norm_num) hSmall) := by
  exact gradEnergy_bumpTest_eq_unit P hP C.r C.A_max C.rPos
    ⟨C.A_sup, C.supPos⟩ hSmall

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
