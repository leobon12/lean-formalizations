import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldWeylCost
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Marg




 






set_option autoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

def shieldOuterShape : EuclideanAnnulus :=
  ⟨(0, (2 : ℝ), 3), by norm_num, by norm_num⟩

theorem shieldOuterShape_at (R : Ioi (0 : ℝ)) (w : ℂ) :
    Positivity.Witnesses.annulusTranslate (shieldOuterShape.dilate R R.2) w =
      (⟨(w, 2 * (R : ℝ), 3 * (R : ℝ)),
        by change 0 < 2 * (R : ℝ); exact mul_pos (by norm_num) R.2,
        by
          change 2 * (R : ℝ) < 3 * (R : ℝ)
          have hR : (0 : ℝ) < (R : ℝ) := R.property
          linarith only [hR]⟩ : EuclideanAnnulus) := by
  apply Subtype.ext
  change ((R : ℝ) • (0 : ℂ) + w, (R : ℝ) * 2, (R : ℝ) * 3) =
    (w, 2 * (R : ℝ), 3 * (R : ℝ))
  simp only [smul_zero, zero_add, Prod.mk.injEq, true_and]
  constructor <;> ring

theorem shieldInnerShape_at (R : Ioi (0 : ℝ)) (w : ℂ) :
    Objects.ProbabilityS7S9.supInner R.2 w =
      (⟨(w, (21 / 20) * (R : ℝ), (39 / 20) * (R : ℝ)),
        by
          change 0 < (21 / 20) * (R : ℝ)
          exact mul_pos (by norm_num) R.2,
        by
          change (21 / 20) * (R : ℝ) < (39 / 20) * (R : ℝ)
          have hR : (0 : ℝ) < (R : ℝ) := R.property
          nlinarith only [hR]⟩ : EuclideanAnnulus) := by
  apply Subtype.ext
  change (w, (1 + 1 / 20) * (R : ℝ), (2 - 1 / 20) * (R : ℝ)) =
    (w, (21 / 20) * (R : ℝ), (39 / 20) * (R : ℝ))
  simp only [Prod.mk.injEq, true_and]
  constructor <;> ring

def shieldBumpIn : ContDiffBump (0 : ℂ) :=
  ⟨1, 21 / 20, by norm_num, by norm_num⟩

def shieldBumpOut : ContDiffBump (0 : ℂ) :=
  ⟨39 / 20, 2, by norm_num, by norm_num⟩

def shieldAnnBump (K : ℝ) : LQGMetric.TestC where
  toFun := fun y => K * (shieldBumpIn y - shieldBumpOut y)
  contDiff' := contDiff_const.mul (shieldBumpIn.contDiff.sub shieldBumpOut.contDiff)
  hasCompactSupport' :=
    (shieldBumpIn.hasCompactSupport.sub shieldBumpOut.hasCompactSupport).mul_left
  tsupport_subset' := subset_univ _

theorem shieldAnnBump_eq_neg (K : ℝ) {y : ℂ}
    (h1 : 21 / 20 ≤ ‖y‖) (h2 : ‖y‖ ≤ 39 / 20) :
    shieldAnnBump K y = -K := by
  have hin : shieldBumpIn y = 0 := by
    apply Function.notMem_support.mp
    rw [ContDiffBump.support_eq]
    change y ∉ ball (0 : ℂ) (21 / 20)
    rw [mem_ball, dist_zero_right]
    linarith
  have hout : shieldBumpOut y = 1 :=
    shieldBumpOut.one_of_mem_closedBall (by
      change y ∈ closedBall (0 : ℂ) (39 / 20)
      rw [mem_closedBall, dist_zero_right]
      exact h2)
  change K * (shieldBumpIn y - shieldBumpOut y) = -K
  rw [hin, hout]
  ring

theorem shieldAnnBump_eq_zero_outer (K : ℝ) {y : ℂ}
    (h : 2 ≤ ‖y‖) : shieldAnnBump K y = 0 := by
  have hin : shieldBumpIn y = 0 := by
    apply Function.notMem_support.mp
    rw [ContDiffBump.support_eq]
    change y ∉ ball (0 : ℂ) (21 / 20)
    rw [mem_ball, dist_zero_right]
    linarith
  have hout : shieldBumpOut y = 0 := by
    apply Function.notMem_support.mp
    rw [ContDiffBump.support_eq]
    change y ∉ ball (0 : ℂ) 2
    rw [mem_ball, dist_zero_right]
    exact not_lt.mpr h
  change K * (shieldBumpIn y - shieldBumpOut y) = 0
  rw [hin, hout]
  ring

def shieldBumpAt (K t : ℝ) (w : ℂ) : LQGMetric.TestC :=
  LQGMetric.GM.transTest w (LQGMetric.GM.dilT t (shieldAnnBump K))

theorem shieldBumpAt_apply (K : ℝ) {t : ℝ} (ht : 0 < t) (w y : ℂ) :
    shieldBumpAt K t w y = shieldAnnBump K ((t⁻¹ : ℝ) • (y - w)) := by
  rw [shieldBumpAt, LQGMetric.GM.transTest_apply, LQGMetric.GM.dilT_apply ht]

theorem shieldBumpAt_eq_neg (K : ℝ) {t : ℝ} (ht : 0 < t) (w : ℂ) {y : ℂ}
    (h1 : (21 / 20) * t ≤ dist y w)
    (h2 : dist y w ≤ (39 / 20) * t) :
    shieldBumpAt K t w y = -K := by
  rw [shieldBumpAt_apply K ht]
  apply shieldAnnBump_eq_neg <;> rw [Objects.ProbabilityS7S9.norm_smul_inv_sub' ht]
  · exact (le_div_iff₀ ht).mpr h1
  · exact (div_le_iff₀ ht).mpr h2

theorem shieldBumpAt_eq_zero_outer (K : ℝ) {t : ℝ} (ht : 0 < t)
    (w : ℂ) {y : ℂ} (h : 2 * t ≤ dist y w) :
    shieldBumpAt K t w y = 0 := by
  rw [shieldBumpAt_apply K ht]
  apply shieldAnnBump_eq_zero_outer
  rw [Objects.ProbabilityS7S9.norm_smul_inv_sub' ht]
  exact (le_div_iff₀ ht).mpr h

theorem gradEnergy_shieldBumpAt (K : ℝ) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    LQGMetric.gradEnergy (shieldBumpAt K t w) =
      LQGMetric.gradEnergy (shieldAnnBump K) := by
  rw [shieldBumpAt, LQGMetric.GM.gradEnergy_transTest,
    LQGMetric.GM.gradEnergy_dilT ht]

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
