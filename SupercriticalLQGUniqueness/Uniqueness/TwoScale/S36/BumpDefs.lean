import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.WeylBump
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.CMBound
import LQGMetric.Papers.GM.S5.L510C7
import LQGMetric.Papers.GM.S5.Prop43bTrans
import LQGMetric.Papers.GM.S6.GeodSelN
import LQGMetric.Papers.GM.S5.Prop43bInv




 














set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC TestC)

 

 
def bumpIn : ContDiffBump (0 : ℂ) := ⟨21 / 10, 11 / 5, by norm_num, by norm_num⟩

 
def bumpOut : ContDiffBump (0 : ℂ) := ⟨14 / 5, 29 / 10, by norm_num, by norm_num⟩

 
def annBump (K : ℝ) : TestC where
  toFun := fun y => K * (bumpIn y - bumpOut y)
  contDiff' := contDiff_const.mul (bumpIn.contDiff.sub bumpOut.contDiff)
  hasCompactSupport' := (bumpIn.hasCompactSupport.sub bumpOut.hasCompactSupport).mul_left
  tsupport_subset' := subset_univ _

theorem annBump_apply (K : ℝ) (y : ℂ) : annBump K y = K * (bumpIn y - bumpOut y) := rfl

theorem annBump_eq_neg (K : ℝ) {y : ℂ} (h1 : 11 / 5 ≤ ‖y‖) (h2 : ‖y‖ ≤ 14 / 5) :
    annBump K y = -K := by
  rw [annBump_apply]
  have hin : bumpIn y = 0 := by
    apply Function.notMem_support.mp
    rw [ContDiffBump.support_eq]
    change y ∉ Metric.ball (0 : ℂ) (11 / 5)
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hout : bumpOut y = 1 := bumpOut.one_of_mem_closedBall (by
    change y ∈ Metric.closedBall (0 : ℂ) (14 / 5)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h2)
  rw [hin, hout]
  ring

theorem annBump_eq_zero (K : ℝ) {y : ℂ} (h : ‖y‖ ≤ 21 / 10) : annBump K y = 0 := by
  rw [annBump_apply]
  have hin : bumpIn y = 1 := bumpIn.one_of_mem_closedBall (by
    change y ∈ Metric.closedBall (0 : ℂ) (21 / 10)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h)
  have hout : bumpOut y = 1 := bumpOut.one_of_mem_closedBall (by
    change y ∈ Metric.closedBall (0 : ℂ) (14 / 5)
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith)
  rw [hin, hout]
  ring

 
def bumpAt (K s : ℝ) (x : ℂ) : TestC := LQGMetric.GM.transTest x (LQGMetric.GM.dilT s (annBump K))

theorem bumpAt_apply (K : ℝ) {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    bumpAt K s x y = annBump K ((s⁻¹ : ℝ) • (y - x)) := by
  rw [bumpAt, LQGMetric.GM.transTest_apply, LQGMetric.GM.dilT_apply hs]

theorem gradEnergy_bumpAt (K : ℝ) {s : ℝ} (hs : 0 < s) (x : ℂ) :
    LQGMetric.gradEnergy (bumpAt K s x) = LQGMetric.gradEnergy (annBump K) := by
  rw [bumpAt, LQGMetric.GM.gradEnergy_transTest, LQGMetric.GM.gradEnergy_dilT hs]

theorem norm_smul_inv_sub {s : ℝ} (hs : 0 < s) (x y : ℂ) :
    ‖(s⁻¹ : ℝ) • (y - x)‖ = dist y x / s := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), dist_eq_norm]
  field_simp

theorem bumpAt_eq_neg (K : ℝ) {s : ℝ} (hs : 0 < s) (x : ℂ) {y : ℂ}
    (h1 : 11 * s / 5 ≤ dist y x) (h2 : dist y x ≤ 14 * s / 5) : bumpAt K s x y = -K := by
  rw [bumpAt_apply K hs]
  apply annBump_eq_neg <;> rw [norm_smul_inv_sub hs]
  · rw [le_div_iff₀ hs]; linarith
  · rw [div_le_iff₀ hs]; linarith

theorem bumpAt_eq_zero (K : ℝ) {s : ℝ} (hs : 0 < s) (x : ℂ) {y : ℂ}
    (h : dist y x ≤ 2 * s) : bumpAt K s x y = 0 := by
  rw [bumpAt_apply K hs]
  apply annBump_eq_zero
  rw [norm_smul_inv_sub hs, div_le_iff₀ hs]
  linarith

 

 
def annOut {s : ℝ} (hs : 0 < s) (x : ℂ) : EuclideanAnnulus :=
  ⟨(x, (2 * s, 3 * s)), by positivity, by linarith⟩

 
def annIn {s : ℝ} (hs : 0 < s) (x : ℂ) : EuclideanAnnulus :=
  ⟨(x, (s, 2 * s)), hs, by linarith⟩

 
def annSmall {s : ℝ} (hs : 0 < s) (x : ℂ) : EuclideanAnnulus :=
  ⟨(x, (11 * s / 5, 14 * s / 5)), by positivity, by linarith⟩

 
def RatioEv (d : LSCMetric) {s : ℝ} (hs : 0 < s) (x : ℂ) : Prop :=
  aroundDist d (annOut hs x) < ⊤ ∧ 2 * aroundDist d (annOut hs x) ≤ acrossDist d (annIn hs x) ∧
    0 < acrossDist d (annIn hs x)

 


theorem aroundDist_le_of_nested' (D : LSCMetric) (big small : EuclideanAnnulus)
    (hset : small.toSet ⊆ big.toSet)
    (hin : big.innerBoundary ⊆ Metric.closedBall small.center small.innerRadius)
    (hout : big.outerBoundary ⊆ (Metric.ball small.center small.outerRadius)ᶜ) :
    aroundDist D big ≤ aroundDist D small := by
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hPs => le_iInf fun hsep => ?_
  have hclosed : IsClosed (P '' Icc a b) := hP.isClosed_image
  have hpath : LQGMetric.Disconnects (P '' Icc a b)
      small.innerBoundary small.outerBoundary :=
    (disconnects_iff_lqgMetric_disconnects hclosed).mp hsep
  have hpath' : LQGMetric.Disconnects (P '' Icc a b)
      big.innerBoundary big.outerBoundary :=
    (LQGMetric.Disconnects.closedBall_compl_ball small.2.2.le hpath).mono
      (Subset.refl _) hin hout
  have hsep' : Disconnects (P '' Icc a b)
      big.innerBoundary big.outerBoundary :=
    (disconnects_iff_lqgMetric_disconnects hclosed).mpr hpath'
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le (fun t ht => hset (hPs t ht)) <|
      iInf_le_of_le hsep' le_rfl

theorem around_le_small (d : LSCMetric) {s : ℝ} (hs : 0 < s) (x : ℂ) :
    aroundDist d (annOut hs x) ≤ aroundDist d (annSmall hs x) := by
  apply aroundDist_le_of_nested'
  · intro y hy
    change y ∈ Metric.ball x (14 * s / 5) ∧ y ∉ closure (Metric.ball x (11 * s / 5)) at hy
    change y ∈ Metric.ball x (3 * s) ∧ y ∉ closure (Metric.ball x (2 * s))
    rw [closure_ball x (by positivity)] at hy ⊢
    refine ⟨Metric.ball_subset_ball (by linarith) hy.1, fun h => hy.2 ?_⟩
    exact Metric.closedBall_subset_closedBall (by linarith) h
  · intro y hy
    change y ∈ Metric.sphere x (2 * s) at hy
    change y ∈ Metric.closedBall x (11 * s / 5)
    rw [Metric.mem_closedBall, Metric.mem_sphere.mp hy]
    linarith
  · intro y hy
    change y ∈ Metric.sphere x (3 * s) at hy
    change y ∈ (Metric.ball x (14 * s / 5))ᶜ
    rw [mem_compl_iff, Metric.mem_ball, Metric.mem_sphere.mp hy]
    linarith

 
theorem ratioEv_scale_iff (d₁ d₂ : LSCMetric) (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hscale : ∀ x y : ℂ, d₂ (x, y) = k * d₁ (x, y)) {s : ℝ} (hs : 0 < s) (x : ℂ) :
    RatioEv d₂ hs x ↔ RatioEv d₁ hs x := by
  unfold RatioEv
  rw [Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hscale,
    Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hscale]
  have h1 : k * aroundDist d₁ (annOut hs x) < ⊤ ↔ aroundDist d₁ (annOut hs x) < ⊤ :=
    mul_lt_top_iff_of_ne hk0 hkt _
  have h2 : 2 * (k * aroundDist d₁ (annOut hs x)) ≤ k * acrossDist d₁ (annIn hs x) ↔
      2 * aroundDist d₁ (annOut hs x) ≤ acrossDist d₁ (annIn hs x) := by
    rw [mul_left_comm]
    exact ENNReal.mul_le_mul_iff_right hk0 hkt
  have h3 : 0 < k * acrossDist d₁ (annIn hs x) ↔ 0 < acrossDist d₁ (annIn hs x) := by
    rw [ENNReal.mul_pos_iff]
    exact ⟨fun h => h.2, fun h => ⟨pos_iff_ne_zero.mpr hk0, h⟩⟩
  rw [h1, h2, h3]

 

theorem around_lt_across_of_ratioEv {d : LSCMetric} {s : ℝ} {hs : 0 < s} {x : ℂ}
    (hE : RatioEv d hs x) : aroundDist d (annOut hs x) < acrossDist d (annIn hs x) := by
  obtain ⟨hfin, h2, hpos⟩ := hE
  by_cases htop : acrossDist d (annIn hs x) = ⊤
  · rw [htop]
    exact hfin
  · by_contra hge
    push Not at hge
    have : 2 * acrossDist d (annIn hs x) ≤ acrossDist d (annIn hs x) :=
      (mul_le_mul' le_rfl hge).trans h2
    have hlt : acrossDist d (annIn hs x) < 2 * acrossDist d (annIn hs x) := by
      rw [two_mul]
      exact ENNReal.lt_add_right htop hpos.ne'
    exact absurd this (not_le.mpr hlt)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
