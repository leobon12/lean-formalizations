import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerExtension

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

def laneCmid : ℂ := ⟨1 / 2, 1 / 2⟩

 

def laneCInwardPerturb (β : ℝ → ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  let w : ℝ := ε * t * (1 - t)
  ((1 - w : ℝ) : ℂ) * β t + (w : ℂ) * laneCmid

theorem laneC_inwardPerturb_continuous
    {β : ℝ → ℂ} (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (ε : ℝ) :
    ContinuousOn (laneCInwardPerturb β ε) (Icc (0 : ℝ) 1) := by
  unfold laneCInwardPerturb
  have hw : Continuous fun t : ℝ => ε * t * (1 - t) := by fun_prop
  exact (((Complex.continuous_ofReal.comp
    (continuous_const.sub hw)).continuousOn).mul hβ).add
      ((Complex.continuous_ofReal.comp hw).continuousOn.mul continuousOn_const)

theorem laneC_inwardPerturb_ends (β : ℝ → ℂ) (ε : ℝ) :
    laneCInwardPerturb β ε 0 = β 0 ∧
      laneCInwardPerturb β ε 1 = β 1 := by
  simp [laneCInwardPerturb]

private theorem laneC_inward_weight_bounds
    {ε t : ℝ} (hε : 0 < ε ∧ ε ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ ε * t * (1 - t) ∧ ε * t * (1 - t) < 1 := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hε0 : 0 ≤ ε := hε.1.le
  have hprod : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have hprod1 : t * (1 - t) ≤ 1 := by
    nlinarith [mul_nonneg ht0 (by linarith : 0 ≤ 1 - t)]
  constructor
  · nlinarith [mul_nonneg hε0 hprod]
  · nlinarith [mul_le_mul_of_nonneg_left hprod1 hε0]

theorem laneC_inwardPerturb_square
    {β : ℝ → ℂ} (hβsq : ∀ t ∈ Icc (0 : ℝ) 1,
      β t ∈ (rectAB 1 1).toSet)
    {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      laneCInwardPerturb β ε t ∈ (rectAB 1 1).toSet := by
  intro t ht
  let w := ε * t * (1 - t)
  have hw := laneC_inward_weight_bounds hε ht
  have hb := mem_rectAB_toSet.mp (hβsq t ht)
  have hpoint :
      (laneCInwardPerturb β ε t).re = (1 - w) * (β t).re + w / 2 ∧
      (laneCInwardPerturb β ε t).im = (1 - w) * (β t).im + w / 2 := by
    simp [laneCInwardPerturb, laneCmid, w, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
    all_goals ring
  rw [mem_rectAB_toSet, hpoint.1, hpoint.2]
  constructor <;> constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw.2.le) hb.1.1]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw.2.le)
      (sub_nonneg.mpr hb.1.2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw.2.le) hb.2.1]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw.2.le)
      (sub_nonneg.mpr hb.2.2)]

theorem laneC_inwardPerturb_positive_re
    {β : ℝ → ℂ} (hβsq : ∀ t ∈ Icc (0 : ℝ) 1,
      β t ∈ (rectAB 1 1).toSet)
    {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) :
    0 < (laneCInwardPerturb β ε t).re := by
  let w := ε * t * (1 - t)
  have hw := laneC_inward_weight_bounds hε ht
  have hwp : 0 < w := by
    have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hq : 0 < 1 - t := by
      have : t < 1 := lt_of_le_of_ne ht.2 ht1
      linarith
    exact mul_pos (mul_pos hε.1 htp) hq
  have hb : 0 ≤ (β t).re := (mem_rectAB_toSet.mp (hβsq t ht)).1.1
  have hre : (laneCInwardPerturb β ε t).re =
      (1 - w) * (β t).re + w / 2 := by
    simp [laneCInwardPerturb, laneCmid, w, Complex.add_re,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [hre]
  nlinarith [mul_nonneg (sub_nonneg.mpr hw.2.le) hb]

end SupercriticalLQGUniqueness.B2.DG20Conc
