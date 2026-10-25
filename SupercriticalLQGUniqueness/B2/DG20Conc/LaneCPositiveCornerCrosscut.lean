import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPositiveTurnSweep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_positive_corner_paid_crosscut
    (D : ContMetric) {τ : ℝ → ℂ}
    (hτ : ContinuousOn τ (Icc (0 : ℝ) 1))
    (hclosed : τ 0 = τ 1)
    {c : ℂ} {r : ℝ}
    (hτann : ∀ x ∈ Icc (0 : ℝ) 1,
      r < dist (τ x) c ∧ dist (τ x) c < 2 * r)
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim1 : c.im ≤ 1) (hTopNear : 1 - c.im ≤ r)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1)
    {M : ℝ → ℂ} (hM : ContinuousOn M (Icc (0 : ℝ) 1))
    (hMexp : ∀ x ∈ Icc (0 : ℝ) 1,
      Complex.exp (M x) = τ x - c)
    (hperiod : 2 * Real.pi ≤ (M 1 - M 0).im) :
    ∃ α : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1,
        r < dist (α v) c ∧ dist (α v) c < 2 * r ∧
          α v ∈ (rectAB 1 1).toSet) ∧
      α 0 ∈ (rectAB 1 1).side₁ ∧
      (α 1).im = 1 ∧
      D.len α 0 1 ≤ D.len τ 0 1 := by
  obtain ⟨k, s, t, hs, ht, hst, hts, hsAng, htAng, hband, hcost⟩ :=
    laneC_positive_turn_bounded_sweep D hclosed hM hperiod
  let R := laneCRepeatLoop τ
  let N := laneCRepeatLift M
  let shift : ℂ := (k : ℂ) * (2 * Real.pi * Complex.I)
  have hshiftExp : Complex.exp shift = 1 := by
    simpa only [shift] using Complex.exp_int_mul_two_pi_mul_I k
  have hshiftIm : shift.im = 2 * Real.pi * (k : ℝ) := by
    simp [shift, Complex.mul_im, Complex.mul_re]
    ring
  have hRcont : ContinuousOn R (Icc (0 : ℝ) 2) :=
    laneC_repeatLoop_continuousOn hτ hclosed
  have hNcont : ContinuousOn N (Icc (0 : ℝ) 2) :=
    laneC_repeatLift_continuousOn hM
  have hRann : ∀ x ∈ Icc (0 : ℝ) 2,
      r < dist (R x) c ∧ dist (R x) c < 2 * r :=
    laneC_repeatLoop_mapsTo hclosed
      (A := {z : ℂ | r < dist z c ∧ dist z c < 2 * r}) hτann
  have hRexp : ∀ x ∈ Icc (0 : ℝ) 2,
      Complex.exp (N x) = R x - c :=
    laneC_repeatLift_exp hclosed hMexp
  let σ := SupercriticalLQGUniqueness.B2.Strong.seg R s t
  let L := SupercriticalLQGUniqueness.B2.Strong.seg
    (fun x => N x - shift) s t
  have hσ : ContinuousOn σ (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hRcont hs ht
  have hNshift : ContinuousOn (fun x => N x - shift) (Icc (0 : ℝ) 2) :=
    hNcont.sub continuousOn_const
  have hL : ContinuousOn L (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hNshift hs ht
  have hσann : ∀ x ∈ Icc (0 : ℝ) 1,
      r < dist (σ x) c ∧ dist (σ x) c < 2 * r := by
    intro x hx
    exact hRann _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs ht hx)
  have hLexp : ∀ x ∈ Icc (0 : ℝ) 1,
      Complex.exp (L x) = σ x - c := by
    intro x hx
    let p := s + x * (t - s)
    have hp := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs ht hx
    change Complex.exp (N p - shift) = R p - c
    rw [Complex.exp_sub, hshiftExp, div_one]
    exact hRexp p hp
  have hLangle (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (L x).im = (N (s + x * (t - s))).im - 2 * Real.pi * (k : ℝ) := by
    simp only [L, SupercriticalLQGUniqueness.B2.Strong.seg,
      Complex.sub_im, hshiftIm]
  have hL0 : (L 0).im = Real.pi := by
    rw [hLangle 0 (by simp)]
    simp only [zero_mul, add_zero]
    change (laneCRepeatLift M s).im - 2 * Real.pi * (k : ℝ) = Real.pi
    linarith [hsAng]
  have hL1 : (L 1).im = 5 * Real.pi / 2 := by
    rw [hLangle 1 (by simp)]
    rw [show s + 1 * (t - s) = t by ring]
    change (laneCRepeatLift M t).im - 2 * Real.pi * (k : ℝ) = 5 * Real.pi / 2
    linarith [htAng]
  have hLband : ∀ x ∈ Icc (0 : ℝ) 1,
      Real.pi ≤ (L x).im ∧ (L x).im ≤ 5 * Real.pi / 2 := by
    intro x hx
    have hp : s + x * (t - s) ∈ Icc s t := by
      constructor <;> nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hst),
        mul_le_mul_of_nonneg_right hx.2 (sub_nonneg.mpr hst)]
    have hb := hband _ hp
    rw [hLangle x hx]
    constructor <;> linarith
  obtain ⟨α, hα, hαann, hαleft, hαtop, hαcost⟩ :=
    laneC_corner_crosscut_of_bounded_lift D
      (ρ := σ) (a := 0) (b := 1) (s := 0) (t := 1)
      (by simp) (by simp) (by norm_num) hσ hσann
      hcre0 hcreNear hcim1 hTopNear hbelow hright
      hL hLexp hL0 hL1 hLband
  exact ⟨α, hα, hαann, hαleft, hαtop, hαcost.trans hcost⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
