import QuantumZipper.Proofs.Loewner.RevMapExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-FLOW (1): quantitative complex solutions near a real solution

`exists_ball_isCRevSol_quant`: if a real reverse Loewner solution from `x` stays at distance
`≥ c` from `0` on `[0,T]`, then every `z` with `‖z - x‖ < (c/4) e^{-8T/c²}` has a complex
solution staying at distance `≥ c/2` from `0`. The radius depends only on `c` and `T`.

This is the proof of `RevMapExtension.exists_ball_isCRevSol` (Picard–Lindelöf for a
box-truncated field plus Grönwall) with the clearance `c` taken as a hypothesis instead of being
extracted from the solution, so that the radius is explicit. The private box-clamp helpers of
that file are copied verbatim (renamed).
-/

noncomputable section

open Complex Filter MeasureTheory intervalIntegral Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension

def b7bfClampR (lo hi y : ℝ) : ℝ := min (max y lo) hi

theorem abs_b7bfClampR_sub_le (lo hi y₁ y₂ : ℝ) :
    |b7bfClampR lo hi y₁ - b7bfClampR lo hi y₂| ≤ |y₁ - y₂| := by
  unfold b7bfClampR
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ (by simp))
  refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le le_rfl (by simp))

theorem b7bfClampR_mem {lo hi : ℝ} (h : lo ≤ hi) (y : ℝ) :
    lo ≤ b7bfClampR lo hi y ∧ b7bfClampR lo hi y ≤ hi :=
  ⟨le_min (le_max_right _ _) h, min_le_right _ _⟩

theorem b7bfClampR_eq {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) : b7bfClampR lo hi y = y := by
  unfold b7bfClampR; rw [max_eq_left h1, min_eq_left h2]

/-- Clamp to the closed box `[m - r, m + r] × [-r, r]`. -/
def b7bfBoxClamp (m r : ℝ) (y : ℂ) : ℂ :=
  (b7bfClampR (m - r) (m + r) y.re : ℂ) + (b7bfClampR (-r) r y.im : ℂ) * I

theorem b7bfBoxClamp_re (m r : ℝ) (y : ℂ) :
    (b7bfBoxClamp m r y).re = b7bfClampR (m - r) (m + r) y.re := by simp [b7bfBoxClamp]

theorem b7bfBoxClamp_im (m r : ℝ) (y : ℂ) :
    (b7bfBoxClamp m r y).im = b7bfClampR (-r) r y.im := by simp [b7bfBoxClamp]

theorem b7bfBoxClamp_eq {m r : ℝ} {y : ℂ} (hre : |y.re - m| ≤ r) (him : |y.im| ≤ r) :
    b7bfBoxClamp m r y = y := by
  have h1 := abs_le.1 hre
  have h2 := abs_le.1 him
  apply Complex.ext
  · rw [b7bfBoxClamp_re]; exact b7bfClampR_eq (by linarith) (by linarith)
  · rw [b7bfBoxClamp_im]; exact b7bfClampR_eq (by linarith) (by linarith)

theorem b7bf_norm_le_norm_of_abs_le {a b : ℂ} (hre : |a.re| ≤ |b.re|)
    (him : |a.im| ≤ |b.im|) : ‖a‖ ≤ ‖b‖ := by
  have h1 : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    have e1 := sq_le_sq.2 hre
    have e2 := sq_le_sq.2 him
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem norm_b7bfBoxClamp_sub_le (m r : ℝ) (y₁ y₂ : ℂ) :
    ‖b7bfBoxClamp m r y₁ - b7bfBoxClamp m r y₂‖ ≤ ‖y₁ - y₂‖ := by
  apply b7bf_norm_le_norm_of_abs_le
  · rw [Complex.sub_re, Complex.sub_re, b7bfBoxClamp_re, b7bfBoxClamp_re]; exact abs_b7bfClampR_sub_le _ _ _ _
  · rw [Complex.sub_im, Complex.sub_im, b7bfBoxClamp_im, b7bfBoxClamp_im]; exact abs_b7bfClampR_sub_le _ _ _ _

theorem norm_b7bfBoxClamp_sub_center_le {m r : ℝ} (hr : 0 ≤ r) (y : ℂ) :
    ‖b7bfBoxClamp m r y - (m : ℂ)‖ ≤ 2 * r := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im, b7bfBoxClamp_re, b7bfBoxClamp_im, ofReal_re, ofReal_im, sub_zero]
  have h1 := b7bfClampR_mem (show m - r ≤ m + r by linarith) y.re
  have h2 := b7bfClampR_mem (show -r ≤ r by linarith) y.im
  have e1 : |b7bfClampR (m - r) (m + r) y.re - m| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |b7bfClampR (-r) r y.im| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
  linarith
/-- Quantitative form of `exists_ball_isCRevSol`: explicit radius from the clearance. -/
theorem exists_ball_isCRevSol_quant {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W) (hT : 0 ≤ T)
    {x : ℝ} {w : ℝ → ℝ} (hw : IsRealRevSol W x T w) {c : ℝ} (hc : 0 < c)
    (hcw : ∀ t ∈ Icc (0 : ℝ) T, c ≤ |w t|) :
    ∀ z ∈ Metric.ball (x : ℂ) ((c / 4) / Real.exp ((2 / (c / 2) ^ 2) * T)),
      ∃ u, IsCRevSol W z T u ∧ ∀ s ∈ Icc (0 : ℝ) T, c / 2 ≤ ‖u s‖ := by
  set r := c / 4 with hr
  have hr0 : 0 < r := by positivity
  set m : ℝ → ℝ := fun s => w s + W s with hm
  have hmcont : ContinuousOn m (Icc 0 T) := hw.1.add hW.continuousOn
  set mC : ℝ → ℂ := fun s => (w s : ℂ) + (W s : ℂ) with hmC
  set F : ℝ → ℂ → ℂ := fun s y => -2 / (b7bfBoxClamp (m s) r y - W s) with hF
  have hPfar : ∀ s ∈ Icc (0 : ℝ) T, ∀ y, c / 2 ≤ ‖b7bfBoxClamp (m s) r y - W s‖ := by
    intro s hs y
    have h1 := norm_b7bfBoxClamp_sub_center_le (m := m s) hr0.le y
    have h2 := hcw s hs
    have e : b7bfBoxClamp (m s) r y - (W s : ℂ) = (w s : ℂ) + (b7bfBoxClamp (m s) r y - (m s : ℂ)) := by
      simp only [hm]; push_cast; ring
    have h3 : ‖((w s : ℝ) : ℂ)‖ = |w s| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 := norm_sub_le ((w s : ℂ) + (b7bfBoxClamp (m s) r y - (m s : ℂ)))
      (b7bfBoxClamp (m s) r y - (m s : ℂ))
    rw [add_sub_cancel_right, ← e] at h4
    linarith
  set K : ℝ≥0 := ⟨2 / (c / 2) ^ 2, by positivity⟩ with hKdef
  have hFlip : ∀ s ∈ Icc (0 : ℝ) T, LipschitzWith K (F s) := by
    intro s hs
    apply LipschitzWith.of_dist_le_mul
    intro y₁ y₂
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := RealLine.norm_neg_two_div_sub_le' (by positivity : 0 < c / 2) (hPfar s hs y₁)
      (hPfar s hs y₂)
    rw [show b7bfBoxClamp (m s) r y₁ - (W s : ℂ) - (b7bfBoxClamp (m s) r y₂ - W s) =
      b7bfBoxClamp (m s) r y₁ - b7bfBoxClamp (m s) r y₂ by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_b7bfBoxClamp_sub_le _ _ _ _) (by positivity))
  have hFbd : ∀ s ∈ Icc (0 : ℝ) T, ∀ y, ‖F s y‖ ≤ 2 / (c / 2) := by
    intro s hs y
    have h1 := hPfar s hs y
    simp only [hF]
    rw [norm_div, show ‖(-2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
  have hFcont : ∀ y, ContinuousOn (fun s => F s y) (Icc 0 T) := by
    intro y
    have hP : ContinuousOn (fun s => b7bfBoxClamp (m s) r y) (Icc 0 T) := by
      simp only [b7bfBoxClamp, b7bfClampR]
      refine ContinuousOn.add ?_ continuousOn_const
      exact continuous_ofReal.comp_continuousOn
        (((continuous_const.max (continuous_id.sub continuous_const)).min
          (continuous_id.add continuous_const)).comp_continuousOn hmcont)
    exact continuousOn_const.div (hP.sub (continuous_ofReal.comp hW).continuousOn)
      fun s hs h0 => by have := hPfar s hs y; rw [h0, norm_zero] at this; linarith
  have hFm : ∀ s ∈ Icc (0 : ℝ) T, F s (mC s) = -2 / (w s : ℂ) := by
    intro s hs
    have hb : b7bfBoxClamp (m s) r (mC s) = mC s := by
      apply b7bfBoxClamp_eq
      · simp only [hmC, hm, add_re, ofReal_re, sub_self, abs_zero]; exact hr0.le
      · simp only [hmC, add_im, ofReal_im, add_zero, abs_zero]; exact hr0.le
    rw [show F s (mC s) = -2 / (b7bfBoxClamp (m s) r (mC s) - W s) from rfl, hb]
    simp only [hmC, add_sub_cancel_right]
  set ρ := r / Real.exp (K * T) with hρ
  intro z hz
  have hpl : IsPicardLindelof F (⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) z
      ⟨2 / (c / 2) * T, mul_nonneg (by positivity) hT⟩ 0 ⟨2 / (c / 2), by positivity⟩ K := by
    refine ⟨fun s hs => (hFlip s hs).lipschitzOnWith, fun y _ => hFcont y,
      fun s hs y _ => hFbd s hs y, ?_⟩
    show 2 / (c / 2) * max (T - 0) (0 - 0) ≤ 2 / (c / 2) * T - 0
    rw [sub_zero, sub_zero, max_eq_left hT, sub_zero]
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α 0 = z := hα0
  have hαcont : ContinuousOn α (Icc 0 T) := fun s hs => (hαd s hs).continuousWithinAt
  -- Grönwall comparison with the real solution
  have hgd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => α s - mC s)
      (F s (α s) - F s (mC s)) (Icc 0 T) s := by
    intro s hs
    rw [hFm s hs]
    exact (hαd s hs).sub (RealLine.isRealRevSol_hasDerivWithinAt_ofReal hw hs)
  have hgc : ContinuousOn (fun s => α s - mC s) (Icc 0 T) :=
    fun s hs => (hgd s hs).continuousWithinAt
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖z - x‖) (K := K) (ε := 0)
    hgc (fun s hs => (hgd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (by
      apply le_of_eq
      simp only [hmC]
      rw [hα0', RealLine.isRealRevSol_zero hw hT]
      congr 1; push_cast; ring)
    (fun s hs => by
      rw [add_zero, ← dist_eq_norm, ← dist_eq_norm]
      exact (hFlip s (Ico_subset_Icc_self hs)).dist_le_mul _ _)
  have hzx : ‖z - x‖ * Real.exp (K * T) < r := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact (lt_div_iff₀ (Real.exp_pos _)).1 hz
  have hsmall : ∀ s ∈ Icc (0 : ℝ) T, ‖α s - mC s‖ ≤ r := by
    intro s hs
    have h1 := hgr s hs
    rw [gronwallBound_ε0, sub_zero] at h1
    have h2 : Real.exp (K * s) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 K.2)
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (z - x))
    linarith
  have hPα : ∀ s ∈ Icc (0 : ℝ) T, b7bfBoxClamp (m s) r (α s) = α s := by
    intro s hs
    have h1 := hsmall s hs
    apply b7bfBoxClamp_eq
    · have := (Complex.abs_re_le_norm (α s - mC s)).trans h1
      simpa [hmC, hm] using this
    · have := (Complex.abs_im_le_norm (α s - mC s)).trans h1
      simpa [hmC] using this
  set u : ℝ → ℂ := fun s => α s - W s with hu
  have hubd : ∀ s ∈ Icc (0 : ℝ) T, c / 2 ≤ ‖u s‖ := by
    intro s hs
    have := hPfar s hs (α s)
    rwa [hPα s hs] at this
  have hune : ∀ s ∈ Icc (0 : ℝ) T, u s ≠ 0 := by
    intro s hs h0
    have := hubd s hs
    rw [h0, norm_zero] at this
    linarith
  have hucont : ContinuousOn u (Icc 0 T) :=
    hαcont.sub (continuous_ofReal.comp hW).continuousOn
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (-2 / u s) (Icc 0 T) s := by
    intro s hs
    have := hαd s hs
    have e : F s (α s) = -2 / u s := by
      simp only [hF, hu, hPα s hs]
    rwa [e] at this
  refine ⟨u, ⟨hucont, fun s hs => ⟨hune s hs, ?_⟩⟩, hubd⟩
  have hsubT : Icc (0 : ℝ) s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hlocal : ∀ q ∈ Ioo (0 : ℝ) s, HasDerivWithinAt α (-2 / u q) (Ioi q) q := by
    intro q hq
    have hq' : q ∈ Ico (0 : ℝ) T := ⟨hq.1.le, lt_of_lt_of_le hq.2 hs.2⟩
    exact ((hderiv q (Ico_subset_Icc_self hq')).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hq')).mono Ioi_subset_Ici_self
  have hint : IntervalIntegrable (fun q => (-2 : ℂ) / u q) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact continuousOn_const.div (hucont.mono hsubT) (fun q hq => hune q (hsubT hq))
  have hFTC : ∫ q in (0 : ℝ)..s, (-2 : ℂ) / u q = α s - α 0 :=
    integral_eq_sub_of_hasDeriv_right_of_le hs.1 (hαcont.mono hsubT) hlocal hint
  have hneg : (∫ q in (0 : ℝ)..s, (-2 : ℂ) / u q) = -∫ q in (0 : ℝ)..s, (2 : ℂ) / u q := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext q; ring
  show α s - W s = z - W s - ∫ q in (0 : ℝ)..s, 2 / u q
  linear_combination -hFTC + hneg + hα0'

end SWCore
end QuantumZipper
