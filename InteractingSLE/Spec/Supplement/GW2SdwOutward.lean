/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Labels move outward under the Loewner flow

Packet PROVE-GW2-SDE (round 9, ruling R118). The 17/35 scaling of the label gap (COVER's scaled cover) assumes that
force-point labels move outward at later stages. Take a real force point `x` and a solution `u` of the centered
forward flow (`QuantumZipper.IsForwardSol W x T u`, i.e. `V̂_t = u t`; by `tendsto_fwdMap_of_isForwardSol_real`,
`u t` is the boundary value of `f_t = g_t − W_t` at `x`). Its absolute position is `g_t(x) = Re (u t) + W t`.

* **`re_neg_of_isForwardSol_real`** / **`re_pos_of_isForwardSol_real`**: a label that starts left (right) of the
  driver stays left (right) of it on `[0, T]`;
* **`antitoneOn_pos_of_isForwardSol_left`** / **`monotoneOn_pos_of_isForwardSol_right`**: left labels move left and
  right labels move right (`∂_t g_t(x) = 2/(g_t(x) − W_t)`);
* **`pos_le_of_isForwardSol_left`**, **`le_pos_of_isForwardSol_right`**: each label stays outside its start;
* **`gap_mono_of_isForwardSol`**, **`le_gap_of_isForwardSol`**: the gap between a left and a right label is
  nondecreasing in time and never below its initial value `y − x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory

namespace InteractingSLE.Theorem14.GW2Sdw

variable {W : ℝ → ℝ}

/-- A real solution never has zero real part on `[0, T]`. -/
theorem re_ne_zero_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : (u t).re ≠ 0 := by
  intro h
  apply (hu.2 t ht).1
  apply Complex.ext
  · simpa using h
  · simpa using im_eq_zero_of_isForwardSol_real hW hu ht

/-- The initial value of a solution. -/
theorem re_isForwardSol_zero {x T : ℝ} {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W x T u) (hT : 0 ≤ T) :
    (u 0).re = x - W 0 := by
  rw [(hu.2 0 ⟨le_rfl, hT⟩).2]
  simp

/-- The absolute position of a label: `g_t(x) = x + Re ∫₀ᵗ 2/u`. -/
theorem pos_eq_of_isForwardSol {x T : ℝ} {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W x T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : (u t).re + W t = x + (∫ s in (0 : ℝ)..t, 2 / u s).re := by
  rw [(hu.2 t ht).2]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  ring

/-- **A label left of the driver stays left of it.** -/
theorem re_neg_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (h0 : x < W 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : (u t).re < 0 := by
  by_contra hc'
  have hc := not_lt.1 hc'
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hcont : ContinuousOn (fun r => (u r).re) (Icc 0 T) := Complex.continuous_re.comp_continuousOn hu.1
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have h00 : (u 0).re ≤ 0 := by
    rw [re_isForwardSol_zero hu hT]
    linarith
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 (hcont.mono hsub) ⟨h00, hc⟩
  exact re_ne_zero_of_isForwardSol_real hW hu (hsub hs) hs0

/-- **A label right of the driver stays right of it.** -/
theorem re_pos_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (h0 : W 0 < x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : 0 < (u t).re := by
  by_contra hc'
  have hc := not_lt.1 hc'
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hcont : ContinuousOn (fun r => (u r).re) (Icc 0 T) := Complex.continuous_re.comp_continuousOn hu.1
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have h00 : 0 ≤ (u 0).re := by
    rw [re_isForwardSol_zero hu hT]
    linarith
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 (hcont.mono hsub) ⟨hc, h00⟩
  exact re_ne_zero_of_isForwardSol_real hW hu (hsub hs) hs0

theorem re_two_div_eq (w : ℂ) : (2 / w).re = 2 * w.re / Complex.normSq w := by
  rw [Complex.div_re]
  simp

theorem re_two_div_neg {w : ℂ} (h : w.re < 0) : (2 / w).re < 0 := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 fun h0 => by simp [h0] at h
  rw [re_two_div_eq]
  exact div_neg_of_neg_of_pos (by linarith) hn

theorem re_two_div_pos {w : ℂ} (h : 0 < w.re) : 0 < (2 / w).re := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 fun h0 => by simp [h0] at h
  rw [re_two_div_eq]
  exact div_pos (by linarith) hn

/-- The increment of a label's position is `∫ₐᵇ Re (2/u)`. -/
theorem pos_sub_pos_eq_integral {x T : ℝ} {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W x T u) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    (u b).re + W b - ((u a).re + W a) = ∫ s in a..b, (2 / u s).re := by
  have hcont : ContinuousOn (fun s => 2 / u s) (Icc 0 T) :=
    continuousOn_const.div hu.1 fun s hs => (hu.2 s hs).1
  have hii : ∀ c ∈ Icc (0 : ℝ) T, ∀ d ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun s => 2 / u s) volume c d :=
    fun c hc d hd => (hcont.mono (uIcc_subset_Icc hc hd)).intervalIntegrable
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, ha.1.trans ha.2⟩
  have hre : ∫ s in a..b, (2 / u s).re = (∫ s in a..b, 2 / u s).re := by
    simpa using Complex.reCLM.intervalIntegral_comp_comm (hii a ha b hb)
  rw [pos_eq_of_isForwardSol hu ha, pos_eq_of_isForwardSol hu hb, hre,
    ← intervalIntegral.integral_interval_sub_left (hii 0 h0 b hb) (hii 0 h0 a ha)]
  simp only [Complex.sub_re]
  ring

/-- **Left labels move left.** -/
theorem antitoneOn_pos_of_isForwardSol_left (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (h0 : x < W 0) :
    AntitoneOn (fun t => (u t).re + W t) (Icc 0 T) := by
  intro a ha b hb hab
  have hd := pos_sub_pos_eq_integral hu ha hb
  have hnn : 0 ≤ ∫ s in a..b, -(2 / u s).re := intervalIntegral.integral_nonneg hab fun s hs =>
    (neg_pos.2 (re_two_div_neg (re_neg_of_isForwardSol_real hW hu h0 ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩))).le
  rw [intervalIntegral.integral_neg] at hnn
  show (u b).re + W b ≤ (u a).re + W a
  linarith

/-- **Right labels move right.** -/
theorem monotoneOn_pos_of_isForwardSol_right (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (h0 : W 0 < x) :
    MonotoneOn (fun t => (u t).re + W t) (Icc 0 T) := by
  intro a ha b hb hab
  have hd := pos_sub_pos_eq_integral hu ha hb
  have hnn : 0 ≤ ∫ s in a..b, (2 / u s).re := intervalIntegral.integral_nonneg hab fun s hs =>
    (re_two_div_pos (re_pos_of_isForwardSol_real hW hu h0 ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩)).le
  show (u a).re + W a ≤ (u b).re + W b
  linarith

/-- A left label stays left of its start. -/
theorem pos_le_of_isForwardSol_left (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (h0 : x < W 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u t).re + W t ≤ x := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h := antitoneOn_pos_of_isForwardSol_left hW hu h0 ⟨le_rfl, hT⟩ ht ht.1
  have h00 := re_isForwardSol_zero hu hT
  simp only at h
  linarith

/-- A right label stays right of its start. -/
theorem le_pos_of_isForwardSol_right (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (h0 : W 0 < x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    x ≤ (u t).re + W t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h := monotoneOn_pos_of_isForwardSol_right hW hu h0 ⟨le_rfl, hT⟩ ht ht.1
  have h00 := re_isForwardSol_zero hu hT
  simp only at h
  linarith

/-- **The gap between a left and a right label is nondecreasing.** -/
theorem gap_mono_of_isForwardSol (hW : Continuous W) {x y T : ℝ} {u v : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (hv : QuantumZipper.IsForwardSol W y T v) (hx : x < W 0)
    (hy : W 0 < y) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) (hab : a ≤ b) :
    (v a).re - (u a).re ≤ (v b).re - (u b).re := by
  have h1 := antitoneOn_pos_of_isForwardSol_left hW hu hx ha hb hab
  have h2 := monotoneOn_pos_of_isForwardSol_right hW hv hy ha hb hab
  simp only at h1 h2
  linarith

/-- **The gap between a left and a right label never falls below its initial value.** -/
theorem le_gap_of_isForwardSol (hW : Continuous W) {x y T : ℝ} {u v : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) (hv : QuantumZipper.IsForwardSol W y T v) (hx : x < W 0)
    (hy : W 0 < y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    y - x ≤ (v t).re - (u t).re := by
  have h1 := pos_le_of_isForwardSol_left hW hu hx ht
  have h2 := le_pos_of_isForwardSol_right hW hv hy ht
  linarith

end InteractingSLE.Theorem14.GW2Sdw
