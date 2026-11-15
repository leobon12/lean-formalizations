/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAHL6
import QuantumZipper.Proofs.GFF.K3.C5Kernel
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.RS.TraceShift

/-!
# The local comparison of Aux. lemma 55: (HL6) and (HL7)

Packet PROVE-LOCEXT-A, deterministic parts of step 4 (see `LocalExtAHL6` for the route). Source: Aux. lemma 55,
proof (`source/spec/p241-288.md` L184–L212, pp. 248–249).

For a driver in the local regime with distant marks separated from it, and `y ∈ ℍ ∖ K_s`:

* `dFun_eq`: **the two representations** of `D_s(y) = ∫₀ˢ Im(2/f_u(y)) (E(u) − A(u)) du`, namely
  `D_s = G_{ℍ∖K_s} v − f + q − q_s`;
* `abs_dFun_le_of_re`, `abs_dFun_le_of_norm_le`, `abs_dFun_le_of_le_norm`: the bounds near the real line away from
  the seed (`≲ Im y`), near the seed and the hull (`≲ Im f_s(y)`), and at `∞` (`≲ 1/|y|`);
* `tendsto_im_fwdMap_of_mem_fwdHull`: **properness**: `Im f_s(y) → 0` as `y → y₀ ∈ K_s`;
* `dFun_eq_zero`: **(HL6)**, `D_s = 0` on `ℍ ∖ K_s` (bounded harmonic uniqueness in the half-plane coordinate);
* `srcDrift_eq_distDrift`: **(HL7)**, `A(u) = E(u) = κ^{-1/2} ∑_{j∈J} ρ_j/(W_u − V^j_u)` through the regime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol greenH)

/-! ### An elementary bound on the argument -/

/-- For `Re z ≥ 0`: `|arg z| ≤ (π/2)|Im z|/|z|` (Jordan's inequality). -/
theorem abs_arg_le_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    |Complex.arg z| ≤ Real.pi / 2 * (|z.im| / ‖z‖) := by
  have hθ := Complex.abs_arg_le_pi_div_two_iff.2 hz
  have hsin := Complex.sin_arg z
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hπ := Real.pi_pos
  rcases le_total 0 (Complex.arg z) with h0 | h0
  · rw [abs_of_nonneg h0]
    have := Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at hθ; exact hθ)
    rw [hsin] at this
    have h1 : z.im / ‖z‖ ≤ |z.im| / ‖z‖ := div_le_div_of_nonneg_right (le_abs_self _) hn.le
    have h2 : Complex.arg z ≤ Real.pi / 2 * (z.im / ‖z‖) := by
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ Real.pi / 2 by positivity)
      rwa [← mul_assoc, show Real.pi / 2 * (2 / Real.pi) = 1 by field_simp, one_mul] at this
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  · rw [abs_of_nonpos h0]
    have := Real.mul_le_sin (neg_nonneg.2 h0) (by rw [abs_of_nonpos h0] at hθ; exact hθ)
    rw [Real.sin_neg, hsin] at this
    have h1 : -(z.im / ‖z‖) ≤ |z.im| / ‖z‖ := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (neg_le_abs _) hn.le
    have h2 : -Complex.arg z ≤ Real.pi / 2 * (-(z.im / ‖z‖)) := by
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ Real.pi / 2 by positivity)
      rwa [← mul_assoc, show Real.pi / 2 * (2 / Real.pi) = 1 by field_simp, one_mul] at this
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

/-! ### The two representations of `D_s` -/

section Rep

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {W : ℝ → ℝ} {VL : Fin nL → ℝ → ℝ} {VR : Fin nR → ℝ → ℝ} {T : ℝ}

/-- **The distant marks in the local regime**: on `[0, T]` each distant mark solves the real Loewner equation, lies
on its side of the driver, and stays at distance `≥ 7r`. -/
structure HasDistantMarks (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ → ℝ) (VL : Fin nL → ℝ → ℝ)
    (VR : Fin nR → ℝ → ℝ) (r T : ℝ) : Prop where
  markL : ∀ i ∈ distSetL xL, IsSeparatedMark W (VL i) (xL i) T (7 * r)
  markR : ∀ i ∈ distSetR xR, IsSeparatedMark W (VR i) (xR i) T (7 * r)
  leftL : ∀ i ∈ distSetL xL, ∀ u ∈ Icc (0 : ℝ) T, VL i u ≤ W u
  rightR : ∀ i ∈ distSetR xR, ∀ u ∈ Icc (0 : ℝ) T, W u ≤ VR i u

variable (κ xL xR ρL ρR r W VL VR)

/-- `q_s(y)`, the function (HL5) at time `s`. -/
def qAt (s : ℝ) (y : ℂ) : ℝ :=
  distantHarm κ xL xR ρL ρR (fun i => VL i s - W s) (fun i => VR i s - W s) (fwdMap W s y)

/-- `E(u) − A(u)`: the distant drift minus the source drift. -/
def driftGap (u : ℝ) : ℝ :=
  distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) - srcDrift κ xL xR ρL ρR r W u

/-- `D_s(y) = ∫₀ˢ Im(2/f_u(y)) (E(u) − A(u)) du`. -/
def dFun (s : ℝ) (y : ℂ) : ℝ := ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * driftGap κ xL xR ρL ρR r W VL VR u

variable {κ xL xR ρL ρR r W VL VR}

theorem continuousOn_distDrift (h : IsLocalRegime W r T) (hD : HasDistantMarks xL xR W VL VR r T) :
    ContinuousOn (fun u => distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u)) (Icc 0 T) := by
  have hr7 : 0 < 7 * r := by linarith [h.r_pos]
  refine continuousOn_const.mul ((continuousOn_finsetSum _ fun i hi => ?_).add
    (continuousOn_finsetSum _ fun i hi => ?_))
  · refine continuousOn_const.div (h.cont.continuousOn.sub (hD.markL i hi).cont) fun u hu h0 => ?_
    exact (hD.markL i hi).ne_zero hr7 hu (by linarith)
  · refine continuousOn_const.div (h.cont.continuousOn.sub (hD.markR i hi).cont) fun u hu h0 => ?_
    exact (hD.markR i hi).ne_zero hr7 hu (by linarith)

theorem continuousOn_driftGap (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) :
    ContinuousOn (driftGap κ xL xR ρL ρR r W VL VR) (Icc 0 T) :=
  (continuousOn_distDrift h hD).sub (continuousOn_srcDrift h hF hr)

theorem exists_abs_driftGap_le (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc (0 : ℝ) T, |driftGap κ xL xR ρL ρR r W VL VR u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn
    (continuousOn_driftGap (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD)).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun u hu => (hC _ (mem_image_of_mem _ hu)).trans (le_max_left _ _)⟩

/-- **The two representations of `D_s`** (the integrated Loewner–Green identity against the source, Green inversion,
and the dynamics of (HL5)): `D_s(y) = G_{ℍ∖K_s} v (y) − f(y) + q(y) − q_s(y)`. -/
theorem dFun_eq (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) :
    dFun κ xL xR ρL ρR r W VL VR s y = greenPot κ xL xR ρL ρR r W s y - fCut κ xL xR ρL ρR r y +
      qExt κ xL xR ρL ρR y - qAt κ xL xR ρL ρR W VL VR s y := by
  have hs0 := hs.1
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hmL : ∀ i ∈ distSetL xL, IsSeparatedMark W (VL i) (xL i) s (7 * r) := fun i hi =>
    ⟨(hD.markL i hi).cont.mono hsub, fun u hu => (hD.markL i hi).eq u (hsub hu),
      fun u hu => (hD.markL i hi).sep u (hsub hu)⟩
  have hmR : ∀ i ∈ distSetR xR, IsSeparatedMark W (VR i) (xR i) s (7 * r) := fun i hi =>
    ⟨(hD.markR i hi).cont.mono hsub, fun u hu => (hD.markR i hi).eq u (hsub hu),
      fun u hu => (hD.markR i hi).sep u (hsub hu)⟩
  have hq := distantHarm_fwdMap_sub_qExt (κ := κ) (ρL := ρL) (ρR := ρR) h.cont hs0 hy
    (by linarith [h.r_pos] : 0 < 7 * r) hmL hmR ⟨hs0, le_rfl⟩
  have hG := greenPot_eq (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hs hy
  have him : ContinuousOn (fun u => (2 / fwdMap W u y).im) (Icc 0 s) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_const.div (Ito.continuousOn_fwdMap_time' h.cont hs0 hy)
      fun u hu => Ito.fwdMap_ne_zero h.cont hs0 hy hu)
  have hI1 : IntervalIntegrable (fun u => (2 / fwdMap W u y).im * srcDrift κ xL xR ρL ρR r W u) volume 0 s :=
    (him.mul ((continuousOn_srcDrift h hF hr).mono hsub)).intervalIntegrable_of_Icc hs0
  have hI2 : IntervalIntegrable (fun u => distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) *
      (2 / fwdMap W u y).im) volume 0 s :=
    (((continuousOn_distDrift h hD).mono hsub).mul him).intervalIntegrable_of_Icc hs0
  have hsplit : dFun κ xL xR ρL ρR r W VL VR s y =
      (∫ u in (0 : ℝ)..s, distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) *
        (2 / fwdMap W u y).im) - ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * srcDrift κ xL xR ρL ρR r W u := by
    rw [dFun, ← intervalIntegral.integral_sub hI2 hI1]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [driftGap]
    ring
  simp only [qAt]
  rw [hsplit]
  linarith

/-! ### Bounds for `D_s` -/

/-- **(HL5) is small near the real line between the marks**: for `w ∈ ℍ` with `|Re w| ≤ R` and distant marks
beyond `±(R + d)`, `|q(w)| ≤ |κ^{-1/2}| (∑_J |ρ_j|) (π/2) Im w / d`. -/
theorem abs_distantHarm_le {aL : Fin nL → ℝ} {aR : Fin nR → ℝ} {R d : ℝ} (hd : 0 < d) {w : ℂ} (hw : 0 < w.im)
    (hwR : |w.re| ≤ R) (haL : ∀ i ∈ distSetL xL, aL i ≤ -R - d) (haR : ∀ i ∈ distSetR xR, R + d ≤ aR i) :
    |distantHarm κ xL xR ρL ρR aL aR w| ≤
      |1 / Real.sqrt κ| * ((∑ i ∈ distSetL xL, |ρL i|) + ∑ i ∈ distSetR xR, |ρR i|) *
        (Real.pi / 2 * (w.im / d)) := by
  have hπ := Real.pi_pos
  have hL : ∀ i ∈ distSetL xL, |Complex.arg (w - aL i)| ≤ Real.pi / 2 * (w.im / d) := fun i hi => by
    have hre : d ≤ (w - aL i).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; linarith [haL i hi, (abs_le.1 hwR).1]
    have hne : w - aL i ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre; linarith
    refine (abs_arg_le_of_re_nonneg (by linarith) hne).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hn : d ≤ ‖w - aL i‖ := hre.trans (Complex.re_le_norm _)
    rw [show (w - aL i).im = w.im by simp, abs_of_pos hw]
    exact div_le_div_of_nonneg_left hw.le hd hn
  have hR : ∀ i ∈ distSetR xR, |Real.pi - Complex.arg (w - aR i)| ≤ Real.pi / 2 * (w.im / d) := fun i hi => by
    have him : ((aR i : ℂ) - w).im < 0 := by simp [hw]
    have harg : Complex.arg (w - aR i) = Complex.arg ((aR i : ℂ) - w) + Real.pi := by
      rw [← Complex.arg_neg_eq_arg_add_pi_of_im_neg him, neg_sub]
    have hre : d ≤ ((aR i : ℂ) - w).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; linarith [haR i hi, (abs_le.1 hwR).2]
    have hne : (aR i : ℂ) - w ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre; linarith
    rw [harg, show Real.pi - (Complex.arg ((aR i : ℂ) - w) + Real.pi) = -Complex.arg ((aR i : ℂ) - w) by ring,
      abs_neg]
    refine (abs_arg_le_of_re_nonneg (by linarith) hne).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hn : d ≤ ‖(aR i : ℂ) - w‖ := hre.trans (Complex.re_le_norm _)
    rw [show ((aR i : ℂ) - w).im = -w.im by simp, abs_neg, abs_of_pos hw]
    exact div_le_div_of_nonneg_left hw.le hd hn
  have he : distantHarm κ xL xR ρL ρR aL aR w = 1 / Real.sqrt κ * ((∑ i ∈ distSetR xR, ρR i *
      (Real.pi - Complex.arg (w - aR i))) - ∑ i ∈ distSetL xL, ρL i * Complex.arg (w - aL i)) := by
    simp only [distantHarm, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  rw [he, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_sub (∑ i ∈ distSetR xR, ρR i * (Real.pi - Complex.arg (w - aR i)))
    (∑ i ∈ distSetL xL, ρL i * Complex.arg (w - aL i))).trans ?_
  have h1 : |∑ i ∈ distSetR xR, ρR i * (Real.pi - Complex.arg (w - aR i))| ≤
      (∑ i ∈ distSetR xR, |ρR i|) * (Real.pi / 2 * (w.im / d)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hR i hi) (abs_nonneg _)
  have h2 : |∑ i ∈ distSetL xL, ρL i * Complex.arg (w - aL i)| ≤
      (∑ i ∈ distSetL xL, |ρL i|) * (Real.pi / 2 * (w.im / d)) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hL i hi) (abs_nonneg _)
  linarith

/-- The modulus of `Im(2/f)` is at most `2 Im f / (Re f)²`. -/
theorem abs_im_two_div_le_of_re {f : ℂ} (hf : 0 < f.im) {a : ℝ} (ha : 0 < a) (hre : a ≤ |f.re|) :
    |(2 / f).im| ≤ 2 * f.im / a ^ 2 := by
  have hns : 0 < Complex.normSq f := Complex.normSq_pos.2 fun h => by rw [h, Complex.zero_im] at hf; linarith
  have hsq : a ^ 2 ≤ Complex.normSq f := by
    rw [Complex.normSq_apply]
    have : a ^ 2 ≤ f.re ^ 2 := by rw [← sq_abs f.re]; exact pow_le_pow_left₀ ha.le hre 2
    nlinarith [sq_nonneg f.im]
  rw [im_two_div, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * f.im), abs_of_pos hns]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq

theorem abs_im_two_div_le_of_norm {f : ℂ} {a : ℝ} (ha : 0 < a) (hn : a ≤ ‖f‖) : |(2 / f).im| ≤ 2 / a := by
  have hpos : 0 < ‖f‖ := lt_of_lt_of_le ha hn
  calc |(2 / f).im| ≤ ‖2 / f‖ := Complex.abs_im_le_norm _
    _ = 2 / ‖f‖ := by rw [norm_div]; simp
    _ ≤ 2 / a := div_le_div_of_nonneg_left zero_le_two ha hn

/-- **Far points stay far**: for `|y| ≥ r` alive through the regime, `|f_u(y)| ≥ |y|/4`. -/
theorem IsLocalRegime.norm_div_four_le (h : IsLocalRegime W r T) {y : ℂ} (hy : y ∈ H \ fwdHull W T)
    (hyn : r ≤ ‖y‖) {u : ℝ} (hu : u ∈ Icc 0 T) : ‖y‖ / 4 ≤ ‖fwdMap W u y‖ := by
  have hr := h.r_pos
  rcases le_or_gt (‖y‖ / 2) |y.re| with hre | hre
  · rcases le_or_gt 0 y.re with h0 | h0
    · rw [abs_of_nonneg h0] at hre
      have := le_re_fwdMap_of_le_re h.cont h.T_nonneg hy h.bound (δ := ‖y‖ / 4) (by linarith) (by linarith) hu
      exact this.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    · rw [abs_of_neg h0] at hre
      have := re_fwdMap_le_of_re_le h.cont h.T_nonneg hy h.bound (δ := ‖y‖ / 4) (by linarith) (by linarith) hu
      exact (by linarith : ‖y‖ / 4 ≤ -(fwdMap W u y).re).trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  · have hnsq : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hre2 : y.re ^ 2 < (‖y‖ / 2) ^ 2 := by
      have := abs_lt.1 hre; nlinarith [norm_nonneg y]
    have hbar := sq_im_le_sq_im_fwdMap h.cont h.T_nonneg hy hu
    have hu5 : 5 * u ≤ 5 * (r ^ 2 / 64) := by linarith [hu.2, h.T_le]
    have hr2 : r ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hr.le hyn 2
    have him : ‖y‖ / 4 ≤ (fwdMap W u y).im := by
      have hpos := Ito.im_fwdMap_pos h.cont h.T_nonneg hy hu
      nlinarith [norm_nonneg y]
    exact him.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))

theorem im_fwdMap_le_im (h : IsLocalRegime W r T) {y : ℂ} (hy : y ∈ H \ fwdHull W T) {u : ℝ}
    (hu : u ∈ Icc 0 T) : (fwdMap W u y).im ≤ y.im := by
  have hanti := (QuantumZipper.im_isForwardSol_le h.cont hy.1
    (Ito.isForwardSol_fwdMap_of_mem h.cont h.T_nonneg hy)).1 ⟨le_rfl, h.T_nonneg⟩ hu hu.1
  have h0 : (fwdMap W 0 y).im = y.im := by
    rw [Ito.fwdMap_eq_sub_add_integral h.cont h.T_nonneg hy ⟨le_rfl, h.T_nonneg⟩]
    simp
  beta_reduce at hanti
  rwa [h0] at hanti

/-- **`D_s` near the real line away from the seed**: `|D_s(y)| ≤ s C (32/r²) Im y` for `|Re y| ≥ r/2`. -/
theorem abs_dFun_le_of_re (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) (hre : r / 2 ≤ |y.re|) {C : ℝ}
    (hC : ∀ u ∈ Icc (0 : ℝ) T, |driftGap κ xL xR ρL ρR r W VL VR u| ≤ C) :
    |dFun κ xL xR ρL ρR r W VL VR s y| ≤ C * (32 * y.im / r ^ 2) * s := by
  have hr := h.r_pos
  have hsr := h.mono hs
  have hb : ∀ u ∈ Ι (0 : ℝ) s, ‖(2 / fwdMap W u y).im * driftGap κ xL xR ρL ρR r W VL VR u‖ ≤
      C * (32 * y.im / r ^ 2) := by
    intro u hu
    rw [uIoc_of_le hs.1] at hu
    have huI : u ∈ Icc 0 s := Ioc_subset_Icc_self hu
    have him := Ito.im_fwdMap_pos h.cont hs.1 hy huI
    have hre' : r / 4 ≤ |(fwdMap W u y).re| := by
      rcases le_or_gt 0 y.re with h0 | h0
      · rw [abs_of_nonneg h0] at hre
        exact (le_re_fwdMap_of_le_re h.cont hs.1 hy hsr.bound (δ := r / 4) (by linarith) (by linarith)
          huI).trans (le_abs_self _)
      · rw [abs_of_neg h0] at hre
        have := re_fwdMap_le_of_re_le h.cont hs.1 hy hsr.bound (δ := r / 4) (by linarith) (by linarith) huI
        exact (by linarith : r / 4 ≤ -(fwdMap W u y).re).trans (neg_le_abs _)
    have h1 := abs_im_two_div_le_of_re him (by linarith) hre'
    have h2 := im_fwdMap_le_im hsr hy huI
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC u ⟨huI.1, huI.2.trans hs.2⟩)
    calc |driftGap κ xL xR ρL ρR r W VL VR u| * |(2 / fwdMap W u y).im|
        ≤ C * (2 * (fwdMap W u y).im / (r / 4) ^ 2) :=
          mul_le_mul (hC u ⟨huI.1, huI.2.trans hs.2⟩) h1 (abs_nonneg _) hC0
      _ ≤ C * (32 * y.im / r ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          rw [show (r / 4) ^ 2 = r ^ 2 / 16 by ring, div_div_eq_mul_div]
          rw [div_le_div_iff_of_pos_right (by positivity)]
          linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at this

/-- **`D_s` at `∞`**: `|D_s(y)| ≤ s C (8/|y|)` for `|y| ≥ r`. -/
theorem abs_dFun_le_of_le_norm (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) (hyn : r ≤ ‖y‖) {C : ℝ}
    (hC : ∀ u ∈ Icc (0 : ℝ) T, |driftGap κ xL xR ρL ρR r W VL VR u| ≤ C) :
    |dFun κ xL xR ρL ρR r W VL VR s y| ≤ C * (8 / ‖y‖) * s := by
  have hr := h.r_pos
  have hsr := h.mono hs
  have hb : ∀ u ∈ Ι (0 : ℝ) s, ‖(2 / fwdMap W u y).im * driftGap κ xL xR ρL ρR r W VL VR u‖ ≤
      C * (8 / ‖y‖) := by
    intro u hu
    rw [uIoc_of_le hs.1] at hu
    have huI : u ∈ Icc 0 s := Ioc_subset_Icc_self hu
    have h1 := abs_im_two_div_le_of_norm (by linarith : 0 < ‖y‖ / 4) (hsr.norm_div_four_le hy hyn huI)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC u ⟨huI.1, huI.2.trans hs.2⟩)
    calc |driftGap κ xL xR ρL ρR r W VL VR u| * |(2 / fwdMap W u y).im| ≤ C * (2 / (‖y‖ / 4)) :=
          mul_le_mul (hC u ⟨huI.1, huI.2.trans hs.2⟩) h1 (abs_nonneg _) hC0
      _ = C * (8 / ‖y‖) := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at this

/-- The constant of the bound near the seed. -/
def seedConst (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) : ℝ :=
  14 / r * (∫ z, |vSrc κ xL xR ρL ρR r z|) + |1 / Real.sqrt κ| * ((∑ i ∈ distSetL xL, |ρL i|) +
    ∑ i ∈ distSetR xR, |ρR i|) * (Real.pi / 2 * (4 / (21 * r)))

/-- **The Green potential near the seed**: `|G_{ℍ∖K_s} v (y)| ≤ (14/r) (∫|v|) Im f_s(y)` for `|y| ≤ r`. -/
theorem abs_greenPot_le (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ} (hy : y ∈ H \ fwdHull W s) (hyn : ‖y‖ ≤ r) :
    |greenPot κ xL xR ρL ρR r W s y| ≤ 14 / r * (∫ z, |vSrc κ xL xR ρL ρR r z|) * (fwdMap W s y).im := by
  have hr0 := h.r_pos
  have hsr := h.mono hs
  have hfy := hsr.norm_fwdMap_le_of_norm_le hy hyn ⟨hs.1, le_rfl⟩
  have hyim := Ito.im_fwdMap_pos h.cont hs.1 hy ⟨hs.1, le_rfl⟩
  have hb : ∀ z, ‖greenH (fwdMap W s y) (fwdMap W s z) * vSrc κ xL xR ρL ρR r z‖ ≤
      14 / r * (fwdMap W s y).im * |vSrc κ xL xR ρL ρR r z| := by
    intro z
    by_cases hz : vSrc κ xL xR ρL ρR r z = 0
    · simp [hz]
    obtain ⟨hzS, hz6, hz7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hz
    have hzs : z ∈ H \ fwdHull W s := hsr.mem_of_lt_norm hzS.1 hzS.2
    have hfz := hsr.le_norm_fwdMap_src hzS.1 hz6 ⟨hs.1, le_rfl⟩
    have hzim := Ito.im_fwdMap_pos h.cont hs.1 hzs ⟨hs.1, le_rfl⟩
    have hsep : r ≤ ‖fwdMap W s y - fwdMap W s z‖ := by
      have := norm_sub_norm_le (fwdMap W s z) (fwdMap W s y)
      rw [norm_sub_rev] at this
      linarith
    have hne : fwdMap W s y ≠ fwdMap W s z := fun he => by rw [he, sub_self, norm_zero] at hsep; linarith
    have hG0 : 0 ≤ greenH (fwdMap W s y) (fwdMap W s z) :=
      QuantumZipper.greenH_nonneg hyim.le hzim.le hne
    have hG := QuantumZipper.K3.greenH_le_im_mul_im hyim hzim hne
    have hzim7 : (fwdMap W s z).im ≤ 7 * r :=
      (im_fwdMap_le_im hsr hzs ⟨hs.1, le_rfl⟩).trans ((le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hz7))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hG0]
    refine mul_le_mul_of_nonneg_right (hG.trans ?_) (abs_nonneg _)
    have hsq : r ^ 2 ≤ ‖fwdMap W s y - fwdMap W s z‖ ^ 2 := pow_le_pow_left₀ hr0.le hsep 2
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hsq)]
    have : 14 / r * (fwdMap W s y).im * ‖fwdMap W s y - fwdMap W s z‖ ^ 2 ≥
        14 / r * (fwdMap W s y).im * r ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : 14 / r * (fwdMap W s y).im * r ^ 2 = 14 * r * (fwdMap W s y).im := by field_simp
    nlinarith
  have := norm_integral_le_of_norm_le ((integrable_vSrc hF hr).abs.const_mul (14 / r * (fwdMap W s y).im))
    (ae_of_all _ hb)
  rw [Real.norm_eq_abs, integral_const_mul] at this
  simp only [greenPot]
  linarith

/-- **`D_s` near the seed and the hull**: `|D_s(y)| ≤ C Im f_s(y)` for `|y| ≤ r` (there `f = q`, and both the Green
potential and `q_s` vanish on the boundary in the half-plane coordinate). -/
theorem abs_dFun_le_of_norm_le (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) (hyn : ‖y‖ ≤ r) :
    |dFun κ xL xR ρL ρR r W VL VR s y| ≤ seedConst κ xL xR ρL ρR r * (fwdMap W s y).im := by
  have hr0 := h.r_pos
  have hsr := h.mono hs
  have hfy := hsr.norm_fwdMap_le_of_norm_le hy hyn ⟨hs.1, le_rfl⟩
  have hyim := Ito.im_fwdMap_pos h.cont hs.1 hy ⟨hs.1, le_rfl⟩
  rw [dFun_eq h hF hr hD hs hy, fCut_eq_qExt hr0 (by linarith), sub_add_cancel]
  have hG := abs_greenPot_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hs hy hyn
  have hq : |qAt κ xL xR ρL ρR W VL VR s y| ≤ |1 / Real.sqrt κ| * ((∑ i ∈ distSetL xL, |ρL i|) +
      ∑ i ∈ distSetR xR, |ρR i|) * (Real.pi / 2 * ((fwdMap W s y).im / (21 * r / 4))) := by
    refine abs_distantHarm_le (R := 7 * r / 4) (by linarith) hyim
      ((Complex.abs_re_le_norm _).trans hfy) (fun i hi => ?_) (fun i hi => ?_)
    · have h1 := hD.leftL i hi s hs
      have h2 := (hD.markL i hi).sep s hs
      rw [abs_of_nonpos (by linarith)] at h2
      linarith
    · have h1 := hD.rightR i hi s hs
      have h2 := (hD.markR i hi).sep s hs
      rw [abs_of_nonneg (by linarith)] at h2
      linarith
  have e : Real.pi / 2 * ((fwdMap W s y).im / (21 * r / 4)) = Real.pi / 2 * (4 / (21 * r)) *
      (fwdMap W s y).im := by field_simp
  rw [e] at hq
  calc |greenPot κ xL xR ρL ρR r W s y - qAt κ xL xR ρL ρR W VL VR s y|
      ≤ |greenPot κ xL xR ρL ρR r W s y| + |qAt κ xL xR ρL ρR W VL VR s y| := abs_sub _ _
    _ ≤ seedConst κ xL xR ρL ρR r * (fwdMap W s y).im := by
        simp only [seedConst]
        nlinarith [hG, hq]

/-- **Properness of the Loewner map at the hull**: `Im f_s(y) → 0` as `y → y₀ ∈ K_s` within `ℍ ∖ K_s`. -/
theorem tendsto_im_fwdMap_of_mem_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {y₀ : ℂ}
    (hy₀ : y₀ ∈ fwdHull W s) :
    Tendsto (fun y => (fwdMap W s y).im) (𝓝[H \ fwdHull W s] y₀) (𝓝 0) := by
  obtain ⟨hz, σ, hσs, hsw, hinf⟩ := (QuantumZipper.FwdClock.mem_fwdHull_iff_inf_im hW).1 hy₀
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, ht0, htσ, hlt⟩ := hinf ε hε
  have hy₀t : y₀ ∈ H \ fwdHull W t := QuantumZipper.RS.mem_compl_fwdHull_iff.2
    ⟨hz, by rw [hsw]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htσ⟩
  have hopen := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht0
  have hcont : ContinuousAt (fwdMap W t) y₀ :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht0).differentiableAt (hopen.mem_nhds hy₀t)).continuousAt
  have hev : ∀ᶠ y in 𝓝 y₀, (fwdMap W t y).im < ε :=
    (Complex.continuous_im.continuousAt.comp hcont).eventually (gt_mem_nhds hlt)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hyε hy
  have hts : t ≤ s := htσ.le.trans hσs
  have hpos := Ito.im_fwdMap_pos hW hs hy ⟨hs, le_rfl⟩
  have hanti := (QuantumZipper.im_isForwardSol_le hW hy.1 (Ito.isForwardSol_fwdMap_of_mem hW hs hy)).1
    ⟨ht0, hts⟩ ⟨hs, le_rfl⟩ hts
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  exact lt_of_le_of_lt hanti hyε

/-! ### `D_s` is the imaginary part of a holomorphic function -/

variable (κ xL xR ρL ρR r W VL VR) in
/-- `Φ_s(y) = ∫₀ˢ 2(E(u) − A(u))/f_u(y) du`, holomorphic on `ℍ ∖ K_s`, with `Im Φ_s = D_s`. -/
def phiFun (s : ℝ) (y : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..s, 2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) / fwdMap W u y

theorem dFun_eq_im_phiFun (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ} (hy : y ∈ H \ fwdHull W s) :
    dFun κ xL xR ρL ρR r W VL VR s y = (phiFun κ xL xR ρL ρR r W VL VR s y).im := by
  have hc := (continuousOn_driftGap (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD).mono (Icc_subset_Icc_right hs.2)
  have hcont : ContinuousOn (fun u => 2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) / fwdMap W u y) (Icc 0 s) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).div
      (Ito.continuousOn_fwdMap_time' h.cont hs.1 hy) fun u hu => Ito.fwdMap_ne_zero h.cont hs.1 hy hu
  rw [phiFun, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    (hcont.intervalIntegrable_of_Icc hs.1), dFun]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Complex.imCLM_apply]
  rw [show 2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) / fwdMap W u y =
    (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) * (2 / fwdMap W u y) by ring, Complex.im_ofReal_mul]
  ring

/-- **`Φ_s` is holomorphic on `ℍ ∖ K_s`** (differentiation under the integral: on a closed disc around a point of
`ℍ ∖ K_s`, `Im f_u ≥ Im f_s ≥ δ > 0` for `u ≤ s`, so the `y`-derivative `−2c(u) f_u'(y)/f_u(y)²` is bounded). -/
theorem differentiableOn_phiFun (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    DifferentiableOn ℂ (phiFun κ xL xR ρL ρR r W VL VR s) (H \ fwdHull W s) := by
  intro y₀ hy₀
  have hs0 := hs.1
  have hopen := QuantumZipper.FwdHolo.isOpen_compl_fwdHull h.cont hs0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen y₀ hy₀
  set B := closedBall y₀ (ρ / 2) with hB
  have hBsub : B ⊆ H \ fwdHull W s := (closedBall_subset_ball (by linarith)).trans hball
  -- a uniform lower bound for `Im f_s` on the disc
  have hcont_im : ContinuousOn (fun y => (fwdMap W s y).im) B :=
    Complex.continuous_im.comp_continuousOn
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap h.cont hs0).continuousOn.mono hBsub)
  obtain ⟨y₁, hy₁B, hy₁⟩ := (isCompact_closedBall y₀ (ρ / 2)).exists_isMinOn
    ⟨y₀, mem_closedBall_self (by linarith)⟩ hcont_im
  set δ := (fwdMap W s y₁).im with hδ
  have hδpos : 0 < δ := Ito.im_fwdMap_pos h.cont hs0 (hBsub hy₁B) ⟨hs0, le_rfl⟩
  have hlow : ∀ y ∈ B, ∀ u ∈ Icc (0 : ℝ) s, δ ≤ ‖fwdMap W u y‖ := fun y hy u hu => by
    have h1 : δ ≤ (fwdMap W s y).im := hy₁ hy
    have hanti := (QuantumZipper.im_isForwardSol_le h.cont (hBsub hy).1
      (Ito.isForwardSol_fwdMap_of_mem h.cont hs0 (hBsub hy))).1 hu ⟨hs0, le_rfl⟩ hu.2
    exact h1.trans (hanti.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _)))
  obtain ⟨Cc, hCc0, hCc⟩ := exists_abs_driftGap_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD
  have hc := (continuousOn_driftGap (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD).mono (Icc_subset_Icc_right hs.2)
  -- the integrand and its derivative
  let F : ℂ → ℝ → ℂ := fun y u => 2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) / fwdMap W u y
  let F' : ℂ → ℝ → ℂ := fun y u => -(2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) *
    Complex.exp (QuantumZipper.logDerivFwd W u y) / fwdMap W u y ^ 2)
  have hIoc : Ι (0 : ℝ) s = Ioc 0 s := uIoc_of_le hs0
  have hFc : ∀ y ∈ H \ fwdHull W s, ContinuousOn (F y) (Icc 0 s) := fun y hy =>
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).div
      (Ito.continuousOn_fwdMap_time' h.cont hs0 hy) fun u hu => Ito.fwdMap_ne_zero h.cont hs0 hy hu
  have hF'c : ContinuousOn (F' y₀) (Icc 0 s) :=
    (((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).mul
      (Complex.continuous_exp.comp_continuousOn (Ito.continuousOn_logDerivFwd h.cont hs0 hy₀))).div
      ((Ito.continuousOn_fwdMap_time' h.cont hs0 hy₀).pow 2) fun u hu =>
        pow_ne_zero 2 (Ito.fwdMap_ne_zero h.cont hs0 hy₀ hu)).neg
  have hmeas : ∀ {g : ℝ → ℂ}, ContinuousOn g (Icc 0 s) →
      AEStronglyMeasurable g (volume.restrict (Ι (0 : ℝ) s)) := fun hg => by
    rw [hIoc]; exact (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  -- the bound on the derivative
  set K := 2 * Cc * Real.exp (2 * s / δ ^ 2) / δ ^ 2 with hK
  have hbound : ∀ᵐ u ∂(volume.restrict (Ι (0 : ℝ) s)), ∀ y ∈ B, ‖F' y u‖ ≤ K := by
    rw [hIoc]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu y hy => ?_)
    have huI : u ∈ Icc 0 s := Ioc_subset_Icc_self hu
    have hyu := Ito.mem_diff_fwdHull_of_le (hBsub hy) huI.2
    have hfn := hlow y hy u huI
    have hL : ‖QuantumZipper.logDerivFwd W u y‖ ≤ 2 * s / δ ^ 2 := by
      rw [QuantumZipper.logDerivFwd, norm_neg]
      have hb : ∀ r ∈ Ι (0 : ℝ) u, ‖2 / fwdMap W r y ^ 2‖ ≤ 2 / δ ^ 2 := fun r hr => by
        rw [uIoc_of_le huI.1] at hr
        have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.trans huI.2⟩
        rw [norm_div, norm_pow]
        simp only [Complex.norm_ofNat]
        exact div_le_div_of_nonneg_left zero_le_two (by positivity)
          (pow_le_pow_left₀ hδpos.le (hlow y hy r hrI) 2)
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [sub_zero, abs_of_nonneg huI.1] at this
      have hus : 2 / δ ^ 2 * u ≤ 2 / δ ^ 2 * s := mul_le_mul_of_nonneg_left huI.2 (by positivity)
      calc ‖∫ r in (0 : ℝ)..u, 2 / fwdMap W r y ^ 2‖ ≤ 2 / δ ^ 2 * u := this
        _ ≤ 2 / δ ^ 2 * s := hus
        _ = 2 * s / δ ^ 2 := by ring
    have hexp : ‖Complex.exp (QuantumZipper.logDerivFwd W u y)‖ ≤ Real.exp (2 * s / δ ^ 2) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans hL)
    show ‖-(2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) *
      Complex.exp (QuantumZipper.logDerivFwd W u y) / fwdMap W u y ^ 2)‖ ≤ K
    simp only [norm_neg, norm_div, norm_mul, norm_pow]
    have h2c : ‖(2 : ℂ)‖ * ‖(driftGap κ xL xR ρL ρR r W VL VR u : ℂ)‖ ≤ 2 * Cc := by
      rw [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hCc u ⟨huI.1, huI.2.trans hs.2⟩) zero_le_two
    calc ‖(2 : ℂ)‖ * ‖(driftGap κ xL xR ρL ρR r W VL VR u : ℂ)‖ *
          ‖Complex.exp (QuantumZipper.logDerivFwd W u y)‖ / ‖fwdMap W u y‖ ^ 2
        ≤ 2 * Cc * Real.exp (2 * s / δ ^ 2) / δ ^ 2 := by
          gcongr
      _ = K := rfl
  have hdiff : ∀ᵐ u ∂(volume.restrict (Ι (0 : ℝ) s)), ∀ y ∈ B, HasDerivAt (F · u) (F' y u) y := by
    rw [hIoc]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu y hy => ?_)
    have huI : u ∈ Icc 0 s := Ioc_subset_Icc_self hu
    have hyu := Ito.mem_diff_fwdHull_of_le (hBsub hy) huI.2
    have hd := QuantumZipper.FwdHolo.hasDerivAt_fwdMap h.cont huI.1 hyu
    have hne := Ito.fwdMap_ne_zero h.cont huI.1 hyu ⟨huI.1, le_rfl⟩
    have := (hasDerivAt_const y (2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ))).div hd hne
    refine this.congr_deriv ?_
    show _ = -(2 * (driftGap κ xL xR ρL ρR r W VL VR u : ℂ) *
      Complex.exp (QuantumZipper.logDerivFwd W u y) / fwdMap W u y ^ 2)
    ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ι (0 : ℝ) s))
    (F := F) (F' := F') (x₀ := y₀) (bound := fun _ => K) (closedBall_mem_nhds y₀ (by linarith))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ hρ) fun y hy => hmeas (hFc y (hball hy))) ?_
    (hmeas hF'c) hbound ?_ hdiff
  · have heq : phiFun κ xL xR ρL ρR r W VL VR s = fun y => ∫ u, F y u ∂(volume.restrict (Ι (0 : ℝ) s)) := by
      funext y
      rw [phiFun, intervalIntegral.integral_of_le hs0, hIoc]
    rw [heq]
    exact hres.2.differentiableAt.differentiableWithinAt
  · rw [hIoc]; exact (hFc y₀ hy₀).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) s)) := by
      rw [hIoc]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    exact integrable_const K

theorem continuousOn_dFun (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ContinuousOn (dFun κ xL xR ρL ρR r W VL VR s) (H \ fwdHull W s) :=
  (Complex.continuous_im.comp_continuousOn (differentiableOn_phiFun h hF hr hD hs).continuousOn).congr
    fun _ hy => dFun_eq_im_phiFun h hF hr hD hs hy

/-! ### (HL6): `D_s = 0` -/

/-- **`D_s → 0` at every boundary point of `ℍ ∖ K_s`**: real points away from the seed (first representation),
real points near the seed and points of the hull (second representation and properness). -/
theorem tendsto_dFun_of_notMem (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y₀ : ℂ}
    (hy₀ : y₀ ∉ H \ fwdHull W s) :
    Tendsto (dFun κ xL xR ρL ρR r W VL VR s) (𝓝[H \ fwdHull W s] y₀) (𝓝 0) := by
  have hr0 := h.r_pos
  have hsr := h.mono hs
  obtain ⟨C, hC0, hC⟩ := exists_abs_driftGap_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD
  set Ω := H \ fwdHull W s with hΩ
  -- a squeeze by a bound tending to `0`
  have squeeze : ∀ g : ℂ → ℝ, Tendsto g (𝓝[Ω] y₀) (𝓝 0) →
      (∀ᶠ y in 𝓝[Ω] y₀, |dFun κ xL xR ρL ρR r W VL VR s y| ≤ g y) →
      Tendsto (dFun κ xL xR ρL ρR r W VL VR s) (𝓝[Ω] y₀) (𝓝 0) := fun g hg hb => by
    refine squeeze_zero_norm' (hb.mono fun y hy => ?_) hg
    rwa [Real.norm_eq_abs]
  rcases lt_trichotomy y₀.im 0 with hneg | hzero | hpos
  · -- below the real line: no nearby points of `Ω`
    have : 𝓝[Ω] y₀ = ⊥ := by
      rw [← Filter.not_neBot, ← mem_closure_iff_nhdsWithin_neBot]
      intro hcl
      have hsub : closure Ω ⊆ {z : ℂ | 0 ≤ z.im} :=
        closure_minimal (fun z hz => show 0 ≤ z.im from le_of_lt hz.1)
          (isClosed_le continuous_const Complex.continuous_im)
      exact absurd (hsub hcl) (not_le.2 hneg)
    rw [this]; exact tendsto_bot
  · -- a real point
    have him : Tendsto (fun y : ℂ => y.im) (𝓝[Ω] y₀) (𝓝 0) := by
      rw [← hzero]; exact (Complex.continuous_im.tendsto y₀).mono_left nhdsWithin_le_nhds
    rcases lt_or_ge ‖y₀‖ r with hn | hn
    · refine squeeze (fun y => seedConst κ xL xR ρL ρR r * y.im) (by simpa using him.const_mul _) ?_
      have hev : ∀ᶠ y in 𝓝 y₀, ‖y‖ < r := (continuous_norm.tendsto y₀).eventually (gt_mem_nhds hn)
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hyn hy
      refine (abs_dFun_le_of_norm_le h hF hr hD hs hy hyn.le).trans ?_
      have hsc : 0 ≤ seedConst κ xL xR ρL ρR r := by
        have := (abs_nonneg _).trans (abs_dFun_le_of_norm_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD hs hy
          hyn.le)
        exact nonneg_of_mul_nonneg_left this (Ito.im_fwdMap_pos h.cont hs.1 hy ⟨hs.1, le_rfl⟩)
      exact mul_le_mul_of_nonneg_left (im_fwdMap_le_im hsr hy ⟨hs.1, le_rfl⟩) hsc
    · have hre : r ≤ |y₀.re| := by
        have : ‖y₀‖ = |y₀.re| := by
          rw [← Complex.re_add_im y₀, hzero]; simp
        rw [← this]; exact hn
      have hg : Tendsto (fun y : ℂ => C * (32 * y.im / r ^ 2) * s) (𝓝[Ω] y₀) (𝓝 0) := by
        have := (((him.const_mul 32).div_const (r ^ 2)).const_mul C).mul_const s
        simpa using this
      refine squeeze (fun y => C * (32 * y.im / r ^ 2) * s) hg ?_
      have hev : ∀ᶠ y in 𝓝 y₀, r / 2 < |y.re| :=
        (Complex.continuous_re.abs.tendsto y₀).eventually (lt_mem_nhds (by linarith))
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hyre hy
      exact abs_dFun_le_of_re h hs hy hyre.le hC
  · -- a point of the hull
    have hK : y₀ ∈ fwdHull W s := by
      by_contra hn; exact hy₀ ⟨hpos, hn⟩
    have hn : ‖y₀‖ < r := by
      have := hsr.fwdHull_subset hK
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    have hprop := tendsto_im_fwdMap_of_mem_fwdHull h.cont hs.1 hK
    refine squeeze (fun y => seedConst κ xL xR ρL ρR r * (fwdMap W s y).im)
      (by simpa using hprop.const_mul (seedConst κ xL xR ρL ρR r)) ?_
    have hev : ∀ᶠ y in 𝓝 y₀, ‖y‖ < r := (continuous_norm.tendsto y₀).eventually (gt_mem_nhds hn)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hyn hy
    exact abs_dFun_le_of_norm_le h hF hr hD hs hy hyn.le

/-- The superlevel sets `{|D_s| ≥ ε}` are compact subsets of `ℍ ∖ K_s`. -/
theorem isCompact_superlevel (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) {ε : ℝ}
    (hε : 0 < ε) :
    IsCompact {y | y ∈ H \ fwdHull W s ∧ ε ≤ |dFun κ xL xR ρL ρR r W VL VR s y|} := by
  have hr0 := h.r_pos
  obtain ⟨C, hC0, hC⟩ := exists_abs_driftGap_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD
  set K := {y | y ∈ H \ fwdHull W s ∧ ε ≤ |dFun κ xL xR ρL ρR r W VL VR s y|} with hK
  set R := max r (C * 8 * s / ε + 1) with hR
  refine Metric.isCompact_of_isClosed_isBounded ?_ ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_)
  · refine isClosed_of_closure_subset fun y hy => ?_
    have hne : (𝓝[K] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
    have hKΩ : K ⊆ H \ fwdHull W s := fun z hz => hz.1
    by_cases hyΩ : y ∈ H \ fwdHull W s
    · refine ⟨hyΩ, ?_⟩
      have hc : Tendsto (fun z => |dFun κ xL xR ρL ρR r W VL VR s z|) (𝓝[K] y)
          (𝓝 |dFun κ xL xR ρL ρR r W VL VR s y|) :=
        (((continuousOn_dFun h hF hr hD hs).continuousAt
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull h.cont hs.1).mem_nhds hyΩ)).abs.tendsto).mono_left
            nhdsWithin_le_nhds
      exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun z hz => hz.2)
    · have ht := (tendsto_dFun_of_notMem (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD hs hyΩ).mono_left
        (nhdsWithin_mono _ hKΩ)
      have hev := ht.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < ε by simpa using hε))
      have hev2 : ∀ᶠ z in 𝓝[K] y, ε ≤ |dFun κ xL xR ρL ρR r W VL VR s z| :=
        eventually_nhdsWithin_of_forall fun z hz => hz.2
      obtain ⟨z, hz1, hz2⟩ := (hev.and hev2).exists
      exact absurd hz2 (not_le.2 hz1)
  · intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra hn
    rw [not_le] at hn
    have hry : r ≤ ‖y‖ := (le_max_left _ _).trans hn.le
    have hb := abs_dFun_le_of_le_norm h hs hy.1 hry hC
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hr0 hry
    have h1 : C * (8 / ‖y‖) * s < ε := by
      have hlt : C * 8 * s / ε + 1 < ‖y‖ := (le_max_right _ _).trans_lt hn
      rw [show C * (8 / ‖y‖) * s = C * 8 * s / ‖y‖ by ring, div_lt_iff₀ hy0]
      have : C * 8 * s / ε < ‖y‖ := by linarith
      rw [div_lt_iff₀ hε] at this
      linarith
    linarith [hy.2]

/-- **(HL6)**: `D_s = 0` on `ℍ ∖ K_s`, i.e. `G_{ℍ∖K_s} v = f − q + q_s` there. The function `D_s ∘ F_s` (with
`F_s = f_s⁻¹`) is a bounded harmonic function on `ℍ` with boundary value `0` at every real point (QuantumZipper's
inverse Loewner map; the bounded harmonic uniqueness of the companion theorem). -/
theorem dFun_eq_zero (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hD : HasDistantMarks xL xR W VL VR r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ} (hy : y ∈ H \ fwdHull W s) :
    dFun κ xL xR ρL ρR r W VL VR s y = 0 := by
  have hr0 := h.r_pos
  have hs0 := hs.1
  have hsr := h.mono hs
  obtain ⟨C, hC0, hC⟩ := exists_abs_driftGap_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD
  set Fs := QuantumZipper.fwdMapInv W s with hFs
  set Dt : ℂ → ℝ := fun w => dFun κ xL xR ρL ρR r W VL VR s (Fs w) with hDt
  have hFsΩ : ∀ w ∈ H, Fs w ∈ H \ fwdHull W s := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull h.cont h.zero hs0 hw
  -- harmonic
  have hharm : InnerProductSpace.HarmonicOnNhd Dt H := by
    intro w hw
    have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
    have hd : DifferentiableOn ℂ (fun w => phiFun κ xL xR ρL ρR r W VL VR s (Fs w)) H :=
      (differentiableOn_phiFun h hF hr hD hs).comp
        (QuantumZipper.RS.differentiableOn_fwdMapInv h.cont h.zero hs0) fun w hw => hFsΩ w hw
    have ha := (hd.analyticAt (hHo.mem_nhds hw)).harmonicAt_im
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 ha
    filter_upwards [hHo.mem_nhds hw] with w' hw'
    exact (dFun_eq_im_phiFun h hF hr hD hs (hFsΩ w' hw')).symm
  -- bounded
  have hbdd : ∃ M : ℝ, ∀ w ∈ H, |Dt w| ≤ M := by
    refine ⟨max (seedConst κ xL xR ρL ρR r * r) (C * (8 / r) * s), fun w hw => ?_⟩
    have hyΩ := hFsΩ w hw
    rcases le_or_gt ‖Fs w‖ r with hn | hn
    · refine (abs_dFun_le_of_norm_le h hF hr hD hs hyΩ hn).trans (le_max_of_le_left ?_)
      have hsc : 0 ≤ seedConst κ xL xR ρL ρR r := by
        have := (abs_nonneg _).trans (abs_dFun_le_of_norm_le (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD hs hyΩ hn)
        exact nonneg_of_mul_nonneg_left this (Ito.im_fwdMap_pos h.cont hs0 hyΩ ⟨hs0, le_rfl⟩)
      refine mul_le_mul_of_nonneg_left ?_ hsc
      exact (im_fwdMap_le_im hsr hyΩ ⟨hs0, le_rfl⟩).trans ((le_abs_self _).trans
        ((Complex.abs_im_le_norm _).trans hn))
    · refine (abs_dFun_le_of_le_norm h hs hyΩ hn.le hC).trans (le_max_of_le_right ?_)
      have hn0 : 0 < ‖Fs w‖ := hr0.trans hn
      have : 8 / ‖Fs w‖ ≤ 8 / r := div_le_div_of_nonneg_left (by norm_num) hr0 hn.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC0) hs0
  -- boundary values
  have hlim : ∀ x : ℝ, Tendsto Dt (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hKc := isCompact_superlevel (κ := κ) (ρL := ρL) (ρR := ρR) h hF hr hD hs (ε := ε / 2) (by linarith)
    set K := {y | y ∈ H \ fwdHull W s ∧ ε / 2 ≤ |dFun κ xL xR ρL ρR r W VL VR s y|} with hK
    have hfc : ContinuousOn (fwdMap W s) K :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap h.cont hs0).continuousOn).mono fun y hy => hy.1
    have hCc := hKc.image_of_continuousOn hfc
    have hx : (x : ℂ) ∉ fwdMap W s '' K := by
      rintro ⟨y, hy, hyx⟩
      have := Ito.im_fwdMap_pos h.cont hs0 hy.1 ⟨hs0, le_rfl⟩
      rw [hyx, Complex.ofReal_im] at this
      exact lt_irrefl 0 this
    filter_upwards [nhdsWithin_le_nhds (hCc.isClosed.isOpen_compl.mem_nhds hx), self_mem_nhdsWithin]
      with w hwC hw
    rw [Real.dist_eq, sub_zero]
    by_contra hge
    rw [not_lt] at hge
    refine hwC ⟨Fs w, ⟨hFsΩ w hw, by linarith⟩, ?_⟩
    exact QuantumZipper.RS.fwdMap_fwdMapInv h.cont h.zero hs0 hw
  have hDt : IsBoundedHarmonicExtension (fun _ => 0) ∅ Dt := ⟨hharm, hbdd, fun x _ => hlim x⟩
  have h0 : IsBoundedHarmonicExtension (fun _ => (0 : ℝ)) ∅ (fun _ => 0) :=
    ⟨fun w _ => ⟨contDiffAt_const, Filter.Eventually.of_forall fun _ => by
      simp [InnerProductSpace.laplacian_const]⟩, ⟨0, fun _ _ => by simp⟩, fun _ _ => tendsto_const_nhds⟩
  have heq := Impl.eqOn_of_isBoundedHarmonicExtension Set.finite_empty hDt h0
  have hfy : fwdMap W s y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap h.cont hs0 hy
  have := heq hfy
  have hinv : Fs (fwdMap W s y) = y := QuantumZipper.RS.fwdMapInv_fwdMap h.cont h.zero hs0 hy
  have hDty : Dt (fwdMap W s y) = dFun κ xL xR ρL ρR r W VL VR s y := by
    simp only [Dt, hinv]
  rw [hDty] at this
  exact this.symm

/-! ### (HL7): the source drift is the distant-force drift -/

/-- **(HL7)** (p. 249: "`a_t = κ^{-1/2} ∑_{j∈J} ρ_j/(W_t − V^j_t)`"): through the local regime, the source drift
`A(u) = ∫ Im(2/f_u(z)) v(z) dz` equals the distant-force drift `E(u)`. Proof: `D_s(y₁) = 0` for all `s` (HL6) at the
point `y₁ = 8r i`, alive through the regime; differentiating in `s` gives `Im(2/f_s(y₁)) (E(s) − A(s)) = 0`, and
`Im(2/f_s(y₁)) < 0`. -/
theorem srcDrift_eq_distDrift (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hD : HasDistantMarks xL xR W VL VR r T) (hT : 0 < T) {u : ℝ}
    (hu : u ∈ Icc 0 T) :
    srcDrift κ xL xR ρL ρR r W u = distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) := by
  have hr0 := h.r_pos
  set y₁ : ℂ := ((8 * r : ℝ) : ℂ) * Complex.I with hy₁
  have hy₁im : y₁.im = 8 * r := by simp [hy₁]
  have hy₁n : ‖y₁‖ = 8 * r := by
    rw [hy₁, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hy₁T : y₁ ∈ H \ fwdHull W T := h.mem_of_lt_norm (by rw [hy₁im]; linarith) (by rw [hy₁n]; linarith)
  set g : ℝ → ℝ := fun u => (2 / fwdMap W u y₁).im * driftGap κ xL xR ρL ρR r W VL VR u with hg
  have hgc : ContinuousOn g (Icc 0 T) :=
    (Complex.continuous_im.comp_continuousOn (continuousOn_const.div
      (Ito.continuousOn_fwdMap_time' h.cont h.T_nonneg hy₁T)
      fun u hu => Ito.fwdMap_ne_zero h.cont h.T_nonneg hy₁T hu)).mul (continuousOn_driftGap h hF hr hD)
  have h1 : HasDerivWithinAt (fun s => ∫ u in (0 : ℝ)..s, g u) (g u) (Icc 0 T) u :=
    hasDerivWithinAt_integral_Icc hgc hu
  have h2 : HasDerivWithinAt (fun s => ∫ u in (0 : ℝ)..s, g u) 0 (Icc 0 T) u := by
    refine (hasDerivWithinAt_const u (Icc 0 T) (0 : ℝ)).congr (fun s hs => ?_) ?_
    · exact dFun_eq_zero h hF hr hD hs (Ito.mem_diff_fwdHull_of_le hy₁T hs.2)
    · exact dFun_eq_zero h hF hr hD hu (Ito.mem_diff_fwdHull_of_le hy₁T hu.2)
  have hg0 : g u = 0 := (uniqueDiffOn_Icc hT u hu).eq_deriv _ h1 h2
  have him : (2 / fwdMap W u y₁).im ≠ 0 := by
    have hpos := Ito.im_fwdMap_pos h.cont h.T_nonneg hy₁T hu
    have hns : 0 < Complex.normSq (fwdMap W u y₁) :=
      Complex.normSq_pos.2 (Ito.fwdMap_ne_zero h.cont h.T_nonneg hy₁T hu)
    rw [im_two_div]
    exact (div_neg_of_neg_of_pos (by linarith) hns).ne
  have hc : driftGap κ xL xR ρL ρR r W VL VR u = 0 := (mul_eq_zero.1 hg0).resolve_left him
  simp only [driftGap, sub_eq_zero] at hc
  exact hc.symm

end Rep

end LocalExt

end InteractingSLE
