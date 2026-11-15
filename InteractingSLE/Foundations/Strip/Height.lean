/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Strip.Chain
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# The strip height bound (3.20)

Packet PROVE-ZHAN-A. Astra §3, "Simplicity and the strip height bound" (`ig1_formalization_proofs.txt`
L1323–L1335): for a strip Loewner point write `X + iY = ψ_t(z) − ξ_t`. Its height obeys

  `Y' = −sin Y/(cosh X − cos Y) ≥ −cot(Y/2)`,

so `U = cos(Y/2)` satisfies `U' ≤ U/2`. A point swallowed by time `t` must therefore have initial height at most
`H(t) = 2 arccos(e^{−t/2}) < π`.

## Main results

* `im_cothHalfC`: `Im coth((X + iY)/2) = −2e^X sin Y/(e^{2X} − 2e^X cos Y + 1)`;
* `IsSepMark.cos_im_stripMap_le`: `cos(Im ψ_t(z)/2) ≤ cos(Im z/2) e^{t/2}` on `[0, t(S)]` while `e^z − 1` is not
  swallowed;
* `IsSepMark.exists_isForwardSol_of_cos_lt` (**(3.20)**): if `cos(Im z/2) e^{T/2} < 1`, i.e. `Im z > H(T)`, then
  `e^z − 1` is not swallowed by the chordal time `s(T)` of strip time `T` (it has a forward solution on `[0, s(T)]`),
  for every `T ≤ t(S)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open QuantumZipper (H fwdMap fwdHull IsForwardSol)

namespace InteractingSLE

namespace Strip

/-- The derivative of the imaginary part of a complex-valued function of a real variable. -/
theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).im) f'.im t := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf

/-- `Im coth(w/2) = −2e^X sin Y/(e^{2X} − 2e^X cos Y + 1)` for `w = X + iY`. -/
theorem im_cothHalfC (w : ℂ) :
    (cothHalfC w).im = -(2 * Real.exp w.re * Real.sin w.im) /
      (Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1) := by
  have hre : (exp w).re = Real.exp w.re * Real.cos w.im := exp_re w
  have him : (exp w).im = Real.exp w.re * Real.sin w.im := exp_im w
  have hN : normSq (exp w - 1) = Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1 := by
    rw [normSq_apply, sub_re, sub_im, one_re, one_im, hre, him]
    have := Real.sin_sq_add_cos_sq w.im
    nlinarith [this]
  rw [cothHalfC, div_im, hN]
  simp only [add_re, add_im, sub_re, sub_im, one_re, one_im, hre, him]
  ring

/-- The denominator `e^{2X} − 2e^X cos Y + 1` is at least `2e^X (1 − cos Y)`. -/
theorem two_exp_mul_le_denom (X Y : ℝ) :
    2 * Real.exp X * (1 - Real.cos Y) ≤ Real.exp X ^ 2 - 2 * Real.exp X * Real.cos Y + 1 := by
  nlinarith [sq_nonneg (Real.exp X - 1)]

/-- **The height inequality**: for `0 < Y < π`, `Im coth((X + iY)/2) ≥ −sin Y/(1 − cos Y)` (`= −cot(Y/2)`). -/
theorem neg_sin_div_le_im_cothHalfC {w : ℂ} (h0 : 0 < w.im) (hπ : w.im < Real.pi) :
    -(Real.sin w.im / (1 - Real.cos w.im)) ≤ (cothHalfC w).im := by
  have hs : 0 < Real.sin w.im := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hc : 0 < 1 - Real.cos w.im := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
    rw [Real.cos_zero] at this
    linarith
  rw [im_cothHalfC]
  have hE := Real.exp_pos w.re
  have hD := two_exp_mul_le_denom w.re w.im
  have hDpos : 0 < Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1 := by
    nlinarith [mul_pos hE hc]
  rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hDpos hc]
  nlinarith [mul_pos hE hs]

/-- `sin(Y/2) · sin Y/(1 − cos Y) = cos(Y/2)` (`sin Y/(1 − cos Y) = cot(Y/2)`) when `sin(Y/2) ≠ 0`. -/
theorem sin_half_mul_cot (Y : ℝ) (hs : Real.sin (Y / 2) ≠ 0) :
    Real.sin (Y / 2) * (Real.sin Y / (1 - Real.cos Y)) = Real.cos (Y / 2) := by
  have h2 : Y = 2 * (Y / 2) := by ring
  have hsc := Real.sin_sq_add_cos_sq (Y / 2)
  have hden : 1 - Real.cos Y = 2 * Real.sin (Y / 2) ^ 2 := by
    rw [h2, Real.cos_two_mul]; field_simp; linarith
  rw [hden, h2, Real.sin_two_mul, show 2 * (Y / 2) / 2 = Y / 2 by ring]
  field_simp

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- `Im ψ_t(z) ∈ (0, π)` while `e^z − 1` is not swallowed. -/
theorem im_stripMap_mem_Ioo (h : IsSepMark w v S) {z : ℂ} (hz : 0 < (stripExp z).im)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    (stripMap w v t z).im ∈ Ioo 0 Real.pi := by
  have hs := h.chordalTime_mem ht
  have hfim := Ito.im_fwdMap_pos_of_continuousOn h.nonneg h.continuousOn_w hz hsol hs
  have hG : fwdMap w (chordalTime w v t) (stripExp z) + (w (chordalTime w v t) : ℂ) -
      (v (chordalTime w v t) : ℂ) ∈ H := by
    change 0 < (_ : ℂ).im
    simpa using hfim
  simp only [stripMap, add_im, ofReal_im, zero_add, log_im]
  exact DerivLog.arg_mem_Ioo_of_mem_H hG

/-- `U = cos(Im ψ/2)` grows at most like `e^{t/2}`: `U_t ≤ U_0 e^{t/2}` (from `U' ≤ U/2`). -/
theorem cos_im_stripMap_le (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    Real.cos ((stripMap w v t z).im / 2) ≤ Real.cos (z.im / 2) * Real.exp (t / 2) := by
  have hz₀ := stripExp_im_pos hz
  set T := stripClock w v S
  set g : ℝ → ℝ := fun t => Real.cos ((stripMap w v t z).im / 2) * Real.exp (-t / 2) with hg
  have hY : ContinuousOn (fun t => (stripMap w v t z).im) (Icc 0 T) :=
    continuous_im.comp_continuousOn (h.continuousOn_stripMap hz₀ hsol)
  have hgc : ContinuousOn g (Icc 0 T) :=
    (Real.continuous_cos.comp_continuousOn (hY.div_const 2)).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_id.neg.div_const 2))
  have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt g
      ((-Real.sin ((stripMap w v t z).im / 2) *
        ((cothHalfC (stripMap w v t z - stripDriver w v t)).im / 2)) * Real.exp (-t / 2) +
        Real.cos ((stripMap w v t z).im / 2) * (Real.exp (-t / 2) * (-1 / 2))) t := by
    intro t ht
    have hYd := hasDerivAt_im (h.hasDerivAt_stripMap hz₀ hsol ht)
    have h1 := (hYd.div_const 2).cos
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
      have := ((hasDerivAt_id t).neg.div_const 2).exp
      simpa using this
    exact h1.mul h2
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      have hYm := h.im_stripMap_mem_Ioo hz₀ hsol (Ioo_subset_Icc_self ht)
      set Y := (stripMap w v t z).im
      have hwim : (stripMap w v t z - stripDriver w v t).im = Y := by simp [Y]
      have hlow := neg_sin_div_le_im_cothHalfC (w := stripMap w v t z - stripDriver w v t)
        (by rw [hwim]; exact hYm.1) (by rw [hwim]; exact hYm.2)
      rw [hwim] at hlow
      have hs2 : 0 < Real.sin (Y / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hYm.1]) (by linarith [hYm.2, Real.pi_pos])
      have hkey := sin_half_mul_cot Y hs2.ne'
      have hE := Real.exp_pos (-t / 2)
      have h3 : -Real.sin (Y / 2) * ((cothHalfC (stripMap w v t z - stripDriver w v t)).im / 2) ≤
          Real.cos (Y / 2) / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hlow hs2.le]
      nlinarith [mul_le_mul_of_nonneg_right h3 hE.le]
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.stripClock_nonneg ⟨h.nonneg, le_rfl⟩⟩
  have hle := hanti h0 ht ht.1
  simp only [hg, h.stripMap_zero hz hsol, neg_zero, zero_div, Real.exp_zero, mul_one] at hle
  have hE := Real.exp_pos (t / 2)
  calc Real.cos ((stripMap w v t z).im / 2)
      = Real.cos ((stripMap w v t z).im / 2) * Real.exp (-t / 2) * Real.exp (t / 2) := by
        rw [mul_assoc, ← Real.exp_add, show -t / 2 + t / 2 = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ Real.cos (z.im / 2) * Real.exp (t / 2) := mul_le_mul_of_nonneg_right hle hE.le

/-- `IsSepMark` restricts to shorter intervals. -/
theorem mono (h : IsSepMark w v S) {S' : ℝ} (h0 : 0 ≤ S') (hS : S' ≤ S) : IsSepMark w v S' :=
  ⟨h0, h.continuousOn_w.mono (Icc_subset_Icc le_rfl hS), h.continuousOn_v.mono (Icc_subset_Icc le_rfl hS),
    fun s hs => h.lt s ⟨hs.1, hs.2.trans hS⟩, fun s hs => h.eq s ⟨hs.1, hs.2.trans hS⟩⟩

/-- A positive lower bound for the gap `w − v` on `[0, S]`. -/
theorem exists_pos_le_gap (h : IsSepMark w v S) : ∃ a > 0, ∀ r ∈ Icc 0 S, a ≤ w r - v r := by
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 h.nonneg)
    (h.continuousOn_w.sub h.continuousOn_v)
  exact ⟨_, sub_pos.2 (h.lt r₀ hr₀), fun r hr => hmin hr⟩

end IsSepMark

/-- `‖e^w − 1‖² ≥ 1 − (max q 0)²` whenever `cos (Im w) ≤ q`. -/
theorem one_sub_sq_le_norm_exp_sub_one_sq {w : ℂ} {q : ℝ} (hq : Real.cos w.im ≤ q) :
    1 - max q 0 ^ 2 ≤ ‖exp w - 1‖ ^ 2 := by
  have hN : ‖exp w - 1‖ ^ 2 = Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1 := by
    rw [← normSq_eq_norm_sq, normSq_apply, sub_re, sub_im, one_re, one_im, exp_re, exp_im]
    have := Real.sin_sq_add_cos_sq w.im
    nlinarith [this]
  rw [hN]
  have hE := Real.exp_pos w.re
  rcases le_or_gt (Real.cos w.im) 0 with hc | hc
  · nlinarith [sq_nonneg (max q 0), mul_nonneg hE.le (neg_nonneg.2 hc)]
  · have hq0 : max q 0 = q := max_eq_left (hc.le.trans hq)
    rw [hq0]
    nlinarith [sq_nonneg (Real.exp w.re - Real.cos w.im), mul_le_mul hq hq hc.le (hc.le.trans hq)]

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- **The strip height bound (3.20)**: a point `z ∈ S_π` with `cos(Im z/2) e^{T/2} < 1` (i.e. initial height above
`H(T) = 2 arccos(e^{−T/2})`) is not swallowed by strip time `T`: `e^z − 1` has a chordal forward solution on
`[0, s(T)]`. -/
theorem exists_isForwardSol_of_cos_lt (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip) {T : ℝ}
    (hT : T ∈ Icc 0 (stripClock w v S)) (hcos : Real.cos (z.im / 2) * Real.exp (T / 2) < 1) :
    ∃ u, IsForwardSol w (stripExp z) (chordalTime w v T) u := by
  set s₁ := chordalTime w v T
  have hs₁ : s₁ ∈ Icc 0 S := h.chordalTime_mem hT
  set W' := Ito.clampDrv w S
  have hW' : Continuous W' := Ito.continuous_clampDrv h.nonneg h.continuousOn_w
  have hz₀ := stripExp_im_pos hz
  have htr : ∀ r ∈ Icc 0 S, ∀ u, IsForwardSol W' (stripExp z) r u ↔ IsForwardSol w (stripExp z) r u :=
    fun r hr u => Ito.isForwardSol_iff_of_eqOn (fun x hx => Ito.clampDrv_eqOn ⟨hx.1, hx.2.trans hr.2⟩) u
  by_contra hno
  have hK : stripExp z ∈ fwdHull W' s₁ := by
    by_contra hK
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs₁.1 hz₀ hK
    exact hno ⟨u, (htr s₁ hs₁ u).1 hu⟩
  obtain ⟨-, σ, hσs, hσ, hcl⟩ := (QuantumZipper.FwdClock.mem_fwdHull_iff_clock hW').1 hK
  obtain ⟨amin, hamin, hamin_le⟩ := h.exists_pos_le_gap
  -- the height constant
  set κ₀ := Real.cos (z.im / 2) * Real.exp (T / 2) with hκ₀
  have hc0 : 0 < Real.cos (z.im / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hz.1, Real.pi_pos], by linarith [hz.2]⟩
  have hκ₀pos : 0 < κ₀ := mul_pos hc0 (Real.exp_pos _)
  set q := 2 * κ₀ ^ 2 - 1 with hq
  set m := 1 - max q 0 ^ 2 with hm_def
  have hm : 0 < m := by
    have hq1 : q < 1 := by nlinarith
    have hmax : max q 0 < 1 := max_lt hq1 one_pos
    have := sq_lt_one_iff_abs_lt_one (max q 0) |>.2 (by rw [abs_of_nonneg (le_max_right _ _)]; exact hmax)
    linarith
  -- the lower bound on `|f_r|` before the swallowing time
  have hlow : ∀ r, 0 ≤ r → r < σ → amin ^ 2 * m ≤ ‖fwdMap W' r (stripExp z)‖ ^ 2 := by
    intro r hr0 hrσ
    have hrS : r ∈ Icc 0 S := ⟨hr0, (hrσ.le.trans hσs).trans hs₁.2⟩
    have hnot : stripExp z ∉ fwdHull W' r := fun hK' => by
      have := hK'.2
      rw [hσ, ENNReal.ofReal_le_ofReal_iff hr0] at this
      linarith
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hr0 hz₀ hnot
    have hsolr : ∃ u, IsForwardSol w (stripExp z) r u := ⟨u, (htr r hrS u).1 hu⟩
    have hr' : IsSepMark w v r := h.mono hr0 hrS.2
    have hrr : r ∈ Icc 0 r := ⟨hr0, le_rfl⟩
    have ht : stripClock w v r ∈ Icc 0 (stripClock w v r) := ⟨hr'.stripClock_nonneg hrr, le_rfl⟩
    have hcosle := hr'.cos_im_stripMap_le hz hsolr ht
    have hct : chordalTime w v (stripClock w v r) = r := hr'.chordalTime_stripClock hrr
    have htT : stripClock w v r ≤ T := by
      have := h.strictMonoOn_stripClock.monotoneOn hrS hs₁ (hrσ.le.trans hσs)
      rwa [h.stripClock_chordalTime hT] at this
    set Y := (stripMap w v (stripClock w v r) z).im
    have hYm := hr'.im_stripMap_mem_Ioo hz₀ hsolr ht
    have hcY : Real.cos (Y / 2) ≤ κ₀ :=
      hcosle.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc0.le)
    have hcY0 : 0 < Real.cos (Y / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hYm.1, Real.pi_pos], by linarith [hYm.2]⟩
    have hcosY : Real.cos Y ≤ q := by
      have : Real.cos Y = 2 * Real.cos (Y / 2) ^ 2 - 1 := by
        rw [← Real.cos_two_mul]; ring_nf
      rw [this, hq]
      nlinarith [mul_le_mul hcY hcY hcY0.le hκ₀pos.le]
    -- `f = a (e^{ψ − ξ} − 1)`
    set f := fwdMap w r (stripExp z)
    set a := w r - v r
    have ha : 0 < a := sub_pos.2 (h.lt r hrS)
    have hfim : 0 < f.im := Ito.im_fwdMap_pos_of_continuousOn hr0 (h.continuousOn_w.mono
      (Icc_subset_Icc le_rfl hrS.2)) hz₀ hsolr hrr
    have hGa : f + (a : ℂ) ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; linarith
    have hψξ := stripMap_sub_stripDriver w v (stripClock w v r) z
    rw [hct] at hψξ
    have hexp : exp (stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)) =
        (f + a) / a := by
      rw [hψξ, exp_sub, exp_log hGa, ← ofReal_exp, Real.exp_log ha]
    have hwim : (stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)).im = Y := by
      simp [Y]
    have hbound := one_sub_sq_le_norm_exp_sub_one_sq
      (w := stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)) (q := q)
      (by rw [hwim]; exact hcosY)
    rw [hexp] at hbound
    have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
    have hfa : (f + a) / a - 1 = f / a := by field_simp; ring
    rw [hfa, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_pow] at hbound
    rw [Ito.fwdMap_clampDrv_of_le hrS.2]
    have hapos : 0 < a ^ 2 := by positivity
    rw [le_div_iff₀ hapos] at hbound
    calc amin ^ 2 * m ≤ a ^ 2 * m :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hamin.le (hamin_le r hrS) 2) hm.le
      _ ≤ ‖f‖ ^ 2 := by rw [mul_comm]; exact hbound
  -- the clock stays bounded, contradicting swallowing
  obtain ⟨t', ht'0, ht'σ, hM⟩ := hcl (S / (amin ^ 2 * m))
  have hc : 0 < amin ^ 2 * m := by positivity
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t')
    (C := 1 / (amin ^ 2 * m)) (f := fun r => 1 / ‖fwdMap W' r (stripExp z)‖ ^ 2) (fun r hr => by
      rw [uIoc_of_le ht'0] at hr
      have hl := hlow r hr.1.le (hr.2.trans_lt ht'σ)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le hc hl)
  have ht'S : t' ≤ S := (ht'σ.le.trans hσs).trans hs₁.2
  have : QuantumZipper.FwdClock.fwdClock W' t' (stripExp z) ≤ S / (amin ^ 2 * m) :=
    calc QuantumZipper.FwdClock.fwdClock W' t' (stripExp z)
        ≤ ‖∫ r in (0 : ℝ)..t', 1 / ‖fwdMap W' r (stripExp z)‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 1 / (amin ^ 2 * m) * |t' - 0| := hI
      _ ≤ S / (amin ^ 2 * m) := by
        rw [sub_zero, abs_of_nonneg ht'0, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right ht'S hc.le
  linarith

end IsSepMark

end Strip

end InteractingSLE
