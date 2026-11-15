/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Strip.Height

/-!
# The finite-time horizontal bound of strip hulls

Packet PROVE-ZHAN-A. Astra §3 uses "the finite-time horizontal hull bound" (`ig1_formalization_proofs.txt`
L1336–L1345, L1426–L1440, L1600–L1605): while the strip driver stays in `[−M, M]`, points with `|Re z| > M` are not
swallowed. Indeed, with `X + iY = ψ_t(z) − ξ_t`,

  `Re coth((X + iY)/2) = (e^{2X} − 1)/|e^{X + iY} − 1|²`

has the sign of `X`, so `Re ψ_t(z)` does not decrease while `X > 0`; if `Re z > M ≥ ξ` this keeps
`X ≥ Re z − M > 0`, hence `|e^{X + iY} − 1| ≥ e^{Re z − M} − 1`, and the chordal flow of `e^z − 1` stays away
from `0`. Together with the height bound (3.20) (`Height.lean`) this confines the strip hull at time `T` to
`[−M, M] × (0, H(T)]`.

## Main results

* `exists_isForwardSol_of_forall_le_norm`: a chordal point whose flow stays at distance `≥ δ` from the driver on
  every interval on which it is defined is not swallowed (continuation);
* `re_cothHalfC`, `re_cothHalfC_pos`, `re_cothHalfC_neg`;
* `IsSepMark.le_re_stripMap`, `IsSepMark.re_stripMap_le`: monotonicity of `Re ψ_t(z)` beyond the driver's range;
* `IsSepMark.exists_isForwardSol_of_driver_lt_re`, `IsSepMark.exists_isForwardSol_of_re_lt_driver`: points to the
  right of `max ξ` (left of `min ξ`) on `[0, T]` are not swallowed by strip time `T`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open QuantumZipper (H fwdMap fwdHull IsForwardSol)

namespace InteractingSLE

namespace Strip

/-! ### Continuation of chordal forward solutions -/

/-- **Continuation**: if the centred flow of `z₀ ∈ ℍ` has norm at least `δ > 0` at every time `r ≤ s₁` up to
which it is defined, then it is defined on `[0, s₁]` (the driver need only be continuous on `[0, S] ⊇ [0, s₁]`). -/
theorem exists_isForwardSol_of_forall_le_norm {w : ℝ → ℝ} {S s₁ δ : ℝ} {z₀ : ℂ} (hS : 0 ≤ S)
    (hw : ContinuousOn w (Icc 0 S)) (hs₁ : s₁ ∈ Icc 0 S) (hz₀ : 0 < z₀.im) (hδ : 0 < δ)
    (hlow : ∀ r ∈ Icc 0 s₁, (∃ u, IsForwardSol w z₀ r u) → δ ≤ ‖fwdMap w r z₀‖) :
    ∃ u, IsForwardSol w z₀ s₁ u := by
  set W' := Ito.clampDrv w S
  have hW' : Continuous W' := Ito.continuous_clampDrv hS hw
  have htr : ∀ r ∈ Icc 0 S, ∀ u, IsForwardSol W' z₀ r u ↔ IsForwardSol w z₀ r u :=
    fun r hr u => Ito.isForwardSol_iff_of_eqOn (fun x hx => Ito.clampDrv_eqOn ⟨hx.1, hx.2.trans hr.2⟩) u
  by_contra hno
  have hK : z₀ ∈ fwdHull W' s₁ := by
    by_contra hK
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs₁.1 hz₀ hK
    exact hno ⟨u, (htr s₁ hs₁ u).1 hu⟩
  obtain ⟨-, σ, hσs, hσ, hcl⟩ := (QuantumZipper.FwdClock.mem_fwdHull_iff_clock hW').1 hK
  have hlow' : ∀ r, 0 ≤ r → r < σ → δ ^ 2 ≤ ‖fwdMap W' r z₀‖ ^ 2 := by
    intro r hr0 hrσ
    have hrS : r ∈ Icc 0 S := ⟨hr0, (hrσ.le.trans hσs).trans hs₁.2⟩
    have hnot : z₀ ∉ fwdHull W' r := fun hK' => by
      have := hK'.2
      rw [hσ, ENNReal.ofReal_le_ofReal_iff hr0] at this
      linarith
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hr0 hz₀ hnot
    rw [Ito.fwdMap_clampDrv_of_le hrS.2]
    exact pow_le_pow_left₀ hδ.le (hlow r ⟨hr0, hrσ.le.trans hσs⟩ ⟨u, (htr r hrS u).1 hu⟩) 2
  obtain ⟨t', ht'0, ht'σ, hM⟩ := hcl (S / δ ^ 2)
  have hc : 0 < δ ^ 2 := by positivity
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t')
    (C := 1 / δ ^ 2) (f := fun r => 1 / ‖fwdMap W' r z₀‖ ^ 2) (fun r hr => by
      rw [uIoc_of_le ht'0] at hr
      have hl := hlow' r hr.1.le (hr.2.trans_lt ht'σ)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le hc hl)
  have ht'S : t' ≤ S := (ht'σ.le.trans hσs).trans hs₁.2
  have : QuantumZipper.FwdClock.fwdClock W' t' z₀ ≤ S / δ ^ 2 :=
    calc QuantumZipper.FwdClock.fwdClock W' t' z₀
        ≤ ‖∫ r in (0 : ℝ)..t', 1 / ‖fwdMap W' r z₀‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 1 / δ ^ 2 * |t' - 0| := hI
      _ ≤ S / δ ^ 2 := by
        rw [sub_zero, abs_of_nonneg ht'0, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right ht'S hc.le
  linarith

/-! ### The real part of `coth` -/

/-- `Re coth(w/2) = (e^{2X} − 1)/(e^{2X} − 2e^X cos Y + 1)` for `w = X + iY`. -/
theorem re_cothHalfC (w : ℂ) :
    (cothHalfC w).re = (Real.exp w.re ^ 2 - 1) /
      (Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1) := by
  have hre : (exp w).re = Real.exp w.re * Real.cos w.im := exp_re w
  have him : (exp w).im = Real.exp w.re * Real.sin w.im := exp_im w
  have hs := Real.sin_sq_add_cos_sq w.im
  have hN : normSq (exp w - 1) = Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1 := by
    rw [normSq_apply, sub_re, sub_im, one_re, one_im, hre, him]
    nlinarith [hs]
  rw [cothHalfC, div_re, hN]
  simp only [add_re, add_im, sub_re, sub_im, one_re, one_im, hre, him]
  rw [← add_div]
  congr 1
  linear_combination (Real.exp w.re) ^ 2 * hs

theorem denom_pos_of_re_ne_zero {w : ℂ} (h : w.re ≠ 0) :
    0 < Real.exp w.re ^ 2 - 2 * Real.exp w.re * Real.cos w.im + 1 := by
  have hE := Real.exp_pos w.re
  have hE1 : Real.exp w.re ≠ 1 := fun h1 => h (Real.exp_eq_one_iff _ |>.1 h1)
  have hc := Real.cos_le_one w.im
  have : 0 < (Real.exp w.re - 1) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * Real.exp w.re)]

theorem re_cothHalfC_pos {w : ℂ} (h : 0 < w.re) : 0 < (cothHalfC w).re := by
  rw [re_cothHalfC]
  refine div_pos ?_ (denom_pos_of_re_ne_zero h.ne')
  have := Real.one_lt_exp_iff.2 h
  nlinarith

theorem re_cothHalfC_neg {w : ℂ} (h : w.re < 0) : (cothHalfC w).re < 0 := by
  rw [re_cothHalfC]
  refine div_neg_of_neg_of_pos ?_ (denom_pos_of_re_ne_zero h.ne)
  have h1 : Real.exp w.re < 1 := by simpa using Real.exp_lt_exp.2 h
  have h0 := Real.exp_pos w.re
  nlinarith

/-- The derivative of the real part of a complex-valued function of a real variable. -/
theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).re) f'.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- `Re ψ_u(z)` does not decrease on `[0, T]` if `Re z > M ≥ ξ_u` there. -/
theorem le_re_stripMap (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {T M : ℝ} (hT : T ∈ Icc 0 (stripClock w v S))
    (hξ : ∀ u ∈ Icc 0 T, stripDriver w v u ≤ M) (hzM : M < z.re) :
    ∀ u ∈ Icc 0 T, z.re ≤ (stripMap w v u z).re := by
  have hz₀ := stripExp_im_pos hz
  have hsub : Icc 0 T ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc le_rfl hT.2
  have hRe : ContinuousOn (fun u => (stripMap w v u z).re) (Icc 0 T) :=
    continuous_re.comp_continuousOn ((h.continuousOn_stripMap hz₀ hsol).mono hsub)
  have hX : ContinuousOn (fun u => (stripMap w v u z).re - stripDriver w v u) (Icc 0 T) :=
    hRe.sub (h.continuousOn_stripDriver.mono hsub)
  set s := {u | z.re ≤ (stripMap w v u z).re}
  have hclosed : IsClosed (s ∩ Icc 0 T) := by
    have := hRe.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := z.re))
    rwa [inter_comm] at this
  have h0 : (0 : ℝ) ∈ s := by
    show z.re ≤ _; rw [h.stripMap_zero hz hsol]
  refine fun u hu => (hclosed.Icc_subset_of_forall_exists_gt h0 fun x hx y hy => ?_) hu
  -- `X > 0` at `x`, hence on a right neighbourhood
  have hxT : x ∈ Icc 0 T := Ico_subset_Icc_self hx.2
  have hXx : 0 < (stripMap w v x z).re - stripDriver w v x := by
    have h1 := hξ x hxT
    have h2 : z.re ≤ (stripMap w v x z).re := hx.1
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hX x hxT) _ hXx
  set y' := min (min y (x + δ / 2)) T
  have hxy' : x < y' := lt_min (lt_min hy (by linarith)) hx.2.2
  have hy'T : y' ≤ T := min_le_right _ _
  have hXpos : ∀ r ∈ Icc x y', 0 < (stripMap w v r z).re - stripDriver w v r := by
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hxT.1.trans hr.1, hr.2.trans hy'T⟩
    have hd : dist r x < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
      have : y' ≤ x + δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith [hr.2]
    have := hball hrT hd
    rw [Real.dist_eq] at this
    linarith [neg_abs_le ((stripMap w v r z).re - stripDriver w v r -
      ((stripMap w v x z).re - stripDriver w v x))]
  have hmono : MonotoneOn (fun u => (stripMap w v u z).re) (Icc x y') := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc x y')
      (hRe.mono (Icc_subset_Icc hxT.1 hy'T)) ?_ ?_
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 (stripClock w v S) :=
        ⟨hxT.1.trans_lt hr.1, hr.2.trans_le (hy'T.trans hT.2)⟩
      exact (hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 (stripClock w v S) :=
        ⟨hxT.1.trans_lt hr.1, hr.2.trans_le (hy'T.trans hT.2)⟩
      rw [(hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).deriv]
      refine (re_cothHalfC_pos ?_).le
      simpa using hXpos r (Ioo_subset_Icc_self hr)
  refine ⟨y', ?_, hxy', (min_le_left _ _).trans (min_le_left _ _)⟩
  have := hmono (left_mem_Icc.2 hxy'.le) (right_mem_Icc.2 hxy'.le) hxy'.le
  exact le_trans (show z.re ≤ (stripMap w v x z).re from hx.1) this

/-- `Re ψ_u(z)` does not increase on `[0, T]` if `Re z < −M ≤ ξ_u` there. -/
theorem re_stripMap_le (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {T M : ℝ} (hT : T ∈ Icc 0 (stripClock w v S))
    (hξ : ∀ u ∈ Icc 0 T, -M ≤ stripDriver w v u) (hzM : z.re < -M) :
    ∀ u ∈ Icc 0 T, (stripMap w v u z).re ≤ z.re := by
  have hz₀ := stripExp_im_pos hz
  have hsub : Icc 0 T ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc le_rfl hT.2
  have hRe : ContinuousOn (fun u => (stripMap w v u z).re) (Icc 0 T) :=
    continuous_re.comp_continuousOn ((h.continuousOn_stripMap hz₀ hsol).mono hsub)
  have hX : ContinuousOn (fun u => (stripMap w v u z).re - stripDriver w v u) (Icc 0 T) :=
    hRe.sub (h.continuousOn_stripDriver.mono hsub)
  set s := {u | (stripMap w v u z).re ≤ z.re}
  have hclosed : IsClosed (s ∩ Icc 0 T) := by
    have := hRe.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := z.re))
    rwa [inter_comm] at this
  have h0 : (0 : ℝ) ∈ s := by
    show _ ≤ z.re; rw [h.stripMap_zero hz hsol]
  refine fun u hu => (hclosed.Icc_subset_of_forall_exists_gt h0 fun x hx y hy => ?_) hu
  have hxT : x ∈ Icc 0 T := Ico_subset_Icc_self hx.2
  have hXx : (stripMap w v x z).re - stripDriver w v x < 0 := by
    have h1 := hξ x hxT
    have h2 : (stripMap w v x z).re ≤ z.re := hx.1
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hX x hxT) _ (neg_pos.2 hXx)
  set y' := min (min y (x + δ / 2)) T
  have hxy' : x < y' := lt_min (lt_min hy (by linarith)) hx.2.2
  have hy'T : y' ≤ T := min_le_right _ _
  have hXneg : ∀ r ∈ Icc x y', (stripMap w v r z).re - stripDriver w v r < 0 := by
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hxT.1.trans hr.1, hr.2.trans hy'T⟩
    have hd : dist r x < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
      have : y' ≤ x + δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith [hr.2]
    have := hball hrT hd
    rw [Real.dist_eq] at this
    linarith [le_abs_self ((stripMap w v r z).re - stripDriver w v r -
      ((stripMap w v x z).re - stripDriver w v x))]
  have hanti : AntitoneOn (fun u => (stripMap w v u z).re) (Icc x y') := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc x y')
      (hRe.mono (Icc_subset_Icc hxT.1 hy'T)) ?_ ?_
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 (stripClock w v S) :=
        ⟨hxT.1.trans_lt hr.1, hr.2.trans_le (hy'T.trans hT.2)⟩
      exact (hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 (stripClock w v S) :=
        ⟨hxT.1.trans_lt hr.1, hr.2.trans_le (hy'T.trans hT.2)⟩
      rw [(hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).deriv]
      refine (re_cothHalfC_neg ?_).le
      simpa using hXneg r (Ioo_subset_Icc_self hr)
  refine ⟨y', ?_, hxy', (min_le_left _ _).trans (min_le_left _ _)⟩
  have := hanti (left_mem_Icc.2 hxy'.le) (right_mem_Icc.2 hxy'.le) hxy'.le
  exact le_trans this (show (stripMap w v x z).re ≤ z.re from hx.1)

/-- At strip time `t(r)`, the centred chordal flow is `f_r(e^z − 1) = (w_r − v_r)(e^{ψ − ξ} − 1)`. -/
theorem fwdMap_eq_mul_exp_sub_one (h : IsSepMark w v S) {z : ℂ} (hz₀ : 0 < (stripExp z).im)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) :
    fwdMap w S (stripExp z) = ((w S - v S : ℝ) : ℂ) *
      (exp (stripMap w v (stripClock w v S) z - stripDriver w v (stripClock w v S)) - 1) := by
  have hSS : S ∈ Icc 0 S := ⟨h.nonneg, le_rfl⟩
  have hct : chordalTime w v (stripClock w v S) = S := h.chordalTime_stripClock hSS
  have ha : 0 < w S - v S := sub_pos.2 (h.lt S hSS)
  have hfim : 0 < (fwdMap w S (stripExp z)).im :=
    Ito.im_fwdMap_pos_of_continuousOn h.nonneg h.continuousOn_w hz₀ hsol hSS
  have hGa : fwdMap w S (stripExp z) + ((w S - v S : ℝ) : ℂ) ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  have hψξ := stripMap_sub_stripDriver w v (stripClock w v S) z
  rw [hct] at hψξ
  rw [hψξ, exp_sub, exp_log hGa, ← ofReal_exp, Real.exp_log ha]
  have ha' : ((w S - v S : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  field_simp
  ring

/-- **Right horizontal bound**: if the strip driver stays `≤ M` on `[0, T]` and `Re z > M`, then `e^z − 1` is not
swallowed by the chordal time `s(T)`. -/
theorem exists_isForwardSol_of_driver_lt_re (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip) {T M : ℝ}
    (hT : T ∈ Icc 0 (stripClock w v S)) (hξ : ∀ u ∈ Icc 0 T, stripDriver w v u ≤ M) (hzM : M < z.re) :
    ∃ u, IsForwardSol w (stripExp z) (chordalTime w v T) u := by
  have hz₀ := stripExp_im_pos hz
  obtain ⟨amin, hamin, hamin_le⟩ := h.exists_pos_le_gap
  have he : 0 < Real.exp (z.re - M) - 1 := by
    have := Real.one_lt_exp_iff.2 (sub_pos.2 hzM); linarith
  have hs₁ := h.chordalTime_mem hT
  refine exists_isForwardSol_of_forall_le_norm h.nonneg h.continuousOn_w hs₁ hz₀ (mul_pos hamin he)
    fun r hr hsolr => ?_
  have hrS : r ∈ Icc 0 S := ⟨hr.1, hr.2.trans hs₁.2⟩
  have hr' : IsSepMark w v r := h.mono hr.1 hrS.2
  have hrT : stripClock w v r ≤ T := by
    have := h.strictMonoOn_stripClock.monotoneOn hrS hs₁ hr.2
    rwa [h.stripClock_chordalTime hT] at this
  have hcl : stripClock w v r ∈ Icc 0 (stripClock w v r) :=
    ⟨hr'.stripClock_nonneg ⟨hr.1, le_rfl⟩, le_rfl⟩
  have hre := hr'.le_re_stripMap hz hsolr hcl (fun u hu => hξ u ⟨hu.1, hu.2.trans hrT⟩) hzM _ hcl
  have hξr := hξ _ ⟨hcl.1, hrT⟩
  rw [hr'.fwdMap_eq_mul_exp_sub_one hz₀ hsolr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.2 (h.lt r hrS))]
  set wψ := stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)
  have hX : z.re - M ≤ wψ.re := by simp only [wψ, sub_re, ofReal_re]; linarith
  have h1 : Real.exp (z.re - M) - 1 ≤ ‖exp wψ - 1‖ := by
    have := norm_sub_norm_le (exp wψ) 1
    rw [norm_exp, norm_one] at this
    linarith [Real.exp_le_exp.2 hX]
  exact mul_le_mul (hamin_le r hrS) h1 he.le (sub_pos.2 (h.lt r hrS)).le

/-- **Left horizontal bound**: if the strip driver stays `≥ −M` on `[0, T]` and `Re z < −M`, then `e^z − 1` is not
swallowed by the chordal time `s(T)`. -/
theorem exists_isForwardSol_of_re_lt_driver (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip) {T M : ℝ}
    (hT : T ∈ Icc 0 (stripClock w v S)) (hξ : ∀ u ∈ Icc 0 T, -M ≤ stripDriver w v u) (hzM : z.re < -M) :
    ∃ u, IsForwardSol w (stripExp z) (chordalTime w v T) u := by
  have hz₀ := stripExp_im_pos hz
  obtain ⟨amin, hamin, hamin_le⟩ := h.exists_pos_le_gap
  have he : 0 < 1 - Real.exp (z.re + M) := by
    have : Real.exp (z.re + M) < 1 := by simpa using Real.exp_lt_exp.2 (show z.re + M < 0 by linarith)
    linarith
  have hs₁ := h.chordalTime_mem hT
  refine exists_isForwardSol_of_forall_le_norm h.nonneg h.continuousOn_w hs₁ hz₀ (mul_pos hamin he)
    fun r hr hsolr => ?_
  have hrS : r ∈ Icc 0 S := ⟨hr.1, hr.2.trans hs₁.2⟩
  have hr' : IsSepMark w v r := h.mono hr.1 hrS.2
  have hrT : stripClock w v r ≤ T := by
    have := h.strictMonoOn_stripClock.monotoneOn hrS hs₁ hr.2
    rwa [h.stripClock_chordalTime hT] at this
  have hcl : stripClock w v r ∈ Icc 0 (stripClock w v r) :=
    ⟨hr'.stripClock_nonneg ⟨hr.1, le_rfl⟩, le_rfl⟩
  have hre := hr'.re_stripMap_le hz hsolr hcl (fun u hu => hξ u ⟨hu.1, hu.2.trans hrT⟩) hzM _ hcl
  have hξr := hξ _ ⟨hcl.1, hrT⟩
  rw [hr'.fwdMap_eq_mul_exp_sub_one hz₀ hsolr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.2 (h.lt r hrS))]
  set wψ := stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)
  have hX : wψ.re ≤ z.re + M := by simp only [wψ, sub_re, ofReal_re]; linarith
  have h1 : 1 - Real.exp (z.re + M) ≤ ‖exp wψ - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (exp wψ)
    rw [norm_exp, norm_one, norm_sub_rev] at this
    linarith [Real.exp_le_exp.2 hX]
  exact mul_le_mul (hamin_le r hrS) h1 he.le (sub_pos.2 (h.lt r hrS)).le

end IsSepMark

end Strip

end InteractingSLE
