/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailPullback
import InteractingSLE.Spec.Restart.ClockTrace
import InteractingSLE.Foundations.Strip.Horizontal

/-!
# Constant strip drift `|σ| < 1`: the bounded hull

Packet PROVE-ZHAN-A5. Astra, *Formalization proofs and dependency audit* (ruling R35), "Constant drift with
`|σ| < 1`: from the diffusion to the actual trace", first paragraph (`source/external/AstraIG1/
ig1_formalization_proofs.txt` L1422–L1440):

> Bounded hull. Choose `|σ| < a < b < 1`. Brownian sublinearity gives a finite random `C` such that
> `|ξ_t| ≤ C + at` for all `t`. Choose `R` with `tanh(R/2) ≥ b`. For `X ≥ R` and `0 ≤ Y ≤ π`,
> `Re coth((X + iY)/2) = sinh X/(cosh X − cos Y) ≥ b`. Starting at `Re z ≥ C + R + 1`, a first-violation argument
> gives `Re ψ_t(z) − ξ_t ≥ R + 1 + (b − a)t`. […] Such points are never swallowed. Reflection gives a left bound.
> The union of all hulls, and the trace, is horizontally bounded.

In the R36 form (`Foundations/Strip`) the strip point `z` is the chordal point `e^z − 1`, and "never swallowed" is
the existence of the chordal forward solution; it follows from `Re ψ_u(z) − ξ_u > R` alone, because the centred
chordal flow is `(w − v)(e^{ψ − ξ} − 1)` (`IsSepMark.fwdMap_eq_mul_exp_sub_one`), whose norm is then at least
`(w − v)(e^R − 1)`. No control of the height is needed. We use `(e^R − 1)/(e^R + 1) = tanh(R/2)`.

## Main results

* `le_re_cothHalfC`, `re_cothHalfC_le`: `Re coth((X + iY)/2) ≥ (e^X − 1)/(e^X + 1)` for `X ≥ 0` (and the mirror);
* `IsSepMark.add_mul_le_re_stripMap` (the first-violation argument): if `ξ_u ≤ C + au` on `[0, t(S)]`,
  `a ≤ b ≤ tanh(R/2)` and `Re z > C + R`, then `Re ψ_u(z) ≥ Re z + bu`; `IsSepMark.re_stripMap_le_sub_mul` (mirror);
* `IsSepMark.exists_isForwardSol_of_sublinear_right`, `…_left`: such points are not swallowed by chordal time `S`;
* `Zhan.IsStripPath.not_mem_fwdHull_of_sublinear`: for a strip path whose strip driver satisfies `|ξ_t| ≤ C + at`,
  no point `e^z − 1` with `|Re z| > C + R` is ever swallowed during the strip life;
* `Zhan.IsStripPath.norm_one_add_trace_mem_Icc` (**the bounded hull**): every generating trace on the strip life
  satisfies `e^{−(C+R)} ≤ ‖1 + η_s‖ ≤ e^{C+R}`, i.e. the strip trace `log(1 + η)` is horizontally bounded.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Strip

/-! ### `Re coth` beyond a level -/

/-- `Re coth(w/2) ≥ (e^X − 1)/(e^X + 1)` (`= tanh(X/2)`) for `X = Re w ≥ 0`. -/
theorem le_re_cothHalfC {w : ℂ} (h : 0 ≤ w.re) :
    (Real.exp w.re - 1) / (Real.exp w.re + 1) ≤ (cothHalfC w).re := by
  rw [re_cothHalfC]
  set E := Real.exp w.re with hEdef
  have hE : 1 ≤ E := Real.one_le_exp_iff.2 h
  have hc := Real.cos_le_one w.im
  have hc' := Real.neg_one_le_cos w.im
  have hD0 : (E - 1) ^ 2 ≤ E ^ 2 - 2 * E * Real.cos w.im + 1 := by nlinarith
  have hDle : E ^ 2 - 2 * E * Real.cos w.im + 1 ≤ (E + 1) ^ 2 := by nlinarith
  rcases (show (0 : ℝ) ≤ E ^ 2 - 2 * E * Real.cos w.im + 1 by nlinarith).eq_or_lt with hD | hD
  · have hE1 : E = 1 := by nlinarith
    rw [← hD, hE1]; norm_num
  · rw [div_le_div_iff₀ (by positivity) hD]
    nlinarith [mul_le_mul_of_nonneg_left hDle (show (0 : ℝ) ≤ E - 1 by linarith)]

/-- `Re coth(w/2) ≤ (e^X − 1)/(e^X + 1)` for `X = Re w ≤ 0`. -/
theorem re_cothHalfC_le {w : ℂ} (h : w.re ≤ 0) :
    (cothHalfC w).re ≤ (Real.exp w.re - 1) / (Real.exp w.re + 1) := by
  rw [re_cothHalfC]
  set E := Real.exp w.re with hEdef
  have hE : E ≤ 1 := Real.exp_le_one_iff.2 h
  have hE0 : 0 < E := Real.exp_pos _
  have hc := Real.cos_le_one w.im
  have hc' := Real.neg_one_le_cos w.im
  have hD0 : (E - 1) ^ 2 ≤ E ^ 2 - 2 * E * Real.cos w.im + 1 := by nlinarith
  have hDle : E ^ 2 - 2 * E * Real.cos w.im + 1 ≤ (E + 1) ^ 2 := by nlinarith
  rcases (show (0 : ℝ) ≤ E ^ 2 - 2 * E * Real.cos w.im + 1 by nlinarith).eq_or_lt with hD | hD
  · have hE1 : E = 1 := by nlinarith
    rw [← hD, hE1]; norm_num
  · rw [div_le_div_iff₀ hD (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hDle (show (0 : ℝ) ≤ 1 - E by linarith)]

/-- `x ↦ (e^x − 1)/(e^x + 1)` is monotone. -/
theorem exp_sub_div_exp_add_mono {x y : ℝ} (hxy : x ≤ y) :
    (Real.exp x - 1) / (Real.exp x + 1) ≤ (Real.exp y - 1) / (Real.exp y + 1) := by
  have hx := Real.exp_pos x
  have hy := Real.exp_pos y
  have hle := Real.exp_le_exp.2 hxy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `(e^{−x} − 1)/(e^{−x} + 1) = −(e^x − 1)/(e^x + 1)`. -/
theorem exp_neg_sub_div_exp_neg_add (x : ℝ) :
    (Real.exp (-x) - 1) / (Real.exp (-x) + 1) = -((Real.exp x - 1) / (Real.exp x + 1)) := by
  have hx := Real.exp_pos x
  rw [Real.exp_neg]
  field_simp
  ring

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- **The first-violation argument (right).** If the strip driver satisfies `ξ_u ≤ C + au` on `[0, t(S)]`,
`a ≤ b ≤ tanh(R/2)` with `R ≥ 0`, and `Re z > C + R`, then `Re ψ_u(z) ≥ Re z + bu` on `[0, t(S)]`. -/
theorem add_mul_le_re_stripMap (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {C a b R : ℝ} (hR : 0 ≤ R)
    (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ u ∈ Icc 0 (stripClock w v S), stripDriver w v u ≤ C + a * u) (hzC : C + R < z.re) :
    ∀ u ∈ Icc 0 (stripClock w v S), z.re + b * u ≤ (stripMap w v u z).re := by
  have hz₀ := stripExp_im_pos hz
  set T := stripClock w v S with hT
  have hRe : ContinuousOn (fun u => (stripMap w v u z).re) (Icc 0 T) :=
    continuous_re.comp_continuousOn (h.continuousOn_stripMap hz₀ hsol)
  have hX : ContinuousOn (fun u => (stripMap w v u z).re - stripDriver w v u) (Icc 0 T) :=
    hRe.sub h.continuousOn_stripDriver
  set s := {u | z.re + b * u ≤ (stripMap w v u z).re}
  have hclosed : IsClosed (s ∩ Icc 0 T) := by
    have hc : ContinuousOn (fun u => (stripMap w v u z).re - b * u) (Icc 0 T) :=
      hRe.sub (continuousOn_const.mul continuousOn_id)
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := z.re))
    rw [inter_comm]
    convert this using 2
    ext u
    simp only [s, mem_ofPred_eq, mem_preimage, mem_Ici]
    constructor <;> intro hu <;> linarith
  have h0 : (0 : ℝ) ∈ s := by
    show z.re + b * 0 ≤ _
    rw [mul_zero, add_zero, h.stripMap_zero hz hsol]
  refine fun u hu => (hclosed.Icc_subset_of_forall_exists_gt h0 fun x hx y hy => ?_) hu
  have hxT : x ∈ Icc 0 T := Ico_subset_Icc_self hx.2
  -- `X > R` at `x`, hence on a right neighbourhood
  have hXx : R < (stripMap w v x z).re - stripDriver w v x := by
    have h1 := hξ x hxT
    have h2 : z.re + b * x ≤ (stripMap w v x z).re := hx.1
    nlinarith [hxT.1]
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hX x hxT) _ (sub_pos.2 hXx)
  set y' := min (min y (x + δ / 2)) T
  have hxy' : x < y' := lt_min (lt_min hy (by linarith)) hx.2.2
  have hy'T : y' ≤ T := min_le_right _ _
  have hXR : ∀ r ∈ Icc x y', R < (stripMap w v r z).re - stripDriver w v r := by
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
  have hmono : MonotoneOn (fun u => (stripMap w v u z).re - b * u) (Icc x y') := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc x y')
      ((hRe.sub (continuousOn_const.mul continuousOn_id)).mono (Icc_subset_Icc hxT.1 hy'T)) ?_ ?_
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 T := ⟨hxT.1.trans_lt hr.1, hr.2.trans_le hy'T⟩
      exact ((hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).sub
        ((hasDerivAt_id r).const_mul b)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 T := ⟨hxT.1.trans_lt hr.1, hr.2.trans_le hy'T⟩
      have hd : HasDerivAt (fun u => (stripMap w v u z).re - b * u) _ r :=
        (hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).sub ((hasDerivAt_id' r).const_mul b)
      rw [hd.deriv]
      have hXr := hXR r (Ioo_subset_Icc_self hr)
      have hre : ((stripMap w v r z) - (stripDriver w v r : ℂ)).re =
          (stripMap w v r z).re - stripDriver w v r := by simp
      have h1 := le_re_cothHalfC (w := stripMap w v r z - (stripDriver w v r : ℂ)) (by rw [hre]; linarith)
      rw [hre] at h1
      have h2 := exp_sub_div_exp_add_mono hXr.le
      simp only [mul_one]
      linarith
  refine ⟨y', ?_, hxy', (min_le_left _ _).trans (min_le_left _ _)⟩
  have := hmono (left_mem_Icc.2 hxy'.le) (right_mem_Icc.2 hxy'.le) hxy'.le
  show z.re + b * y' ≤ (stripMap w v y' z).re
  have hx1 : z.re + b * x ≤ (stripMap w v x z).re := hx.1
  simp only at this
  linarith

/-- **The first-violation argument (left).** If `ξ_u ≥ −C − au` on `[0, t(S)]`, `a ≤ b ≤ tanh(R/2)` with `R ≥ 0`,
and `Re z < −C − R`, then `Re ψ_u(z) ≤ Re z − bu` on `[0, t(S)]`. -/
theorem re_stripMap_le_sub_mul (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {C a b R : ℝ} (hR : 0 ≤ R)
    (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ u ∈ Icc 0 (stripClock w v S), -C - a * u ≤ stripDriver w v u) (hzC : z.re < -C - R) :
    ∀ u ∈ Icc 0 (stripClock w v S), (stripMap w v u z).re ≤ z.re - b * u := by
  have hz₀ := stripExp_im_pos hz
  set T := stripClock w v S with hT
  have hRe : ContinuousOn (fun u => (stripMap w v u z).re) (Icc 0 T) :=
    continuous_re.comp_continuousOn (h.continuousOn_stripMap hz₀ hsol)
  have hX : ContinuousOn (fun u => (stripMap w v u z).re - stripDriver w v u) (Icc 0 T) :=
    hRe.sub h.continuousOn_stripDriver
  set s := {u | (stripMap w v u z).re ≤ z.re - b * u}
  have hclosed : IsClosed (s ∩ Icc 0 T) := by
    have hc : ContinuousOn (fun u => (stripMap w v u z).re + b * u) (Icc 0 T) :=
      hRe.add (continuousOn_const.mul continuousOn_id)
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := z.re))
    rw [inter_comm]
    convert this using 2
    ext u
    simp only [s, mem_ofPred_eq, mem_preimage, mem_Iic]
    constructor <;> intro hu <;> linarith
  have h0 : (0 : ℝ) ∈ s := by
    show _ ≤ z.re - b * 0
    rw [mul_zero, sub_zero, h.stripMap_zero hz hsol]
  refine fun u hu => (hclosed.Icc_subset_of_forall_exists_gt h0 fun x hx y hy => ?_) hu
  have hxT : x ∈ Icc 0 T := Ico_subset_Icc_self hx.2
  have hXx : (stripMap w v x z).re - stripDriver w v x < -R := by
    have h1 := hξ x hxT
    have h2 : (stripMap w v x z).re ≤ z.re - b * x := hx.1
    nlinarith [hxT.1]
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hX x hxT) _ (show 0 < -R -
    ((stripMap w v x z).re - stripDriver w v x) by linarith)
  set y' := min (min y (x + δ / 2)) T
  have hxy' : x < y' := lt_min (lt_min hy (by linarith)) hx.2.2
  have hy'T : y' ≤ T := min_le_right _ _
  have hXR : ∀ r ∈ Icc x y', (stripMap w v r z).re - stripDriver w v r < -R := by
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
  have hanti : AntitoneOn (fun u => (stripMap w v u z).re + b * u) (Icc x y') := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc x y')
      ((hRe.add (continuousOn_const.mul continuousOn_id)).mono (Icc_subset_Icc hxT.1 hy'T)) ?_ ?_
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 T := ⟨hxT.1.trans_lt hr.1, hr.2.trans_le hy'T⟩
      exact ((hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).add
        ((hasDerivAt_id r).const_mul b)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hrS : r ∈ Ioo 0 T := ⟨hxT.1.trans_lt hr.1, hr.2.trans_le hy'T⟩
      have hd : HasDerivAt (fun u => (stripMap w v u z).re + b * u) _ r :=
        (hasDerivAt_re (h.hasDerivAt_stripMap hz₀ hsol hrS)).add ((hasDerivAt_id' r).const_mul b)
      rw [hd.deriv]
      have hXr := hXR r (Ioo_subset_Icc_self hr)
      have hre : ((stripMap w v r z) - (stripDriver w v r : ℂ)).re =
          (stripMap w v r z).re - stripDriver w v r := by simp
      have h1 := re_cothHalfC_le (w := stripMap w v r z - (stripDriver w v r : ℂ)) (by rw [hre]; linarith)
      rw [hre] at h1
      have h2 := exp_sub_div_exp_add_mono (show (stripMap w v r z).re - stripDriver w v r ≤ -R by linarith)
      rw [exp_neg_sub_div_exp_neg_add] at h2
      simp only [mul_one]
      linarith
  refine ⟨y', ?_, hxy', (min_le_left _ _).trans (min_le_left _ _)⟩
  have := hanti (left_mem_Icc.2 hxy'.le) (right_mem_Icc.2 hxy'.le) hxy'.le
  show (stripMap w v y' z).re ≤ z.re - b * y'
  have hx1 : (stripMap w v x z).re ≤ z.re - b * x := hx.1
  simp only at this
  linarith

/-- **Never swallowed (right).** If `ξ_u ≤ C + au` on `[0, t(S)]`, `a ≤ b ≤ tanh(R/2)` with `R > 0`, and
`Re z > C + R`, then the chordal point `e^z − 1` is not swallowed by chordal time `S`. -/
theorem exists_isForwardSol_of_sublinear_right (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    {C a b R : ℝ} (hR : 0 < R) (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ u ∈ Icc 0 (stripClock w v S), stripDriver w v u ≤ C + a * u) (hzC : C + R < z.re) :
    ∃ u, IsForwardSol w (stripExp z) S u := by
  have hz₀ := stripExp_im_pos hz
  obtain ⟨amin, hamin, hamin_le⟩ := h.exists_pos_le_gap
  have he : 0 < Real.exp R - 1 := by have := Real.one_lt_exp_iff.2 hR; linarith
  refine exists_isForwardSol_of_forall_le_norm h.nonneg h.continuousOn_w ⟨h.nonneg, le_rfl⟩ hz₀
    (mul_pos hamin he) fun r hr hsolr => ?_
  have hr' : IsSepMark w v r := h.mono hr.1 hr.2
  have hrT : stripClock w v r ≤ stripClock w v S :=
    h.strictMonoOn_stripClock.monotoneOn hr ⟨h.nonneg, le_rfl⟩ hr.2
  have hcl : stripClock w v r ∈ Icc 0 (stripClock w v r) :=
    ⟨hr'.stripClock_nonneg ⟨hr.1, le_rfl⟩, le_rfl⟩
  have hre := hr'.add_mul_le_re_stripMap hz hsolr hR.le hbR hab
    (fun u hu => hξ u ⟨hu.1, hu.2.trans hrT⟩) hzC _ hcl
  have hξr := hξ _ ⟨hcl.1, hcl.2.trans hrT⟩
  rw [hr'.fwdMap_eq_mul_exp_sub_one hz₀ hsolr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.2 (h.lt r hr))]
  set wψ := stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)
  have hX : R ≤ wψ.re := by
    simp only [wψ, sub_re, ofReal_re]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) hcl.1]
  have h1 : Real.exp R - 1 ≤ ‖exp wψ - 1‖ := by
    have := norm_sub_norm_le (exp wψ) 1
    rw [norm_exp, norm_one] at this
    linarith [Real.exp_le_exp.2 hX]
  exact mul_le_mul (hamin_le r hr) h1 he.le (sub_pos.2 (h.lt r hr)).le

/-- **Never swallowed (left).** If `ξ_u ≥ −C − au` on `[0, t(S)]`, `a ≤ b ≤ tanh(R/2)` with `R > 0`, and
`Re z < −C − R`, then `e^z − 1` is not swallowed by chordal time `S`. -/
theorem exists_isForwardSol_of_sublinear_left (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    {C a b R : ℝ} (hR : 0 < R) (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ u ∈ Icc 0 (stripClock w v S), -C - a * u ≤ stripDriver w v u) (hzC : z.re < -C - R) :
    ∃ u, IsForwardSol w (stripExp z) S u := by
  have hz₀ := stripExp_im_pos hz
  obtain ⟨amin, hamin, hamin_le⟩ := h.exists_pos_le_gap
  have he : 0 < 1 - Real.exp (-R) := by
    have : Real.exp (-R) < 1 := by simpa using Real.exp_lt_exp.2 (show -R < 0 by linarith)
    linarith
  refine exists_isForwardSol_of_forall_le_norm h.nonneg h.continuousOn_w ⟨h.nonneg, le_rfl⟩ hz₀
    (mul_pos hamin he) fun r hr hsolr => ?_
  have hr' : IsSepMark w v r := h.mono hr.1 hr.2
  have hrT : stripClock w v r ≤ stripClock w v S :=
    h.strictMonoOn_stripClock.monotoneOn hr ⟨h.nonneg, le_rfl⟩ hr.2
  have hcl : stripClock w v r ∈ Icc 0 (stripClock w v r) :=
    ⟨hr'.stripClock_nonneg ⟨hr.1, le_rfl⟩, le_rfl⟩
  have hre := hr'.re_stripMap_le_sub_mul hz hsolr hR.le hbR hab
    (fun u hu => hξ u ⟨hu.1, hu.2.trans hrT⟩) hzC _ hcl
  have hξr := hξ _ ⟨hcl.1, hcl.2.trans hrT⟩
  rw [hr'.fwdMap_eq_mul_exp_sub_one hz₀ hsolr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.2 (h.lt r hr))]
  set wψ := stripMap w v (stripClock w v r) z - stripDriver w v (stripClock w v r)
  have hX : wψ.re ≤ -R := by
    simp only [wψ, sub_re, ofReal_re]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) hcl.1]
  have h1 : 1 - Real.exp (-R) ≤ ‖exp wψ - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (exp wψ)
    rw [norm_exp, norm_one, norm_sub_rev] at this
    linarith [Real.exp_le_exp.2 hX]
  exact mul_le_mul (hamin_le r hr) h1 he.le (sub_pos.2 (h.lt r hr)).le

end IsSepMark

end Strip

namespace Zhan

open Strip

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **No point beyond `C + R` is ever swallowed during the strip life.** For a strip path whose strip driver
satisfies `|ξ_t| ≤ C + at`, with `a ≤ b ≤ tanh(R/2)` and `R > 0`, and every chordal time `s` of the strip life, the
chordal point `e^z − 1` of a strip point `z` with `|Re z| > C + R` has a forward solution on `[0, s]`. -/
theorem IsStripPath.exists_isForwardSol_of_sublinear (h : IsStripPath w v ζ) {C a b R : ℝ} (hR : 0 < R)
    (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ t : ℝ≥0, |stripDriver (extPath w) (extPath v) t| ≤ C + a * t) {s : ℝ≥0}
    (hs : IsStripLife w v ζ s) {z : ℂ} (hz : z ∈ piStrip) (hzC : C + R < |z.re|) :
    ∃ u, IsForwardSol (extPath w) (stripExp z) s u := by
  have hm := h.2.1 s hs
  have hξ' : ∀ u : ℝ, 0 ≤ u → |stripDriver (extPath w) (extPath v) u| ≤ C + a * u := fun u hu => by
    have := hξ u.toNNReal
    rwa [Real.coe_toNNReal _ hu] at this
  rcases lt_abs.1 hzC with hzr | hzl
  · exact hm.exists_isForwardSol_of_sublinear_right hz hR hbR hab
      (fun u hu => (le_abs_self _).trans (hξ' u hu.1)) hzr
  · exact hm.exists_isForwardSol_of_sublinear_left (C := C) (a := a) hz hR hbR hab
      (fun u hu => by have := neg_abs_le (stripDriver (extPath w) (extPath v) u); linarith [hξ' u hu.1])
      (by linarith)

/-- **No point beyond `C + R` is in any hull of the strip life.** -/
theorem IsStripPath.not_mem_fwdHull_of_sublinear (h : IsStripPath w v ζ) {C a b R : ℝ} (hR : 0 < R)
    (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ t : ℝ≥0, |stripDriver (extPath w) (extPath v) t| ≤ C + a * t) {s : ℝ≥0}
    (hs : IsStripLife w v ζ s) {z : ℂ} (hz : z ∈ piStrip) (hzC : C + R < |z.re|) :
    stripExp z ∉ fwdHull (extPath w) s := by
  obtain ⟨s', hss', hs'⟩ := h.exists_gt hs
  obtain ⟨u, hu⟩ := h.exists_isForwardSol_of_sublinear hR hbR hab hξ hs' hz hzC
  have hmem : stripExp z ∈ H \ fwdHull (extPath w) s :=
    (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff s.2).2 ⟨stripExp_im_pos hz, s', hss', u, hu⟩
  exact hmem.2

/-- A trace point in `ℍ` at a time of the strip life lies in every later hull of the strip life. -/
theorem IsStripPath.mem_fwdHull_of_trace (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {t t' : ℝ≥0} (htt' : t ≤ t')
    (ht' : IsStripLife w v ζ t') (hH : 0 < (η t).im) : η t ∈ fwdHull (extPath w) t' := by
  obtain ⟨s', hts', hs'⟩ := h.exists_gt ht'
  obtain ⟨-, -, hfill⟩ := hη s' hs'
  obtain ⟨⟨z, -, hcc⟩, -⟩ := hfill t' (ENNReal.coe_lt_coe.2 hts')
  by_contra hK
  have hmem : η t ∈ QuantumZipper.H \ fwdHull (fun s : ℝ => w s.toNNReal) t' := ⟨hH, hK⟩
  rw [← hcc] at hmem
  exact (connectedComponentIn_subset _ _ hmem).2 ⟨t, ⟨zero_le, htt'⟩, rfl⟩

/-- `log(1 + p)` is a strip point for `p ∈ ℍ`, and `stripExp (log (1 + p)) = p`. -/
theorem log_one_add_mem_piStrip {p : ℂ} (hp : 0 < p.im) :
    Complex.log (1 + p) ∈ piStrip ∧ stripExp (Complex.log (1 + p)) = p := by
  have him : (1 + p).im = p.im := by simp
  have hne : (1 + p) ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; rw [him, zero_im] at this; linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [log_im]
    have h1 : 0 ≤ arg (1 + p) := arg_nonneg_iff.2 (by rw [him]; exact hp.le)
    refine h1.lt_of_ne fun h0 => ?_
    have := (arg_eq_zero_iff.1 h0.symm).2
    rw [him] at this; linarith
  · rw [log_im]
    exact arg_lt_pi_iff.2 (Or.inr (by rw [him]; exact hp.ne'))
  · simp only [stripExp, exp_log hne, add_sub_cancel_left]

/-- **The bounded hull.** For a strip path whose strip driver satisfies `|ξ_t| ≤ C + at` (`a ≤ b ≤ tanh(R/2)`,
`R > 0`), every generating trace on the strip life satisfies `e^{−(C+R)} ≤ ‖1 + η_s‖ ≤ e^{C+R}` at every time `s`
of the strip life: the strip trace `log(1 + η)` stays in `[−C − R, C + R] × [0, π]`. -/
theorem IsStripPath.norm_one_add_trace_mem_Icc (h : IsStripPath w v ζ) {C a b R : ℝ} (hR : 0 < R)
    (hbR : b ≤ (Real.exp R - 1) / (Real.exp R + 1)) (hab : a ≤ b)
    (hξ : ∀ t : ℝ≥0, |stripDriver (extPath w) (extPath v) t| ≤ C + a * t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s : ℝ≥0}
    (hs : IsStripLife w v ζ s) :
    ‖1 + η s‖ ∈ Icc (Real.exp (-(C + R))) (Real.exp (C + R)) := by
  -- trace points in `ℍ`
  have hH : ∀ t : ℝ≥0, IsStripLife w v ζ t → 0 < (η t).im →
      ‖1 + η t‖ ∈ Icc (Real.exp (-(C + R))) (Real.exp (C + R)) := by
    intro t ht htH
    obtain ⟨hzS, hze⟩ := log_one_add_mem_piStrip htH
    have hne : (1 + η t) ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; linarith
    have hnorm : 0 < ‖1 + η t‖ := norm_pos_iff.2 hne
    have hle : |(Complex.log (1 + η t)).re| ≤ C + R := by
      by_contra hlt
      push Not at hlt
      have hK := h.mem_fwdHull_of_trace hη le_rfl ht htH
      rw [← hze] at hK
      exact h.not_mem_fwdHull_of_sublinear hR hbR hab hξ ht hzS hlt hK
    rw [log_re] at hle
    obtain ⟨h1, h2⟩ := abs_le.1 hle
    refine ⟨?_, ?_⟩
    · calc Real.exp (-(C + R)) ≤ Real.exp (Real.log ‖1 + η t‖) := Real.exp_le_exp.2 h1
        _ = ‖1 + η t‖ := Real.exp_log hnorm
    · calc ‖1 + η t‖ = Real.exp (Real.log ‖1 + η t‖) := (Real.exp_log hnorm).symm
        _ ≤ Real.exp (C + R) := Real.exp_le_exp.2 h2
  -- every time: approximate from the right by trace points in `ℍ`
  by_contra hns
  obtain ⟨s', hss', hs'⟩ := h.exists_gt hs
  have hηs' := hη s' hs'
  have hw := h.continuousOn_lt hs'
  have hw0 : w 0 = 0 := h.1
  have hcont : ContinuousWithinAt (fun t => ‖1 + η t‖) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s'} s :=
    (continuous_norm.comp_continuousOn (continuousOn_const.add hηs'.2.1)) s
      (show ((s : ℝ≥0) : ℝ≥0∞) ≤ s' from ENNReal.coe_le_coe.2 hss'.le)
  have hopen : IsOpen (Icc (Real.exp (-(C + R))) (Real.exp (C + R)))ᶜ := isClosed_Icc.isOpen_compl
  have hev := hcont.preimage_mem_nhdsWithin (hopen.mem_nhds hns)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- a time `t ∈ (s, s + ε) ∩ (s, s')` with `η t ∈ ℍ`
  set b' : ℝ≥0 := min s' (s + (ε / 2).toNNReal) with hb'
  have hsb' : s < b' := lt_min hss' (by
    have : (0 : ℝ≥0) < (ε / 2).toNNReal := Real.toNNReal_pos.2 (by linarith)
    exact lt_add_of_pos_right s this)
  obtain ⟨t, ⟨hst, htb⟩, htH⟩ :=
    Restart.IsGeneratingTrace.exists_mem_H hηs' hw hw0 hsb' (ENNReal.coe_le_coe.2 (min_le_left _ _))
  have hts' : t ≤ s' := htb.le.trans (min_le_left _ _)
  have ht : IsStripLife w v ζ t := hs'.mono hts'
  refine hball ⟨?_, show ((t : ℝ≥0) : ℝ≥0∞) ≤ s' from ENNReal.coe_le_coe.2 hts'⟩ (hH t ht htH)
  rw [Metric.mem_ball, NNReal.dist_eq]
  have h1 : (t : ℝ) ≤ s + ε / 2 := by
    have := htb.le.trans (min_le_right s' _)
    have h2 : ((s + (ε / 2).toNNReal : ℝ≥0) : ℝ) = s + ε / 2 := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)]
    exact (NNReal.coe_le_coe.2 this).trans h2.le
  have h2 : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
  rw [abs_lt]; constructor <;> linarith

end Zhan

end InteractingSLE
