/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelBH
import InteractingSLE.Spec.Supplement.GW2JointKernel
import InteractingSLE.Spec.Sec5.Prop51HQPost

/-!
# GB6's retained chart is a retained chart landing off a finite set

Packet PROVE-Q3-REL. In GB6 the retained set, read in the counterflow's frame `w = −1/z`, is the inverted flow hull
`A = invHull U σ = −1/K_σ` (`U` the flow's driver, `σ` its stop), and its chart is GB6's relative map
`Ψ = relMap U σ = −1/f_σ(−1/·)` with inverse `Ψi = relInv U σ = −1/f_σ⁻¹(−1/·)` (= GW2's `jointChart U σ`). The set `A`
is unbounded, and `Ψi` tends to `∞` at the images `−1/chartAL`, `−1/chartAR` of the two sides of the flow's base
(`not_tendsto_relInv`, the reason PROVE-BHMEAN's `IsRetainedChart` does not apply). This file proves
**`isRetainedChartOff_relMap`**: `(Ψ, Ψi, relLog)` is an `IsRetainedChartOff` with exceptional set
`relBad U σ = {−1/chartAL, −1/chartAR} ∖ {0}`, for a flow trace that does not return to its base before `σ`; and
**`relBad_notMem_closure`**: the exceptional points lie off the closed relative hull of every explored hull whose
closure misses `cl A`.

* `invHull`, `compl_invHull` (`ℍ ∖ A = −1/(ℍ ∖ K_σ)`), `isDomainChart_rel`;
* `relLog` (`log Ψ' = log f_σ'(−1/w) + 2 log(−1/w) − 2 log f_σ(−1/w)`, principal logarithms), `isDerivLog_relLog`,
  `tendsto_im_relLog` (the lift vanishes on the real axis off `cl A`, at real points `≠ 0`);
* `exists_tendsto_fwdMap_real` (a real point off the closed hull is sent to a real point of the same sign),
  `tendsto_relMap` (`Ψ` lands at every real point off `cl A`), `tendsto_relInv` (`Ψi` lands off `relBad`, using the no
  return of the flow to `0`: `Prop49Exit.extendFrom_ne_zero_of_noReturn` and its left twin);
* `lt_re_fwdMap_of_pos` (strictly right of `chartAR`), `relBad_notMem_closure`.

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric Complex Bornology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Supp8.Q3Rel

open GB6 (relMap relInv)
open WangWu (chartAL chartAR)

/-- **GB6's retained set in the counterflow's frame**: the inverted flow hull `−1/K_σ`. -/
def invHull (U : ℝ → ℝ) (σ : ℝ) : Set ℂ := (fun z : ℂ => -z⁻¹) '' fwdHull U σ

/-- **The logarithm of the relative map's derivative**, normalized to vanish on the real axis:
`log f_σ'(−1/w) + 2 log(−1/w) − 2 log f_σ(−1/w)`. -/
def relLog (U : ℝ → ℝ) (σ : ℝ) (w : ℂ) : ℂ :=
  logDerivFwd U σ (-w⁻¹) + 2 * Complex.log (-w⁻¹) - 2 * Complex.log (fwdMap U σ (-w⁻¹))

/-- **The exceptional points of GB6's retained chart**: the images `−1/chartAL`, `−1/chartAR` of the two sides of the
flow's base (other than `0`). -/
def relBad (U : ℝ → ℝ) (σ : ℝ) : Finset ℝ := ({-(chartAL U σ)⁻¹, -(chartAR U σ)⁻¹} : Finset ℝ).erase 0

variable {U : ℝ → ℝ} {α : ℝ → ℂ} {σ : ℝ}

theorem neg_inv_injective : Function.Injective fun z : ℂ => -z⁻¹ := fun a b h => by
  have := congrArg (fun z : ℂ => -z⁻¹) h
  simpa only [GB6.neg_inv_neg_inv] using this

theorem neg_inv_neg_inv_real (y : ℝ) : -(-y⁻¹)⁻¹ = y := by rw [inv_neg, inv_inv, neg_neg]

/-- `ℍ ∖ A = −1/(ℍ ∖ K_σ)`. -/
theorem compl_invHull : H \ invHull U σ = (fun z : ℂ => -z⁻¹) '' (H \ fwdHull U σ) := by
  ext w
  constructor
  · rintro ⟨hwH, hwA⟩
    exact ⟨-w⁻¹, ⟨GB6.neg_inv_mem_H hwH, fun hK => hwA ⟨-w⁻¹, hK, GB6.neg_inv_neg_inv w⟩⟩, GB6.neg_inv_neg_inv w⟩
  · rintro ⟨z, ⟨hzH, hzK⟩, rfl⟩
    refine ⟨GB6.neg_inv_mem_H hzH, ?_⟩
    rintro ⟨z', hz', he⟩
    exact hzK (neg_inv_injective he ▸ hz')

theorem negInv_mem_compl {w : ℂ} (hw : w ∈ H \ invHull U σ) : -w⁻¹ ∈ H \ fwdHull U σ :=
  ⟨GB6.neg_inv_mem_H hw.1, fun hK => hw.2 ⟨-w⁻¹, hK, GB6.neg_inv_neg_inv w⟩⟩

/-- GW2's joint chart is a chart of `ℍ ∖ A`. -/
theorem isDomainChart_rel (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) :
    IsDomainChart (H \ invHull U σ) (Theorem14.GW2JointKernel.jointChart U σ) := by
  rw [compl_invHull]
  exact Theorem14.GW2JointKernel.isDomainChart_jointChart hU hU0 hσ

theorem mem_slitPlane_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (ne_of_gt hz))

theorem hasDerivAt_negInv {w : ℂ} (hw : w ≠ 0) : HasDerivAt (fun w : ℂ => -w⁻¹) ((w ^ 2)⁻¹) w := by
  have h := (hasDerivAt_inv hw).neg
  rw [neg_neg] at h
  exact h

/-! ### The logarithm of the derivative -/

theorem isDerivLog_relLog (hU : Continuous U) (hσ : 0 ≤ σ) :
    IsDerivLog (relMap U σ) (relLog U σ) (H \ invHull U σ) := by
  have hdF : ∀ z ∈ H \ fwdHull U σ, DifferentiableAt ℂ (fwdMap U σ) z := fun z hz =>
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hU hσ).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hU hσ).mem_nhds hz)
  have hdL : ∀ z ∈ H \ fwdHull U σ, DifferentiableAt ℂ (logDerivFwd U σ) z := fun z hz =>
    (isDerivLog_fwdMap hU hσ).1.differentiableAt ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hU hσ).mem_nhds hz)
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have hz := negInv_mem_compl hw
    have hw0 : w ≠ 0 := GB6.ne_zero_of_mem_H hw.1
    have hR : DifferentiableAt ℂ (fun w : ℂ => -w⁻¹) w := (differentiableAt_inv hw0).neg
    have h1 := DifferentiableAt.comp (g := logDerivFwd U σ) w (hdL _ hz) hR
    have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.log (-w⁻¹)) w := hR.clog (mem_slitPlane_of_mem_H hz.1)
    have hFR := DifferentiableAt.comp (g := fwdMap U σ) w (hdF _ hz) hR
    have h3 := hFR.clog (show (fwdMap U σ ∘ fun w : ℂ => -w⁻¹) w ∈ Complex.slitPlane from
      mem_slitPlane_of_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ hz))
    exact ((h1.add (h2.const_mul 2)).sub (h3.const_mul 2)).differentiableWithinAt
  · have hz := negInv_mem_compl hw
    have hw0 : w ≠ 0 := GB6.ne_zero_of_mem_H hw.1
    have hz0 : -w⁻¹ ≠ 0 := GB6.ne_zero_of_mem_H hz.1
    have hFz : fwdMap U σ (-w⁻¹) ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ hz
    have hF0 : fwdMap U σ (-w⁻¹) ≠ 0 := GB6.ne_zero_of_mem_H hFz
    have hd : HasDerivAt (relMap U σ)
        ((fwdMap U σ (-w⁻¹) ^ 2)⁻¹ * (deriv (fwdMap U σ) (-w⁻¹) * (w ^ 2)⁻¹)) w := by
      have hR := hasDerivAt_negInv hw0
      have h2 := (hdF _ hz).hasDerivAt.comp w hR
      have h3 := (hasDerivAt_negInv hF0).comp w h2
      exact h3
    rw [hd.deriv]
    have e1 : Complex.exp (2 * Complex.log (-w⁻¹)) = (-w⁻¹) ^ 2 := by
      rw [show (2 : ℂ) * Complex.log (-w⁻¹) = ((2 : ℕ) : ℂ) * Complex.log (-w⁻¹) by norm_num, Complex.exp_nat_mul,
        Complex.exp_log hz0]
    have e2 : Complex.exp (2 * Complex.log (fwdMap U σ (-w⁻¹))) = fwdMap U σ (-w⁻¹) ^ 2 := by
      rw [show (2 : ℂ) * Complex.log (fwdMap U σ (-w⁻¹)) = ((2 : ℕ) : ℂ) * Complex.log (fwdMap U σ (-w⁻¹)) by
        norm_num, Complex.exp_nat_mul, Complex.exp_log hF0]
    have e3 : (-w⁻¹) ^ 2 = (w ^ 2)⁻¹ := by rw [neg_sq, inv_pow]
    simp only [relLog]
    rw [Complex.exp_sub, Complex.exp_add, (isDerivLog_fwdMap hU hσ).2 _ hz, e1, e2, e3]
    ring

theorem im_relLog (w : ℂ) :
    (relLog U σ w).im = (logDerivFwd U σ (-w⁻¹)).im + 2 * Complex.arg (-w⁻¹) -
      2 * Complex.arg (fwdMap U σ (-w⁻¹)) := by
  simp only [relLog, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.log_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, add_zero]

/-! ### Real points off the closed hull -/

/-- **A real point off the closed hull is sent to a real point of the same sign**, as the limit of `f_σ`. -/
theorem exists_tendsto_fwdMap_real (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {x : ℝ} (hx0 : x ≠ 0)
    (hxK : (x : ℂ) ∉ closure (fwdHull U σ)) :
    ∃ v : ℝ, (0 < x → 0 < v) ∧ (x < 0 → v < 0) ∧ Tendsto (fwdMap U σ) (𝓝[H] (x : ℂ)) (𝓝 (v : ℂ)) := by
  obtain ⟨u, hu⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hσ hxK hx0
  have hlim := tendsto_fwdMap_of_isForwardSol_real hU hU0 hσ hu
  have him : (u σ).im = 0 := im_eq_zero_of_isForwardSol_real hU hu ⟨hσ, le_rfl⟩
  have hne : u σ ≠ 0 := (hu.2 σ ⟨hσ, le_rfl⟩).1
  have heq : fwdMap U σ (x : ℂ) = u σ := fwdMap_eq_of_isForwardSol hU hu ⟨hσ, le_rfl⟩
  have hur : u σ = ((u σ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hre0 : (u σ).re ≠ 0 := fun h => hne (by rw [hur, h]; simp)
  refine ⟨(u σ).re, fun hpos => ?_, fun hneg => ?_, by rw [← hur]; exact hlim⟩
  · have h1 := WangWu.rightImg_sub_le_re_fwdMap hU hU0 hσ hpos hu
    have h2 := WangWu.chartAR_nonneg hU hσ
    rw [WangWu.chartAR] at h2
    rw [heq] at h1
    exact lt_of_le_of_ne (by linarith) (Ne.symm hre0)
  · have h1 := WangWu.re_fwdMap_le_neg_rightImg hU hU0 hσ hneg hu
    have h2 := WangWu.chartAL_nonpos hU hσ
    rw [WangWu.chartAL] at h2
    rw [heq] at h1
    exact lt_of_le_of_ne (by linarith) hre0

/-- **Strictly right of the right base image**: a positive real point off the closed hull is sent strictly right of
`chartAR` (the real flow is strictly increasing and the alive points form an open set). -/
theorem lt_re_fwdMap_of_pos (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {x : ℝ} (hx : 0 < x)
    (hxK : (x : ℂ) ∉ closure (fwdHull U σ)) : chartAR U σ < (fwdMap U σ (x : ℂ)).re := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_closure (s := fwdHull U σ)).isOpen_compl (x : ℂ) hxK
  set x' : ℝ := max (x / 2) (x - r / 2) with hx'def
  have hx'0 : 0 < x' := lt_max_of_lt_left (by linarith)
  have hx'x : x' < x := max_lt (by linarith) (by linarith)
  have hx'K : (x' : ℂ) ∉ closure (fwdHull U σ) := hball (by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [le_max_right (x / 2) (x - r / 2)])
  obtain ⟨u, hu⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hσ hxK hx.ne'
  obtain ⟨u', hu'⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hσ hx'K hx'0.ne'
  have h1 := WangWu.rightImg_sub_le_re_fwdMap hU hU0 hσ hx'0 hu'
  have h2 := WangWu.re_fwdMap_lt_re_fwdMap hU hU0 hσ hx'x (Or.inl hx'0) hu' hu
  rw [WangWu.chartAR]
  linarith

/-- **Strictly left of the left base image** (the reflection of `lt_re_fwdMap_of_pos`). -/
theorem re_fwdMap_lt_of_neg (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {x : ℝ} (hx : x < 0)
    (hxK : (x : ℂ) ∉ closure (fwdHull U σ)) : (fwdMap U σ (x : ℂ)).re < chartAL U σ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_closure (s := fwdHull U σ)).isOpen_compl (x : ℂ) hxK
  set x' : ℝ := min (x / 2) (x + r / 2) with hx'def
  have hx'0 : x' < 0 := min_lt_of_left_lt (by linarith)
  have hx'x : x < x' := lt_min (by linarith) (by linarith)
  have hx'K : (x' : ℂ) ∉ closure (fwdHull U σ) := hball (by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [min_le_right (x / 2) (x + r / 2)])
  obtain ⟨u, hu⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hσ hxK hx.ne
  obtain ⟨u', hu'⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hσ hx'K hx'0.ne
  have h1 := WangWu.re_fwdMap_le_neg_rightImg hU hU0 hσ hx'0 hu'
  have h2 := WangWu.re_fwdMap_lt_re_fwdMap hU hU0 hσ hx'x (Or.inr hx'0) hu hu'
  rw [WangWu.chartAL]
  linarith

/-- A real point `y ≠ 0` off `cl A` inverts to a real point off `cl K_σ`. -/
theorem negInv_notMem_closure {y : ℝ} (hy0 : y ≠ 0) (hyA : (y : ℂ) ∉ closure (invHull U σ)) :
    (((-y⁻¹ : ℝ)) : ℂ) ∉ closure (fwdHull U σ) := by
  intro hK
  apply hyA
  have hx0 : ((-y⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, neg_eq_zero, inv_eq_zero]; exact hy0
  have hc : ContinuousAt (fun z : ℂ => -z⁻¹) ((-y⁻¹ : ℝ) : ℂ) := (continuousAt_inv₀ hx0).neg
  have h := mem_closure_image hc hK
  have e : -(((-y⁻¹ : ℝ) : ℂ))⁻¹ = (y : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_neg, neg_inv_neg_inv_real]
  change -(((-y⁻¹ : ℝ) : ℂ))⁻¹ ∈ closure ((fun z : ℂ => -z⁻¹) '' fwdHull U σ) at h
  rw [e] at h
  exact h

/-- The inversion takes the domain near a real `y ≠ 0` to `ℍ` near `−1/y`. -/
theorem tendsto_negInv_real {y : ℝ} (hy0 : y ≠ 0) {S : Set ℂ} (hS : S ⊆ H) :
    Tendsto (fun w : ℂ => -w⁻¹) (𝓝[S] (y : ℂ)) (𝓝[H] (((-y⁻¹ : ℝ)) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => GB6.neg_inv_mem_H (hS hw)⟩
  have hc : ContinuousAt (fun z : ℂ => -z⁻¹) (y : ℂ) :=
    (continuousAt_inv₀ (by exact_mod_cast hy0)).neg
  have e : (((-y⁻¹ : ℝ)) : ℂ) = -(y : ℂ)⁻¹ := by push_cast; ring
  rw [e]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The argument at a real point `p ≠ 0`, approached from `ℍ`: `0` if `p > 0`, `π` if `p < 0`. -/
theorem tendsto_arg_real {p : ℝ} (hp : p ≠ 0) :
    Tendsto Complex.arg (𝓝[H] (p : ℂ)) (𝓝 (if 0 < p then 0 else Real.pi)) := by
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · simp only [not_lt.2 hneg.le, ↓reduceIte]
    exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (by simpa using hneg) (by simp)).mono_left
      (nhdsWithin_mono _ fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz)
  · simp only [hpos, ↓reduceIte]
    have hs : (p : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hpos))
    have h0 : Complex.arg (p : ℂ) = 0 := Complex.arg_ofReal_of_nonneg hpos.le
    have h := (Complex.continuousAt_arg hs).tendsto
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds

/-- **The lift `Im relLog` vanishes on the real axis** at every real `y ≠ 0` off `cl A`. -/
theorem tendsto_im_relLog (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {y : ℝ} (hy0 : y ≠ 0)
    (hyA : (y : ℂ) ∉ closure (invHull U σ)) :
    Tendsto (fun w => (relLog U σ w).im) (𝓝[H \ invHull U σ] (y : ℂ)) (𝓝 0) := by
  set x : ℝ := -y⁻¹ with hxdef
  have hx0 : x ≠ 0 := by simp [hxdef, hy0]
  have hxK : (x : ℂ) ∉ closure (fwdHull U σ) := negInv_notMem_closure hy0 hyA
  have hRt : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[H \ invHull U σ] (y : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_negInv_real hy0 sdiff_subset
  have ha := (BHMean.tendsto_im_logDerivFwd_of_notMem_closure hU hU0 hσ hxK).comp hRt
  obtain ⟨v, hvp, hvn, hFv⟩ := exists_tendsto_fwdMap_real hU hU0 hσ hx0 hxK
  have hv0 : v ≠ 0 := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · exact (hvn h).ne
    · exact (hvp h).ne'
  have hFt : Tendsto (fun w => fwdMap U σ (-w⁻¹)) (𝓝[H \ invHull U σ] (y : ℂ)) (𝓝[H] (v : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hFv.comp hRt, eventually_nhdsWithin_of_forall fun w hw =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ (negInv_mem_compl hw)⟩
  have hsame : (if 0 < x then (0 : ℝ) else Real.pi) = if 0 < v then 0 else Real.pi := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · simp only [not_lt.2 h.le, not_lt.2 (hvn h).le, ↓reduceIte]
    · simp only [h, hvp h, ↓reduceIte]
  have hsum := (ha.add ((tendsto_arg_real hx0).comp hRt |>.const_mul 2)).sub
    ((tendsto_arg_real hv0).comp hFt |>.const_mul 2)
  rw [hsame, add_sub_assoc, sub_self, zero_add] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun w _ => ?_)
  show _ = (relLog U σ w).im
  rw [im_relLog]
  simp only [Function.comp]

/-! ### Landing of the chart and of its inverse -/

/-- **`Ψ` lands at every real point off `cl A`.** -/
theorem tendsto_relMap (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {y : ℝ}
    (hyA : (y : ℂ) ∉ closure (invHull U σ)) :
    ∃ x : ℝ, Tendsto (relMap U σ) (𝓝[H \ invHull U σ] (y : ℂ)) (𝓝 (x : ℂ)) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨0, ?_⟩
    obtain ⟨C, -, hC⟩ := WangWu.exists_norm_fwdMap_sub_le hU hU0 hσ
    -- `−1/w → ∞` inside `ℍ ∖ K_σ`, `f_σ` moves points by at most `C`, so `f_σ(−1/w) → ∞` and `Ψ(w) → 0`
    have h1 : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[H \ invHull U σ] ((0 : ℝ) : ℂ)) (cobounded ℂ) := by
      rw [Complex.ofReal_zero]
      exact Filter.tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left
        (nhdsWithin_mono _ fun w hw => GB6.ne_zero_of_mem_H hw.1))
    have h2 : Tendsto (fun w => fwdMap U σ (-w⁻¹)) (𝓝[H \ invHull U σ] ((0 : ℝ) : ℂ)) (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C)
        (tendsto_norm_atTop_iff_cobounded.2 h1))
      filter_upwards [self_mem_nhdsWithin] with w hw
      have := hC _ (negInv_mem_compl hw)
      have h3 := norm_sub_norm_le (-w⁻¹) (fwdMap U σ (-w⁻¹))
      rw [norm_sub_rev] at this
      linarith
    have h4 := (tendsto_inv₀_cobounded.comp h2).neg
    rw [neg_zero] at h4
    have h5 : Tendsto (relMap U σ) (𝓝[H \ invHull U σ] ((0 : ℝ) : ℂ)) (𝓝 0) := h4
    rw [Complex.ofReal_zero] at h5 ⊢
    exact h5
  · set x : ℝ := -y⁻¹ with hxdef
    have hx0 : x ≠ 0 := by simp [hxdef, hy0]
    have hxK : (x : ℂ) ∉ closure (fwdHull U σ) := negInv_notMem_closure hy0 hyA
    obtain ⟨v, hvp, hvn, hFv⟩ := exists_tendsto_fwdMap_real hU hU0 hσ hx0 hxK
    have hv0 : (v : ℂ) ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact_mod_cast (hvn h).ne
      · exact_mod_cast (hvp h).ne'
    refine ⟨-v⁻¹, ?_⟩
    have h := ((continuousAt_inv₀ hv0).neg.tendsto).comp
      (hFv.comp (tendsto_negInv_real hy0 (sdiff_subset : H \ invHull U σ ⊆ H)))
    have e : (-Inv.inv : ℂ → ℂ) (v : ℂ) = (((-v⁻¹ : ℝ)) : ℂ) := by
      simp only [Pi.neg_apply]; push_cast; ring
    rw [e] at h
    exact h

/-- The relative inverse is the inverse of GW2's joint chart. -/
theorem relInv_eq (v : ℂ) : relInv U σ v = (Theorem14.GW2JointKernel.jointChart U σ).2.1 v := rfl

/-- **`Ψi` lands at every real point off the exceptional set**, for a flow trace that does not return to `0`. -/
theorem tendsto_relInv (hU : Continuous U) (hU0 : U 0 = 0) (hα : IsLoewnerTrace U α) (hσ : 0 < σ)
    (hNR : ∀ v ∈ Ioc 0 σ, α v ≠ 0) {y : ℝ} (hy : y ∉ relBad U σ) :
    ∃ p, Tendsto (relInv U σ) (𝓝[H] (y : ℂ)) (𝓝 p) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨0, ?_⟩
    have h1 : Tendsto (fun v : ℂ => -v⁻¹) (𝓝[H] ((0 : ℝ) : ℂ)) (cobounded ℂ ⊓ 𝓟 H) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_nhdsWithin_of_forall fun v hv =>
        GB6.neg_inv_mem_H hv)⟩
      rw [Complex.ofReal_zero]
      exact Filter.tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left
        (nhdsWithin_mono _ fun v hv => GB6.ne_zero_of_mem_H hv))
    have h2 := (InteractingSLE.tendsto_fwdMapInv_cobounded hU hU0 hσ.le).comp h1
    have h3 := (tendsto_inv₀_cobounded.comp h2).neg
    rw [neg_zero] at h3
    exact h3
  · set x : ℝ := -y⁻¹ with hxdef
    have hx0 : x ≠ 0 := by simp [hxdef, hy0]
    have hxb : (x : ℂ) ∈ Hbar := RelTrans.ofReal_mem_Hbar x
    have hlim := (hα.hasBdryLimits hU hU0 hσ.le).tendsto hxb
    set p₀ := extendFrom H (fwdMapInv U σ) (x : ℂ) with hp₀def
    have hxAR : x ≠ chartAR U σ := fun h => hy (Finset.mem_erase.2 ⟨hy0, by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      rw [← h, hxdef, neg_inv_neg_inv_real]⟩)
    have hxAL : x ≠ chartAL U σ := fun h => hy (Finset.mem_erase.2 ⟨hy0, by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      rw [← h, hxdef, neg_inv_neg_inv_real]⟩)
    have h0K : (0 : ℂ) ∈ closure (fwdHull U σ) := ConformalImageFull.zero_mem_closure_fwdHull hU hU0 hσ
    have hp0 : p₀ ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rcases lt_or_gt_of_ne hxAL with hl | hl
        · exact fun h => RelTrans.extendFrom_notMem_closure_of_lt_chartAL hα hU hU0 hσ.le hl
            (show p₀ ∈ closure (fwdHull U σ) by rw [h]; exact h0K)
        · exact Sec5.Prop51H.extendFrom_ne_zero_of_noReturn_left hα hU hU0 hσ hNR hneg (by
            rw [WangWu.chartAL] at hl; exact hl)
      · rcases lt_or_gt_of_ne hxAR with hr | hr
        · exact Sec5.Prop49Exit.extendFrom_ne_zero_of_noReturn hα hU hU0 hσ hNR hpos (by
            rw [WangWu.chartAR] at hr; exact hr)
        · exact fun h => RelTrans.extendFrom_notMem_closure_of_chartAR_lt hα hU hU0 hσ.le hr
            (show p₀ ∈ closure (fwdHull U σ) by rw [h]; exact h0K)
    refine ⟨-p₀⁻¹, ?_⟩
    have hF : Tendsto (fun v => fwdMapInv U σ (-v⁻¹)) (𝓝[H] (y : ℂ)) (𝓝 p₀) :=
      hlim.comp (tendsto_negInv_real hy0 subset_rfl)
    exact ((continuousAt_inv₀ hp0).neg.tendsto).comp hF

/-- **`Ψi` does not land at an exceptional point** when the flow's base is accessible there (the reason
`BHMean.IsRetainedChart` fails for GB6): if `f̄_σ⁻¹(−1/y) = 0` for a real `y ≠ 0`, then `‖Ψi‖ → ∞` at `y`. -/
theorem not_tendsto_relInv (hU : Continuous U) (hU0 : U 0 = 0) (hα : IsLoewnerTrace U α) (hσ : 0 ≤ σ) {y : ℝ}
    (hy0 : y ≠ 0) (hbase : extendFrom H (fwdMapInv U σ) (((-y⁻¹ : ℝ)) : ℂ) = 0) :
    Tendsto (relInv U σ) (𝓝[H] (y : ℂ)) (cobounded ℂ) := by
  have hlim := (hα.hasBdryLimits hU hU0 hσ).tendsto (RelTrans.ofReal_mem_Hbar (-y⁻¹))
  rw [hbase] at hlim
  have hF : Tendsto (fun v => fwdMapInv U σ (-v⁻¹)) (𝓝[H] (y : ℂ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim.comp (tendsto_negInv_real hy0 subset_rfl), eventually_nhdsWithin_of_forall
      fun v hv => GB6.ne_zero_of_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hσ (GB6.neg_inv_mem_H hv))⟩
  exact Filter.tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.comp hF)

/-! ### The chart -/

/-- **GB6's retained chart lands off the exceptional set**: for a flow driver `U` with Loewner trace `α` not returning
to `0` on `(0, σ]`, `(relMap U σ, relInv U σ, relLog U σ)` is a retained chart of `invHull U σ` landing off
`relBad U σ`. -/
theorem isRetainedChartOff_relMap (hU : Continuous U) (hU0 : U 0 = 0) (hα : IsLoewnerTrace U α) (hσ : 0 < σ)
    (hNR : ∀ v ∈ Ioc 0 σ, α v ≠ 0) :
    IsRetainedChartOff (invHull U σ) (relMap U σ) (relInv U σ) (relLog U σ) (relBad U σ) := by
  have hD := isDomainChart_rel hU hU0 hσ.le
  exact ⟨hD.isOpen, hD.isConformalBijection, fun v hv => hD.inv_mem hv, fun v hv => hD.fwd_inv hv,
    hD.isConformal.1, isDerivLog_relLog hU hσ.le, fun y hy => tendsto_relInv hU hU0 hα hσ hNR hy,
    fun y hy => tendsto_relMap hU hU0 hσ.le hy, fun y hy0 hy => tendsto_im_relLog hU hU0 hσ.le hy0 hy⟩

/-! ### The exceptional points lie off the closed relative hull -/

/-- The limit of `f_σ` at a real point `x ≠ 0` off the closed hull is the real number `Re f_σ(x)`. -/
theorem tendsto_fwdMap_re (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {x : ℝ} (hx0 : x ≠ 0)
    (hxK : (x : ℂ) ∉ closure (fwdHull U σ)) :
    Tendsto (fwdMap U σ) (𝓝[H] (x : ℂ)) (𝓝 (((fwdMap U σ (x : ℂ)).re : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := BHMean.exists_isForwardSol_of_notMem_closure hU hU0 hσ hxK hx0
  have hlim := tendsto_fwdMap_of_isForwardSol_real hU hU0 hσ hu
  have him : (u σ).im = 0 := im_eq_zero_of_isForwardSol_real hU hu ⟨hσ, le_rfl⟩
  have heq : fwdMap U σ (x : ℂ) = u σ := fwdMap_eq_of_isForwardSol hU hu ⟨hσ, le_rfl⟩
  have hur : u σ = ((u σ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [heq, ← hur]
  exact hlim

/-- **The exceptional points of GB6's retained chart lie off the closed relative hull** of every explored hull `K_t`
(a hull of a continuous driver from `0`) whose closure misses `cl A`, with `Ψ(K_t) = K̃_u`: a limit point of `Ψ(K_t)`
is `Ψ(z)` for `z ∈ ℍ ∖ A` (not real), `0` (the limit at `0`), or `−1/Re f_σ(−1/y)` for a real `y ≠ 0` off `cl A`, where
`Re f_σ(−1/y)` lies strictly outside `[chartAL, chartAR]`. -/
theorem relBad_notMem_closure (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) {Wr : ℝ → ℝ} {u : ℝ} (hK : relMap U σ '' fwdHull W t = fwdHull Wr u)
    (hd : Disjoint (closure (fwdHull W t)) (closure (invHull U σ))) :
    ∀ b ∈ relBad U σ, (b : ℂ) ∉ closure (fwdHull Wr u) := by
  intro b hb hbK
  obtain ⟨hb0, hbc⟩ := Finset.mem_erase.1 hb
  have hbc' : b = -(chartAL U σ)⁻¹ ∨ b = -(chartAR U σ)⁻¹ := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hbc
  rw [← hK] at hbK
  obtain ⟨q, hqK, hqb⟩ := mem_closure_iff_seq_limit.1 hbK
  choose z hzK hzq using hqK
  have hKsub : fwdHull W t ⊆ H \ invHull U σ := BHMean.fwdHull_subset_compl hd hW ht
  have hcpt : IsCompact (closure (fwdHull W t)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_fwdHull hW t).closure
  obtain ⟨zs, hzs, φ, hφ, hlim⟩ := hcpt.tendsto_subseq fun n => subset_closure (hzK n)
  have hzsA : zs ∉ closure (invHull U σ) := Set.disjoint_left.1 hd hzs
  have hseq : Tendsto (fun n => z (φ n)) atTop (𝓝[H \ invHull U σ] zs) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hKsub (hzK (φ n))⟩
  have hqφ : Tendsto (fun n => relMap U σ (z (φ n))) atTop (𝓝 (b : ℂ)) := by
    have := hqb.comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact (hzq (φ n)).symm
  have hD := isDomainChart_rel hU hU0 hσ
  have hzsb : zs ∈ Hbar := by
    have : closure (fwdHull W t) ⊆ Hbar := by
      rw [← closure_H]; exact closure_mono fun z hz => (hKsub hz).1
    exact this hzs
  by_cases hzsH : zs ∈ H
  · -- an interior limit point is sent into `ℍ`
    have hzsD : zs ∈ H \ invHull U σ := ⟨hzsH, fun h => hzsA (subset_closure h)⟩
    have hc : ContinuousAt (relMap U σ) zs :=
      (hD.differentiableOn_fwd.differentiableAt (hD.isOpen.mem_nhds hzsD)).continuousAt
    have h1 : Tendsto (fun n => relMap U σ (z (φ n))) atTop (𝓝 (relMap U σ zs)) :=
      hc.tendsto.comp (tendsto_nhdsWithin_iff.1 hseq).1
    have he := tendsto_nhds_unique h1 hqφ
    have hpos : (0 : ℝ) < (relMap U σ zs).im := hD.fwd_mem hzsD
    rw [he] at hpos
    simp at hpos
  · have hzsim : zs.im = 0 := le_antisymm (not_lt.1 hzsH) hzsb
    have hzsr : zs = (zs.re : ℂ) := Complex.ext (by simp) (by simp [hzsim])
    set y : ℝ := zs.re with hydef
    have hyA : (y : ℂ) ∉ closure (invHull U σ) := by rw [← hzsr]; exact hzsA
    rw [hzsr] at hseq
    rcases eq_or_ne y 0 with hy0 | hy0
    · -- the limit at `0` is `0`
      have hR : Tendsto (fun w : ℂ => -w⁻¹) (𝓝[H \ invHull U σ] (y : ℂ)) (cobounded ℂ) := by
        rw [hy0, Complex.ofReal_zero]
        exact Filter.tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left
          (nhdsWithin_mono _ fun w hw => GB6.ne_zero_of_mem_H hw.1))
      obtain ⟨C, -, hC⟩ := WangWu.exists_norm_fwdMap_sub_le hU hU0 hσ
      have h2 : Tendsto (fun w => fwdMap U σ (-w⁻¹)) (𝓝[H \ invHull U σ] (y : ℂ)) (cobounded ℂ) := by
        rw [← tendsto_norm_atTop_iff_cobounded]
        refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C)
          (tendsto_norm_atTop_iff_cobounded.2 hR))
        filter_upwards [self_mem_nhdsWithin] with w hw
        have := hC _ (negInv_mem_compl hw)
        have h3 := norm_sub_norm_le (-w⁻¹) (fwdMap U σ (-w⁻¹))
        rw [norm_sub_rev] at this
        linarith
      have h4 := (tendsto_inv₀_cobounded.comp h2).neg
      rw [neg_zero] at h4
      have h5 : Tendsto (relMap U σ) (𝓝[H \ invHull U σ] (y : ℂ)) (𝓝 0) := h4
      have he := tendsto_nhds_unique (h5.comp hseq) hqφ
      exact hb0 (by exact_mod_cast he.symm)
    · set x₀ : ℝ := -y⁻¹ with hx₀def
      have hx₀0 : x₀ ≠ 0 := by simp [hx₀def, hy0]
      have hx₀K : (x₀ : ℂ) ∉ closure (fwdHull U σ) := negInv_notMem_closure hy0 hyA
      set v : ℝ := (fwdMap U σ (x₀ : ℂ)).re with hvdef
      have hFv := tendsto_fwdMap_re hU hU0 hσ hx₀0 hx₀K
      have hv : chartAR U σ < v ∨ v < chartAL U σ := by
        rcases lt_or_gt_of_ne hx₀0 with h | h
        · exact Or.inr (re_fwdMap_lt_of_neg hU hU0 hσ h hx₀K)
        · exact Or.inl (lt_re_fwdMap_of_pos hU hU0 hσ h hx₀K)
      have hAL := WangWu.chartAL_nonpos hU hσ
      have hAR := WangWu.chartAR_nonneg hU hσ
      have hv0 : (v : ℂ) ≠ 0 := by
        rcases hv with h | h
        · exact_mod_cast (by linarith : v ≠ 0)
        · exact_mod_cast (by linarith : v ≠ 0)
      have hlimΨ : Tendsto (relMap U σ) (𝓝[H \ invHull U σ] (y : ℂ)) (𝓝 (-(v : ℂ)⁻¹)) :=
        ((continuousAt_inv₀ hv0).neg.tendsto).comp
          (hFv.comp (tendsto_negInv_real hy0 (sdiff_subset : H \ invHull U σ ⊆ H)))
      have he := tendsto_nhds_unique (hlimΨ.comp hseq) hqφ
      have hbv : b = -v⁻¹ := by exact_mod_cast he.symm
      have hvb : v = -b⁻¹ := by rw [hbv, neg_inv_neg_inv_real]
      rcases hbc' with h | h
      · rw [h, neg_inv_neg_inv_real] at hvb
        rcases hv with h' | h' <;> linarith
      · rw [h, neg_inv_neg_inv_real] at hvb
        rcases hv with h' | h' <;> linarith

/-! ### GB6's disjointness in the counterflow's frame, and the configuration -/

/-- `R(A) = K_σ`: the inversion is an involution. -/
theorem image_invHull : (fun z : ℂ => -z⁻¹) '' invHull U σ = fwdHull U σ := by
  rw [invHull, image_image]
  simp only [GB6.neg_inv_neg_inv, image_id']

/-- **GB6's disjointness, read in the counterflow's frame**: if `cl K_σ` misses `cl R(K'_t)` (the form given before the
first contact, `GB6.disjoint_closure_fwdHull_of_lt_firstContactTime`), then `cl K'_t` misses `cl A`. -/
theorem disjoint_closure_invHull (hU : Continuous U) (hσ : 0 ≤ σ) {W : ℝ → ℝ} {t : ℝ}
    (hd : Disjoint (closure (fwdHull U σ)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull W t))) :
    Disjoint (closure (fwdHull W t)) (closure (invHull U σ)) := by
  -- `0 ∉ cl A`: `K_σ` is bounded and lies in `ℍ`
  obtain ⟨M, hM⟩ := (isBounded_fwdHull hU σ).subset_closedBall 0
  have hKH : fwdHull U σ ⊆ H := (isHPHull_fwdHull hU hσ).1
  have hA0 : (0 : ℂ) ∉ closure (invHull U σ) := by
    intro h0
    obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.1 h0 (1 / (|M| + 1)) (by positivity)
    obtain ⟨z, hz, rfl⟩ := hw
    have hz0 : z ≠ 0 := GB6.ne_zero_of_mem_H (hKH hz)
    have hzM : ‖z‖ ≤ |M| := (mem_closedBall_zero_iff.1 (hM hz)).trans (le_abs_self M)
    rw [dist_zero_left, norm_neg, norm_inv] at hwd
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [inv_lt_comm₀ hpos (by positivity), one_div, inv_inv] at hwd
    linarith
  refine Set.disjoint_left.2 fun z hzK hzA => ?_
  have hz0 : z ≠ 0 := fun h => hA0 (h ▸ hzA)
  have hc : ContinuousAt (fun w : ℂ => -w⁻¹) z := (continuousAt_inv₀ hz0).neg
  have h1 := mem_closure_image hc hzK
  have h2 := mem_closure_image hc hzA
  rw [image_invHull] at h2
  exact Set.disjoint_left.1 hd h2 h1

/-- **GB6's relative configuration** (`IsRelConfigOff` in the counterflow's frame, with GB6's chart): from the flow's
trace not returning to `0` before `σ > 0`, the counterflow's and the relative chains, the hull identity, the
disjointness before the first contact, the relative tip identity, and the word facts. The chart fields are
`isRetainedChartOff_relMap`, the exceptional points `relBad_notMem_closure`. -/
theorem isRelConfigOff_gb6 (hU : Continuous U) (hU0 : U 0 = 0) (hα : IsLoewnerTrace U α) (hσ : 0 < σ)
    (hNR : ∀ v ∈ Ioc 0 σ, α v ≠ 0) {W Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
    {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G v : ℂ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : relMap U σ '' fwdHull W t = fwdHull Wr u)
    (hd : Disjoint (closure (fwdHull U σ)) (closure ((fun w : ℂ => -w⁻¹) '' fwdHull W t)))
    (htip : Tendsto (fun y => fwdMap W t (relInv U σ (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0))
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hGE : IsBoundedHarmonicExtension βE SE GE)
    (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : BHMean.IsSideWord βE SE (fwdMapInv W t) (fwdHull W t) lam)
    (hsu : BHMean.IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam)
    (hflow : BHMean.IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hv : ∀ z, v z = G (fwdMap Wr u (relMap U σ z)) - χ * ((logDerivFwd Wr u (relMap U σ z)).im +
      (relLog U σ z).im)) :
    IsRelConfigOff (invHull U σ) (relMap U σ) (relInv U σ) (relLog U σ) (relBad U σ) W Wr η ηr t u χ lam
      β₀ βE βu S₀ SE Su G₀ GE G v := by
  have hd' := disjoint_closure_invHull hU hσ.le hd
  exact ⟨isRetainedChartOff_relMap hU hU0 hα hσ hNR, hW, hW0, hη, ht, hWr, hWr0, hηr, hu, hK, hd',
    relBad_notMem_closure hU hU0 hσ.le hW ht hK hd', htip, hG₀, hGE, hG, hsE, hsu, hflow, hv⟩

end InteractingSLE.Supp8.Q3Rel
