/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondHit
import InteractingSLE.Spec.Sec5.GlueCondUnionImg
import InteractingSLE.Spec.Sec5.CrossRestartChart
import InteractingSLE.Spec.Sec7.SideHeightLift

/-!
# G3 (ii), Proposition 4.9 direction: the counterflow mean read in the counterflow chart

Packet PROVE-GLUECOND6 (specification §4.2, proofs of Lemma 4.7 and Proposition 4.9, pp. 117–120; Remark 4.10).
Setting: a counterflow hull `K′ = fwdHull w s` (chart `R`, any continuous driver `w`), its reflection `G = R(K′)`
(`R z = −1/z`, the chart `Q`), and the counterflow chart `Ψ = revChart w s = R ∘ f_s ∘ R : ℍ ∖ G → ℍ`.

* **The derivative lift of `Ψ`** (`logDerivPsi`, `isDerivLog_revChart`): by the chain rule (`IsDerivLog.comp`,
  FD12.1's lift `−2 Log` of `R` and the canonical lift `logDerivFwd` of `f_s`),
  `L_Ψ(z) = −2 Log f_s(R z) + L_s(R z) − 2 Log z + 2πi`; its imaginary part is
  `arg_Ψ(z) = 2 arg Ψ(z) + Im L_s(R z) − 2 arg z` (`im_logDerivPsi`). The constant `2πi` normalizes the branch at the
  physical real line: `arg_Ψ → 0` at every real `x ≠ 0` whose image `R x` is off the closure of `K′`
  (`tendsto_im_logDerivPsi`), i.e. this is the branch the flow-line coupling of the image word must use (near the flow's
  base the image data must be the original data, with no `2πχ` shift).
* **The counterflow mean in the counterflow chart** (`cfMeanQ_add_eq_imgMean0`): for every history `y` and every
  `z ∈ ℍ ∖ R(K′_s)`,
  `cfMeanQ u′ s y z + 𝔥₀(z) + χ arg_Ψ(z) = imgMean0 (Ψ z)`,
  `imgMean0 ζ = −cfU(−1/ζ) − πχ/2 + χ(16/κ) · Im(−2 Log ζ)`,
  a bounded harmonic function of `ζ` alone (the unbounded `Im L_s` terms cancel exactly because `χ(16/κ) = −χ(κ)`, and
  `u′(R z) + 𝔥₀(z) − 2χ arg z` is the constant `−πχ/2`, from `eqOn_returnBHE_counterflow`). So the conditional mean of
  `h` given the counterflow prefix alone is `imgMean0 ∘ Ψ − χ arg Ψ′`: the coupling-mean form of the image word at
  image time `0`.
* **Its boundary data** (`isBoundedHarmonicExtension_imgMean0`): `imgMean0` is the bounded harmonic extension of the
  return data `returnData (−πχ/2) χ(16/κ) d_s`, `d_s` the counterflow word's data at time `s`. Explicitly
  (`imgData0_of_neg`, `imgData0_of_pos`): on the exposed sides between the junctions and `∞`,
  * `ζ < −1/(cfPosR₀)` (left of the left junction): `−λ′ + 3πχ/2 = −λ + 2πχ`;
  * `ζ > −1/(cfPosL₀)` (right of the right junction): `λ′ − πχ/2 = λ − πχ`;
  (`λ′ = π/√(16/κ)`, `λ − λ′ = πχ/2`). Hence the image word's junction weights are `ρ′_L = κ − 4 − Σρ_L` and
  `ρ′_R = κ/2 − 2 − Σρ_R` (`−λ(1 + Σρ_L + ρ′_L) = −λ + 2πχ`, `λ(1 + Σρ_R + ρ′_R) = λ − πχ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.GlueImg

open WangWu hiding ratPt exists_ratPt_dist_lt

/-! ### The derivative lift of the counterflow chart -/

section Lift

variable {w : ℝ → ℝ} {s : ℝ}

/-- **The derivative lift of the counterflow chart** `Ψ = R ∘ f_s ∘ R`: the chain-rule lift
`−2 Log f_s(R z) + L_s(R z) − 2 Log z`, shifted by `2πi` so that its imaginary part vanishes on the physical real
line. -/
def logDerivPsi (w : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  -2 * log (fwdMap w s (negInv z)) + (logDerivFwd w s (negInv z) + -2 * log z) + 2 * π * I

/-- The domain `ℍ ∖ R(K_s)` of the counterflow chart is open. -/
theorem isOpen_H_diff_negInv_fwdHull (hw : Continuous w) (hs : 0 ≤ s) : IsOpen (H \ negInv '' fwdHull w s) := by
  rw [H_diff_image_negInv]
  exact isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw hs) sdiff_subset

/-- **`L_Ψ` is a derivative lift of `Ψ` on `ℍ ∖ R(K_s)`** (FD12.1 and the chain rule). -/
theorem isDerivLog_revChart (hw : Continuous w) (hs : 0 ≤ s) :
    IsDerivLog (revChart w s) (logDerivPsi w s) (H \ negInv '' fwdHull w s) := by
  set D := H \ negInv '' fwdHull w s with hD
  set E := H \ fwdHull w s with hE
  have hDo : IsOpen D := isOpen_H_diff_negInv_fwdHull hw hs
  have hEo : IsOpen E := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw hs
  have hDH : D ⊆ H := sdiff_subset
  have hnD : DifferentiableOn ℂ negInv D := differentiableOn_negInv.mono hDH
  have hmaps : MapsTo negInv D E := fun z hz => negInv_notMem_fwdHull hz
  have hfE : DifferentiableOn ℂ (fwdMap w s) E := QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs
  have h1 : IsDerivLog (fwdMap w s ∘ negInv) (fun z => logDerivFwd w s (negInv z) + -2 * log z) D :=
    IsDerivLog.comp hDo hEo hfE hnD hmaps (isDerivLog_fwdMap hw hs) (isDerivLog_neg_inv.mono hDH)
  have hmaps2 : MapsTo (fwdMap w s ∘ negInv) D H := fun z hz =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hmaps hz)
  have h2 := IsDerivLog.comp (ψ := negInv) hDo QuantumZipper.isOpen_H differentiableOn_negInv
    (hfE.comp hnD hmaps) hmaps2 isDerivLog_neg_inv h1
  refine ⟨h2.1.add_const _, fun z hz => ?_⟩
  show exp (logDerivPsi w s z) = deriv (revChart w s) z
  have e : logDerivPsi w s z = (-2 * log ((fwdMap w s ∘ negInv) z) +
      (logDerivFwd w s (negInv z) + -2 * log z)) + 2 * π * I := rfl
  rw [e, exp_add, exp_two_pi_mul_I, mul_one, h2.2 z hz]
  rfl

/-- `arg(−1/ζ) = π − arg ζ` on `ℍ`. -/
theorem arg_negInv_of_mem_H {ζ : ℂ} (hζ : ζ ∈ H) : arg (negInv ζ) = π - arg ζ := by
  have h := congrArg Complex.im (neg_derivLog_neg_inv_eq hζ)
  simp only [neg_im, neg_re, mul_im, mul_re, log_im, re_ofNat, im_ofNat, sub_im, ofReal_re, ofReal_im, I_re, I_im]
    at h
  rw [negInv]
  linarith

/-- **The imaginary part of `L_Ψ`**: `arg_Ψ(z) = 2 arg Ψ(z) + Im L_s(R z) − 2 arg z`. -/
theorem im_logDerivPsi (hw : Continuous w) (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ H \ negInv '' fwdHull w s) :
    (logDerivPsi w s z).im = 2 * arg (revChart w s z) + (logDerivFwd w s (negInv z)).im - 2 * arg z := by
  have hf : fwdMap w s (negInv z) ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (negInv_notMem_fwdHull hz)
  have hΨ : revChart w s z ∈ H := revChart_mem_H hw hs hz
  have e : fwdMap w s (negInv z) = negInv (revChart w s z) := by rw [revChart, negInv_negInv]
  have ha := arg_negInv_of_mem_H hΨ
  simp only [logDerivPsi, add_im, mul_im, mul_re, neg_re, neg_im, log_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im,
    I_re, I_im]
  rw [e, ha]
  ring

end Lift

/-! ### The counterflow mean in the counterflow chart -/

section Identity

open GlueCond Sec7.StripSysField

variable {κ : ℝ} {w : ℝ → ℝ} {s : ℝ}

/-- **The return of a chart-`R` mean**: `ζ ↦ −v(−1/ζ) + (−πχ) + χ(16/κ) Im(−2 Log ζ)`, the chart-`Q` reading (FD12.1,
`retShift (cfOffset κ) (cfCoeff κ)`) of a function `v` of the counterflow chart. With `v = u′` (time `0`) this is the
harmonic extension `u_b` of the counterflow field's data (`eqOn_returnBHE_counterflow`); with `v` the counterflow word's
harmonic extension at time `s` it is the image-chart mean (`cfMeanQ_add_eq_retMean`). -/
def retMean (κ : ℝ) (v : ℂ → ℝ) (ζ : ℂ) : ℝ := -v (negInv ζ) + retShift (cfOffset κ) (cfCoeff κ) ζ

/-- The chart-`R` coupling mean read in the counterflow chart: the unbounded `Im L_s` terms of the coupling mean at
`16/κ` and of `χ arg Ψ′` cancel (`χ(16/κ) = −χ(κ)`). -/
theorem neg_couplingMean_add_chiC_mul (hκ : 0 < κ) (hw : Continuous w) (hs : 0 ≤ s) (v : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ H \ negInv '' fwdHull w s) :
    -couplingMean (16 / κ) w s v (negInv z) + chiC κ * (logDerivPsi w s z).im =
      -v (negInv (revChart w s z)) + 2 * chiC κ * arg (revChart w s z) - 2 * chiC κ * arg z := by
  have e : fwdMap w s (negInv z) = negInv (revChart w s z) := by rw [revChart, WangWu.negInv_negInv]
  rw [couplingMean, Sec4.chiC_sixteen_div hκ, im_logDerivPsi hw hs hz, e]
  ring

/-- **The two centrings, in the form used here**: `u′(R z) + u_b(z) = 2χ arg z − πχ` on `ℍ`, for the counterflow
word's harmonic extension `u′` (chart `R`, parameter `16/κ`) and the harmonic extension `u_b` of the counterflow
field's data `b` (chart `Q`). -/
theorem negInv_add_eq_of_returnBHE (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {u_b : ℂ → ℝ}
    (hu_b : IsBoundedHarmonicExtension b jumps u_b) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (cfWordData κ b jumps) (cfWordJumps κ b jumps) u') {z : ℂ} (hz : z ∈ H) :
    u' (negInv z) + u_b z = 2 * chiC κ * arg z - π * chiC κ := by
  have h := eqOn_returnBHE_counterflow hκ hb hu_b hu' hz
  simp only [retShift, cfOffset, cfCoeff, infinitySourceChart_lift, Sec4.chiC_sixteen_div hκ] at h
  rw [← h]
  ring

/-- **The counterflow mean in the counterflow chart** (the conditional mean of the counterflow field given the
counterflow prefix alone, read through `Ψ`): for every history `y`, every `s ≥ 0` and `z ∈ ℍ ∖ R(K′_s)`,
`cfMeanQ u′ s y z + u_b(z) + χ arg_Ψ(z) = retMean κ (cfU s) (Ψ z)`, with `Ψ` the chart of the driver read from `y`
stopped at `s`. -/
theorem cfMeanQ_add_eq_retMean (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {u_b : ℂ → ℝ}
    (hu_b : IsBoundedHarmonicExtension b jumps u_b) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension (cfWordData κ b jumps) (cfWordJumps κ b jumps) u') (t : ℝ≥0)
    (y : LawUnique.HistorySpace 0 0) {z : ℂ} (hz : z ∈ H \ cfHullQ t y) :
    cfMeanQ κ b jumps u' t y z + u_b z +
        chiC κ * (logDerivPsi (Ito.rpath (Sec4.regPath (cfStop t y))) t z).im =
      retMean κ (cfU κ b jumps t (cfStop t y)) (revChart (Ito.rpath (Sec4.regPath (cfStop t y))) t z) := by
  set w := Ito.rpath (Sec4.regPath (cfStop t y)) with hwdef
  have hw : Continuous w := Sec4.continuous_rpath_regPath (cfStop t y)
  have hz' : z ∈ H \ negInv '' fwdHull w t :=
    ⟨hz.1, fun h => hz.2 (image_mono (fwdHull_subset_hullAt t y) h)⟩
  have h1 := neg_couplingMean_add_chiC_mul hκ hw t.coe_nonneg (cfU κ b jumps t (cfStop t y)) hz'
  have h2 := negInv_add_eq_of_returnBHE hκ hb hu_b hu' hz.1
  simp only [cfMeanQ, retMean, retShift, cfOffset, cfCoeff, infinitySourceChart_lift, Sec4.chiC_sixteen_div hκ]
  rw [← hwdef]
  linear_combination h1 + h2

/-- **`retMean` of a bounded harmonic extension is the bounded harmonic extension of the return data**
(`isBoundedHarmonicExtension_return`). -/
theorem isBoundedHarmonicExtension_retMean {g : ℝ → ℝ} {S : Finset ℝ} {v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension g S v) :
    IsBoundedHarmonicExtension (returnData (cfOffset κ) (cfCoeff κ) g) (returnExcept S) (retMean κ v) := by
  have h := isBoundedHarmonicExtension_return (cfOffset κ) (cfCoeff κ) hv
  have e : (fun z => -v (-z⁻¹) + cfOffset κ + cfCoeff κ * infinitySourceChart.2.2 z) = retMean κ v := by
    funext z
    simp only [retMean, retShift, negInv]
    ring
  rwa [e] at h

end Identity

/-! ### The branch of `arg Ψ′` vanishes on the physical real line -/

section Branch

open ConformalImage ConformalImageFull

variable {w : ℝ → ℝ} {s : ℝ}

/-- A real point right of the seed stays right of the driver: `W_T < g_T(y)` for `y > 0` away from `K_T` (the right
version of `CrossRestart.bdryVal_re_lt`). -/
theorem lt_bdryVal_re (hw : Continuous w) (hw0 : w 0 = 0) {y r T : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (hd : Disjoint (ball (y : ℂ) r) (fwdHull w T)) (hy : 0 < y) : w T < (bdryVal w y T).re := by
  set ψ : ℝ → ℝ := fun t => (bdryVal w y t).re - w t with hψ
  have hψc : ContinuousOn ψ (Icc 0 T) :=
    ((Complex.continuous_re.comp_continuousOn (continuousOn_bdryVal hw hw0 hT hr hd)).sub hw.continuousOn)
  have hψ0 : 0 < ψ 0 := by simp [hψ, bdryVal_zero hw hw0, hw0, hy]
  have hne : ∀ t ∈ Icc (0 : ℝ) T, ψ t ≠ 0 := fun t ht h0 => by
    have hb := bdryVal_ne hw hw0 hr hd hy.ne' ht
    have him := (bdryVal_spec hw hw0 ht.1 hr (disjoint_ball_of_le hd ht.2)).1
    apply hb
    apply Complex.ext
    · simp only [ofReal_re]; linarith [show (bdryVal w y t).re - w t = 0 from h0]
    · simp [him]
  by_contra hcon
  push Not at hcon
  have hψT : ψ T ≤ 0 := by simp only [hψ]; linarith
  obtain ⟨t, ht, ht0⟩ := isPreconnected_Icc.intermediate_value₂ (right_mem_Icc.2 hT)
    (left_mem_Icc.2 hT) hψc continuousOn_const hψT (show (0 : ℝ) ≤ ψ 0 from hψ0.le)
  exact hne t ht ht0

/-- `R` maps `𝓝[ℍ] x` to `𝓝[ℍ] (−1/x)` at a real `x ≠ 0`. -/
theorem tendsto_negInv_nhdsWithin_H {x : ℝ} (hx : x ≠ 0) :
    Tendsto negInv (𝓝[H] (x : ℂ)) (𝓝[H] ((-x⁻¹ : ℝ) : ℂ)) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  have e : negInv (x : ℂ) = ((-x⁻¹ : ℝ) : ℂ) := by simp [negInv]
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun z hz => negInv_mem_H hz⟩
  rw [← e]
  exact (continuousAt_negInv hx').tendsto.mono_left nhdsWithin_le_nhds

/-- Near a physical real point `x ≠ 0` whose image `R x` is off `K_s`, the points of `ℍ` lie off `R(K_s)`. -/
theorem eventually_mem_H_diff_negInv {x : ℝ} (hx : x ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball ((-x⁻¹ : ℝ) : ℂ) ρ) (fwdHull w s)) :
    ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ negInv '' fwdHull w s := by
  have h1 : ∀ᶠ z in 𝓝[H] (x : ℂ), negInv z ∈ ball ((-x⁻¹ : ℝ) : ℂ) ρ :=
    (tendsto_negInv_nhdsWithin_H hx).mono_right nhdsWithin_le_nhds |>.eventually (ball_mem_nhds _ hρ)
  filter_upwards [h1, self_mem_nhdsWithin] with z hz hzH
  refine ⟨hzH, ?_⟩
  rintro ⟨k, hk, rfl⟩
  rw [WangWu.negInv_negInv] at hz
  exact Set.disjoint_left.1 hd hz hk

/-- The centred map read through `R` has the boundary value `g_s(−1/x) − W_s` at a physical real point `x ≠ 0`. -/
theorem tendsto_fwdMap_negInv (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {x : ℝ} (hx : x ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (hd : Disjoint (ball ((-x⁻¹ : ℝ) : ℂ) ρ) (fwdHull w s)) :
    Tendsto (fun z => fwdMap w s (negInv z)) (𝓝[H] (x : ℂ)) (𝓝 (bdryVal w (-x⁻¹) s - w s)) := by
  have h := (bdryVal_spec hw hw0 hs hρ hd).2
  have h' : Tendsto (fun z => fwdMap w s z) (𝓝[H] ((-x⁻¹ : ℝ) : ℂ)) (𝓝 (bdryVal w (-x⁻¹) s - w s)) :=
    (h.sub_const (w s : ℂ)).congr fun z => by simp only [gmap, add_sub_cancel_right]
  exact h'.comp (tendsto_negInv_nhdsWithin_H hx)

/-- **The branch `arg_Ψ` vanishes on the physical real line**: at every real `x ≠ 0` whose image `R x` has a ball off
`K_s`, `Im L_Ψ(z) → 0` as `z → x` in `ℍ`. -/
theorem tendsto_im_logDerivPsi (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {x : ℝ} (hx : x ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (hd : Disjoint (ball ((-x⁻¹ : ℝ) : ℂ) ρ) (fwdHull w s)) :
    Tendsto (fun z => (logDerivPsi w s z).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hev := eventually_mem_H_diff_negInv (w := w) (s := s) hx hρ hd
  -- the canonical lift of `f_s` tends to a real value at `R x`
  have hL : Tendsto (fun z => (logDerivFwd w s (negInv z)).im) (𝓝[H] (x : ℂ)) (𝓝 0) :=
    (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hw hs)
      (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hw hw0 hs) (isMapOut_fwdMap hw hw0 hs) hρ hd).comp
      (tendsto_negInv_nhdsWithin_H hx)
  -- the boundary value of `f_s` at `R x`
  set L : ℂ := bdryVal w (-x⁻¹) s - w s with hLdef
  have hLim : L.im = 0 := by
    simp only [hLdef, sub_im, ofReal_im, sub_zero, (bdryVal_spec hw hw0 hs hρ hd).1]
  have hf := tendsto_fwdMap_negInv hw hw0 hs hx hρ hd
  have hΨH : ∀ᶠ z in 𝓝[H] (x : ℂ), revChart w s z ∈ H := hev.mono fun z hz => revChart_mem_H hw hs hz
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- `x < 0`: `R x > 0`, `f_s(R x) > 0`, `Ψ(x) < 0`, both arguments tend to `π`
    have hy : 0 < -x⁻¹ := neg_pos.2 (inv_lt_zero.2 hneg)
    have hLre : 0 < L.re := by
      simp only [hLdef, sub_re, ofReal_re]
      linarith [lt_bdryVal_re hw hw0 hs hρ hd hy]
    have hL0 : L ≠ 0 := fun h => by rw [h, zero_re] at hLre; exact lt_irrefl _ hLre
    have hΨ : Tendsto (revChart w s) (𝓝[H] (x : ℂ)) (𝓝 (negInv L)) :=
      ((continuousAt_negInv hL0).tendsto.comp hf).congr fun z => rfl
    have hnre : (negInv L).re < 0 := by
      have e : L = ((L.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hLim])
      rw [e]; simp only [negInv, ← ofReal_inv, ← ofReal_neg, ofReal_re]
      exact neg_neg_of_pos (inv_pos.2 hLre)
    have hnim : (negInv L).im = 0 := by
      have e : L = ((L.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hLim])
      rw [e]; simp only [negInv, ← ofReal_inv, ← ofReal_neg, ofReal_im]
    have hΨ' : Tendsto (revChart w s) (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (negInv L)) :=
      tendsto_nhdsWithin_iff.2 ⟨hΨ, hΨH.mono fun z (hz : 0 < (revChart w s z).im) =>
        show 0 ≤ (revChart w s z).im from hz.le⟩
    have hA1 := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hnre hnim).comp hΨ'
    have hxre : (x : ℂ).re < 0 := by simpa using hneg
    have hA2 := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hxre (by simp)).mono_left
      (nhdsWithin_mono _ fun z (hz : 0 < z.im) => le_of_lt hz)
    have h := ((hA1.const_mul 2).add hL).sub (hA2.const_mul 2)
    rw [show (2 : ℝ) * π + 0 - 2 * π = 0 by ring] at h
    refine h.congr' ?_
    filter_upwards [hev] with z hz
    rw [im_logDerivPsi hw hs hz]
    rfl
  · -- `x > 0`: `R x < 0`, `f_s(R x) < 0`, `Ψ(x) > 0`, both arguments tend to `0`
    have hy : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hpos)
    have hLre : L.re < 0 := by
      simp only [hLdef, sub_re, ofReal_re]
      linarith [CrossRestart.bdryVal_re_lt hw hw0 hs hρ hd hy]
    have hL0 : L ≠ 0 := fun h => by rw [h, zero_re] at hLre; exact lt_irrefl _ hLre
    have hΨ : Tendsto (revChart w s) (𝓝[H] (x : ℂ)) (𝓝 (negInv L)) :=
      ((continuousAt_negInv hL0).tendsto.comp hf).congr fun z => rfl
    have hnre : 0 < (negInv L).re := by
      have e : L = ((L.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hLim])
      rw [e]; simp only [negInv, ← ofReal_inv, ← ofReal_neg, ofReal_re]
      exact neg_pos.2 (inv_lt_zero.2 hLre)
    have hA1 : Tendsto (fun z => arg (revChart w s z)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
      have h0 : arg (negInv L) = 0 := by
        have e : L = ((L.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hLim])
        rw [e]; simp only [negInv, ← ofReal_inv, ← ofReal_neg]
        exact arg_ofReal_of_nonneg (neg_nonneg.2 (inv_nonpos.2 hLre.le))
      rw [← h0]
      exact (continuousAt_arg (Or.inl hnre)).tendsto.comp hΨ
    have hA2 : Tendsto arg (𝓝[H] (x : ℂ)) (𝓝 0) := by
      have h0 : arg (x : ℂ) = 0 := arg_ofReal_of_nonneg hpos.le
      rw [← h0]
      exact (continuousAt_arg (Or.inl (by simpa using hpos))).tendsto.mono_left nhdsWithin_le_nhds
    have h := ((hA1.const_mul 2).add hL).sub (hA2.const_mul 2)
    rw [show (2 : ℝ) * 0 + 0 - 2 * 0 = 0 by ring] at h
    refine h.congr' ?_
    filter_upwards [hev] with z hz
    rw [im_logDerivPsi hw hs hz]

end Branch

/-! ### The heights of the exposed counterflow sides in the counterflow chart -/

section Heights

open Sec7.StripSysField

variable {κ : ℝ} {nL nR : ℕ}

/-- `√(16/κ) = 4/√κ`. -/
theorem sqrt_sixteen_div (hκ : 0 < κ) : Real.sqrt (16 / κ) = 4 / Real.sqrt κ := by
  rw [Real.sqrt_div' 16 hκ.le, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `λ′ = λ − πχ/2` (`λ = π/√κ`, `λ′ = π/√(16/κ)`). -/
theorem pi_div_sqrt_sixteen_div (hκ : 0 < κ) : π / Real.sqrt (16 / κ) = π / Real.sqrt κ - π / 2 * chiC κ := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  rw [sqrt_sixteen_div hκ, QuantumZipper.chiC]
  field_simp
  nlinarith [hsq]

/-- **The left exposed side** (`x < 0` with `R x = −1/x` between the counterflow tip and every right mark of the
counterflow word at time `s`): the return data equal `−λ′ + πχ`. For the field `h` (adding the centring constant
`πχ/2`) this is `−λ′ + 3πχ/2 = −λ + 2πχ` (`junction_height_left`). -/
theorem returnData_forceBoundaryData_left (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) {x : ℝ} (hx : x < 0) (hR : ∀ i, -x⁻¹ < vR i) :
    returnData (cfOffset κ) (cfCoeff κ) (forceBoundaryData (16 / κ) ρL ρR vL vR) x =
      -(π / Real.sqrt (16 / κ)) + π * chiC κ := by
  have hpos : ¬ (-x⁻¹ < 0) := not_lt.2 (neg_nonneg.2 (inv_nonpos.2 hx.le))
  have hempty : Finset.univ.filter (fun i => vR i ≤ -x⁻¹) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i _ => not_le.2 (hR i)
  simp only [returnData, forceBoundaryData, hpos, ↓reduceIte, hempty, Finset.sum_empty, add_zero, mul_one,
    liftBoundary, hx, cfOffset, cfCoeff, Sec4.chiC_sixteen_div hκ]
  ring

/-- **The right exposed side** (`x > 0` with `R x = −1/x` between every left mark and the tip): the return data equal
`λ′ − πχ`; for `h`, `λ′ − πχ/2 = λ − πχ` (`junction_height_right`). -/
theorem returnData_forceBoundaryData_right (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) {x : ℝ} (hx : 0 < x) (hL : ∀ i, vL i < -x⁻¹) :
    returnData (cfOffset κ) (cfCoeff κ) (forceBoundaryData (16 / κ) ρL ρR vL vR) x =
      π / Real.sqrt (16 / κ) - π * chiC κ := by
  have hneg : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hx)
  have hempty : Finset.univ.filter (fun i => -x⁻¹ < vL i) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i _ => not_lt.2 (hL i).le
  have hx' : ¬ (x < 0) := not_lt.2 hx.le
  simp only [returnData, forceBoundaryData, hneg, ↓reduceIte, hempty, Finset.sum_empty, add_zero, mul_one,
    liftBoundary, hx', cfOffset, cfCoeff, Sec4.chiC_sixteen_div hκ]
  ring

/-- **The left junction weight**: with `ρ′_L = κ − 4 − Σρ_L`, the flow-line height `−λ(1 + Σρ_L + ρ′_L)` beyond the
left junction is the left exposed height of `h`, `−λ′ + πχ + πχ/2`. -/
theorem junction_height_left (hκ : 0 < κ) (S : ℝ) :
    -(π / Real.sqrt κ) * (1 + S + (κ - 4 - S)) = -(π / Real.sqrt (16 / κ)) + π * chiC κ + π / 2 * chiC κ := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  rw [pi_div_sqrt_sixteen_div hκ, QuantumZipper.chiC]
  field_simp
  linear_combination 4 * hsq

/-- **The right junction weight**: with `ρ′_R = κ/2 − 2 − Σρ_R`, the flow-line height `λ(1 + Σρ_R + ρ′_R)` beyond the
right junction is the right exposed height of `h`, `λ′ − πχ + πχ/2`. -/
theorem junction_height_right (hκ : 0 < κ) (S : ℝ) :
    π / Real.sqrt κ * (1 + S + (κ / 2 - 2 - S)) = π / Real.sqrt (16 / κ) - π * chiC κ + π / 2 * chiC κ := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  rw [pi_div_sqrt_sixteen_div hκ, QuantumZipper.chiC]
  field_simp
  linear_combination (-2) * hsq

end Heights

end InteractingSLE.Sec5.GlueImg
