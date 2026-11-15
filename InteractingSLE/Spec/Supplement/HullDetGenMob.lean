/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGenBR4a
import InteractingSLE.Spec.Supplement.HullDetGenLaw
import InteractingSLE.Spec.Jordan.Transport

/-!
# BR4a's target-change chart

Packet PROVE-HULLDET. In Corollary BR4a the original counterflow lives in the frame `w = −1/z` (the field
`h' = T_∞ h`) and the recentred one in `w̃ = −1/(z − v)` (the field `X = T_∞ (T_v h)`); `w̃ = mob v w = w/(v w + 1)`.
The **target-change chart** `brChart v = (mob v, mob (−v), lift)` with the lift
`lift z = L(−1/mob v z) − L(−1/z)` (`L = Im (−2 log)`, the frozen infinity-source lift) carries `h'` to `X`:

* **`isConformal_brChart`**, `coe_dom_brChart` (its domain is `ℍ`), `continuousOn_brChart_lift`;
* **`eq_chartTransport_brChart`**: `X = chartTransport (brChart v) 1 0 k h'` whenever `h'` and `X` are the
  infinity-source transports (coefficients `−1, a, k`) of `h` and of its recentring at `v`.

So the relative coupling of BR4a is a relative exploration of the original coupling through a fixed chart, to which
`HullDetGen.hasSafeLaw_of_timeChange` and `hasSafeMembers_of_timeChange` apply.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.HullDetGen

open Theorem14.BR4aPath

/-- **BR4a's target-change chart** `(mob v, mob (−v), lift)`, with the lift `L(−1/mob v z) − L(−1/z)`
(`L` the infinity-source lift): the lift of `T_∞ ∘ T_v ∘ T_∞⁻¹`. -/
def brChart (v : ℝ) : Chart :=
  (mob v, mobInv v, fun z => infinitySourceChart.2.2 (-(mob v z)⁻¹) - infinitySourceChart.2.2 (-z⁻¹))

theorem mobInv_eq (v : ℝ) (w : ℂ) : mobInv v w = w / (-v * w + 1) := by
  have h := mob_apply (-v) w
  simp only [mob, mobInv] at h ⊢
  rw [h]
  push_cast
  ring

theorem mob_mem_H (v : ℝ) {z : ℂ} (hz : z ∈ H) : mob v z ∈ H :=
  (QuantumZipper.CA.bijOn_realMobius_H (by norm_num : (0 : ℝ) < 1 * 1 - 0 * v)).mapsTo hz

theorem mobInv_mob (v : ℝ) {z : ℂ} (hz : z ∈ H) : mobInv v (mob v z) = z := by
  have h := mob_mobInv (-v) hz
  have e1 : mob (-v) = mobInv v := by
    funext w
    simp only [mob, mobInv]
  have e2 : mobInv (-v) = mob v := by
    funext w
    simp only [mob, mobInv, neg_neg]
  rw [e1, e2] at h
  exact h

/-- The target-change chart is conformal. -/
theorem isConformal_brChart (v : ℝ) : (brChart v).IsConformal := by
  refine ⟨fun w hw => ?_, fun w hw => mobInv_mem_H v hw, fun w hw => mob_mobInv v hw⟩
  have hne : -(v : ℂ) * w + 1 ≠ 0 := by
    intro h0
    have him : (-(v : ℂ) * w + 1).im = 0 := by rw [h0]; simp
    have hwim : (0 : ℝ) < w.im := hw
    simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, add_zero, Complex.one_im] at him
    by_cases hv : v = 0
    · subst hv
      simp at h0
    · have : -v * w.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact hv (by linarith)
      · linarith
  have hd : DifferentiableAt ℂ (fun w : ℂ => w / (-(v : ℂ) * w + 1)) w :=
    differentiableAt_id.div ((differentiableAt_id.const_mul _).add_const _) hne
  have he : (brChart v).2.1 = fun w : ℂ => w / (-(v : ℂ) * w + 1) := by
    funext w
    exact mobInv_eq v w
  rw [he]
  exact hd.differentiableWithinAt

/-- The domain of the target-change chart is `ℍ`. -/
theorem coe_dom_brChart (v : ℝ) : ((brChart v).dom : Set ℂ) = H := by
  rw [(isConformal_brChart v).coe_dom]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mobInv_mem_H v hz
  · intro hw
    exact ⟨mob v w, mob_mem_H v hw, mobInv_mob v hw⟩

/-! ### Transported test functions of charts with the same maps on `ℍ` -/

/-- Two conformal charts whose inverse maps agree on `ℍ` and whose forward maps agree on the domain transport test
functions identically. -/
theorem pushTest_congr {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal) (hinv : EqOn c.2.1 c'.2.1 H)
    (hfwd : EqOn c.1 c'.1 (c.dom : Set ℂ)) (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest hc φ = Chart.pushTest hc' φ := by
  have hdom : (c.dom : Set ℂ) = c'.dom := by
    rw [hc.coe_dom, hc'.coe_dom]
    exact hinv.image_eq
  ext z
  by_cases hz : z ∈ c.dom
  · have hz' : z ∈ c'.dom := by rw [← SetLike.mem_coe, ← hdom]; exact hz
    rw [Chart.pushTest_apply_of_mem hc φ hz, Chart.pushTest_apply_of_mem hc' φ hz', hfwd hz]
    have hev : c.1 =ᶠ[𝓝 z] c'.1 := by
      filter_upwards [c.dom.isOpen.mem_nhds hz] with y hy using hfwd hy
    rw [hev.deriv_eq]
  · have hz' : z ∉ c'.dom := fun h => hz (by rw [← SetLike.mem_coe, hdom]; exact h)
    rw [Chart.pushTest_apply_of_notMem hc φ hz, Chart.pushTest_apply_of_notMem hc' φ hz']

theorem ne_zero_of_mem_H' {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  rw [h] at hz
  exact lt_irrefl _ (show (0 : ℝ) < 0 from hz)

/-- **The target-change chart is the conjugate of the recentring by the infinity-source chart**, on test functions:
`T_∞ ∘ brChart = T_v ∘ T_∞` (the transported test functions of `∞.trans (brChart v)` and of
`(id.recenter v).trans ∞` agree). -/
theorem pushTest_conj (v : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest Chart.isConformal_infinitySourceChart (Chart.pushTest (isConformal_brChart v) φ) =
      Chart.pushTest (Chart.isConformal_id.recenter v)
        (Chart.pushTest Chart.isConformal_infinitySourceChart φ) := by
  rw [← Chart.pushTest_trans, ← Chart.pushTest_trans]
  refine pushTest_congr _ _ (fun w hw => ?_) (fun z hz => ?_) φ
  · have hw0 := ne_zero_of_mem_H' hw
    have hden : -(v : ℂ) * w + 1 ≠ 0 := by
      intro h0
      have := mobInv_eq v w
      have hmem := mobInv_mem_H v hw
      rw [this, h0, div_zero] at hmem
      exact ne_zero_of_mem_H' hmem rfl
    change -(mobInv v w)⁻¹ = (-w⁻¹ + v)
    rw [mobInv_eq, inv_div]
    field_simp
    ring
  · have hzH : z ∈ H := by
      have := ((Chart.isConformal_infinitySourceChart.trans (isConformal_brChart v)).dom_subset) hz
      exact this
    have hz0 := ne_zero_of_mem_H' hzH
    have hzv : z - v ≠ 0 := by
      intro h0
      have him : (z - v).im = 0 := by rw [h0]; simp
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
      have hpos : (0 : ℝ) < z.im := hzH
      linarith
    change mob v (-z⁻¹) = -(z - v)⁻¹
    rw [mob_apply]
    have hc : (v : ℂ) * -z⁻¹ + 1 = (z - v) * z⁻¹ := by
      field_simp
      ring
    rw [hc, div_mul_eq_div_div, neg_div, neg_div]
    congr 1
    rw [div_right_comm, div_self (inv_ne_zero hz0), one_div]

/-- The lift of the target-change chart, read in `ℍ`, is continuous. -/
theorem continuousOn_brChart_lift_inv (v : ℝ) :
    ContinuousOn (fun w => (brChart v).2.2 ((brChart v).2.1 w)) H := by
  have hL := Sec7.StripSysField.continuousOn_infinitySourceChart_lift'
  have hneg : MapsTo (fun w : ℂ => -w⁻¹) H H := Chart.isConformal_infinitySourceChart.2.1
  have hnegc : ContinuousOn (fun w : ℂ => -w⁻¹) H := Chart.isConformal_infinitySourceChart.1.continuousOn
  have h1 : ContinuousOn (fun w => infinitySourceChart.2.2 (-w⁻¹)) H := hL.comp hnegc hneg
  have h2 : ContinuousOn (fun w => infinitySourceChart.2.2 (-(mobInv v w)⁻¹)) H :=
    h1.comp (isConformal_brChart v).1.continuousOn (fun w hw => mobInv_mem_H v hw)
  refine (h1.sub h2).congr fun w hw => ?_
  change infinitySourceChart.2.2 (-(mob v (mobInv v w))⁻¹) - infinitySourceChart.2.2 (-(mobInv v w)⁻¹) = _
  rw [mob_mobInv v hw]
  rfl

/-- The lift of the target-change chart is continuous on its domain. -/
theorem continuousOn_brChart_lift (v : ℝ) : ContinuousOn (brChart v).2.2 (brChart v).dom := by
  rw [coe_dom_brChart]
  have hL := Sec7.StripSysField.continuousOn_infinitySourceChart_lift'
  have hneg : MapsTo (fun w : ℂ => -w⁻¹) H H := Chart.isConformal_infinitySourceChart.2.1
  have hnegc : ContinuousOn (fun w : ℂ => -w⁻¹) H := Chart.isConformal_infinitySourceChart.1.continuousOn
  have h1 : ContinuousOn (fun w => infinitySourceChart.2.2 (-w⁻¹)) H := hL.comp hnegc hneg
  have hmobc : ContinuousOn (mob v) H := by
    have := (isConformal_brChart v).differentiableOn_fwd
    rw [coe_dom_brChart] at this
    exact this.continuousOn
  exact (h1.comp hmobc fun z hz => mob_mem_H v hz).sub h1

/-- **The recentred infinity-source field is the target-change transport of the infinity-source field.** If
`h' = T_∞ h` and `X = T_∞ (T_v h)` (infinity-source transports with the same coefficients `−1, a, k`; any coefficient
of the lift-free recentring), then `X = chartTransport (brChart v) 1 0 k h'`. -/
theorem eq_chartTransport_brChart (v a k k₀ : ℝ) {h h' hv X : DistOn upperHalfPlaneOpens}
    (h1 : IsChartTransport infinitySourceChart (-1) a k h h')
    (h2 : IsChartTransport (Chart.id.recenter v) 1 0 k₀ h hv)
    (h3 : IsChartTransport infinitySourceChart (-1) a k hv X) :
    X = Chart.chartTransport (isConformal_brChart v) 1 0 k h' := by
  have hI := Chart.isConformal_infinitySourceChart
  have hR := Chart.isConformal_id.recenter v
  have hB := isConformal_brChart v
  ext φ
  rw [Chart.chartTransport_apply', h3.apply_eq hI φ, h2.apply_eq hR, h1.apply_eq hI, pushTest_conj,
    Chart.integral_pushTest hB, Chart.integral_mul_pushTest hB φ fun w => infinitySourceChart.2.2
      (infinitySourceChart.2.1 w), Chart.oneDist_apply,
    Chart.liftDist_apply (Chart.locallyIntegrableOn_of_continuousOn (continuousOn_brChart_lift_inv v))]
  have hL := Sec7.StripSysField.continuousOn_infinitySourceChart_lift'
  have hneg : MapsTo (fun w : ℂ => -w⁻¹) H H := hI.2.1
  have hnegc : ContinuousOn (fun w : ℂ => -w⁻¹) H := hI.1.continuousOn
  have hc1 : ContinuousOn (fun w => infinitySourceChart.2.2 (-w⁻¹)) H := hL.comp hnegc hneg
  have hc2 : ContinuousOn (fun w => infinitySourceChart.2.2 (-(mobInv v w)⁻¹)) H :=
    hc1.comp hB.1.continuousOn (fun w hw => mobInv_mem_H v hw)
  have hlift : (fun w => (brChart v).2.2 ((brChart v).2.1 w) * φ w) =
      fun w => infinitySourceChart.2.2 (-w⁻¹) * φ w - infinitySourceChart.2.2 (-(mobInv v w)⁻¹) * φ w := by
    funext w
    by_cases hw : w ∈ H
    · change (infinitySourceChart.2.2 (-(mob v (mobInv v w))⁻¹) - infinitySourceChart.2.2 (-(mobInv v w)⁻¹)) *
        φ w = _
      rw [mob_mobInv v hw]
      ring
    · rw [testOn_eq_zero_of_notMem_H φ hw]
      ring
  have hrec : ∀ w, (Chart.id.recenter v).2.2 ((Chart.id.recenter v).2.1 w) = 0 := fun _ => rfl
  simp only [hrec, zero_mul, MeasureTheory.integral_zero, mul_zero, add_zero]
  rw [hlift, integral_sub (integrable_mul_testOn_of_continuousOn hc1 φ)
    (integrable_mul_testOn_of_continuousOn hc2 φ)]
  change -1 * (1 * h (Chart.pushTest hR (Chart.pushTest hI φ))) + a * _ +
      k * ∫ w, infinitySourceChart.2.2 (-w⁻¹) * φ w =
    1 * (-1 * h (Chart.pushTest hR (Chart.pushTest hI φ)) + a * _ +
      k * ∫ w, infinitySourceChart.2.2 (-(mobInv v w)⁻¹) * φ w) +
      k * ((∫ w, infinitySourceChart.2.2 (-w⁻¹) * φ w) - ∫ w, infinitySourceChart.2.2 (-(mobInv v w)⁻¹) * φ w)
  ring

/-- `−1/w` is analytic at every point of `ℍ`, with value in `ℍ`. -/
theorem analyticAt_negInv {w : ℂ} (hw : w ∈ H) : AnalyticAt ℂ (fun z : ℂ => -z⁻¹) w :=
  (analyticAt_id.inv (ne_zero_of_mem_H' hw)).neg

/-- The Möbius map `mob v` is analytic at every point of `ℍ`. -/
theorem analyticAt_mob (v : ℝ) {z : ℂ} (hz : z ∈ H) : AnalyticAt ℂ (mob v) z := by
  have hden : (v : ℂ) * z + 1 ≠ 0 := by
    intro h0
    have h := mob_apply v z
    rw [h0, div_zero] at h
    exact ne_zero_of_mem_H' (mob_mem_H v hz) h
  have he : mob v = fun z : ℂ => z * ((v : ℂ) * z + 1)⁻¹ := by
    funext z
    rw [mob_apply, div_eq_mul_inv]
  rw [he]
  exact analyticAt_id.mul (((analyticAt_const.mul analyticAt_id).add analyticAt_const).inv hden)

/-- `w ↦ Im (−2 log (−1/w))` is harmonic at every point of `ℍ` composed with an analytic map into `ℍ`. -/
theorem harmonicOnNhd_brChart_lift (v : ℝ) : InnerProductSpace.HarmonicOnNhd (brChart v).2.2 (brChart v).dom := by
  intro z hz
  have hzH : z ∈ H := by rw [coe_dom_brChart] at hz; exact hz
  have hslit : ∀ {w : ℂ}, w ∈ H → w ∈ Complex.slitPlane := fun hw => Or.inr (ne_of_gt hw)
  have hm := analyticAt_mob v hzH
  have hA1 : AnalyticAt ℂ (fun z : ℂ => -(mob v z)⁻¹) z :=
    (hm.inv (ne_zero_of_mem_H' (mob_mem_H v hzH))).neg
  have hA2 : AnalyticAt ℂ (fun z : ℂ => -z⁻¹) z := analyticAt_negInv hzH
  have hmem1 : -(mob v z)⁻¹ ∈ H := Chart.isConformal_infinitySourceChart.2.1 (mob_mem_H v hzH)
  have hmem2 : -z⁻¹ ∈ H := Chart.isConformal_infinitySourceChart.2.1 hzH
  have hF : AnalyticAt ℂ (fun z : ℂ => -2 * Complex.log (-(mob v z)⁻¹) - -2 * Complex.log (-z⁻¹)) z :=
    (analyticAt_const.mul (hA1.clog (hslit hmem1))).sub (analyticAt_const.mul (hA2.clog (hslit hmem2)))
  have he : (brChart v).2.2 = fun z : ℂ => (-2 * Complex.log (-(mob v z)⁻¹) - -2 * Complex.log (-z⁻¹)).im := by
    funext z
    rw [Complex.sub_im]
    rfl
  rw [he]
  exact hF.harmonicAt_im

end InteractingSLE.Supp8.HullDetGen

