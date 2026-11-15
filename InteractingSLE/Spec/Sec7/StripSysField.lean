/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Coupling.ResampleProjBridge
import InteractingSLE.Spec.Sec2.Assembly2Entr
import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver
import LQGMetric.Complex.HarmonicComp

/-!
# The strip system's field from Theorem 1.1's coupling: the centred counterflow and its GFF

Packet PROVE-STRIPSYS2, item 1 (`planning/handoffs/PROVE-STRIPSYS.md` §5 A). The frozen
`IsCenteredCounterflowDriver κ P h W ζ` asks for the field `h` (parameter `κ`) together with the Theorem 1.1 coupling
(parameter `κ' = 16/κ`) of its infinity-source transport `h' = −h ∘ R − πχ + χ(κ') · lift ∘ R`, `R(z) = −1/z`.
This file builds `h` from `h'` and proves that the frozen relations hold.

* `infinityReturnChart = (R, R, lift ∘ R)`: the inverse of the frozen `infinitySourceChart` (`R ∘ R = id`), whose
  lift read in the coordinate of `ℍ` is the infinity-source lift itself (`infinityReturnChart_lift_inv`);
* **`returnField a k h' = −h' ∘ R + a + k · lift`** (PROVE-PUSHFWD's `chartTransport` of the return chart) and
  **`isChartTransport_returnField`**: `IsChartTransport infinitySourceChart (−1) a k (returnField a k h') h'` for
  every distribution `h'` (the transported test functions compose to the identity, `pushTest_return_pushTest`);
* **`isGFFWithBoundaryData_returnField`**: if `h'` is a GFF with data `g` off the finite set `S`, then
  `returnField a k h'` is a GFF with the data `returnData a k g` (`x ↦ −g(−1/x) + a + k ℓ(x)`, `ℓ = −2π` on `ℝ₋` and
  `0` on `ℝ₊`, the boundary values of the lift `Im(−2 Log z)`) off `insert 0 (R '' S)`;
* the transported data of a piecewise-constant word (`counterflowData`) and its inverse.

Mathematical steps added (standard; not in the specification): `R` is a holomorphic involution of `ℍ` with
`|R'(z)|² |R'(R z)|² = 1`; harmonic functions compose with holomorphic maps (LQGMetric's `harmonicOnNhd_comp_holo`);
`Im(−2 Log z) = −2 arg z` is harmonic on `ℍ` with boundary values `0` on `ℝ₊` and `−2π` on `ℝ₋`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H isOpen_H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Sec7

namespace StripSysField

/-! ### The return chart `(R, R, lift ∘ R)` -/

/-- **The return chart** `(R, R, lift ∘ R)`, `R(z) = −1/z`: the inverse of the frozen infinity-source chart. Read in
the coordinate of `ℍ` its lift is the infinity-source lift (`infinityReturnChart_lift_inv`). -/
def infinityReturnChart : Chart :=
  (fun z => -z⁻¹, fun z => -z⁻¹, fun z => infinitySourceChart.2.2 (-z⁻¹))

theorem isConformal_infinityReturnChart : infinityReturnChart.IsConformal :=
  Chart.isConformal_infinitySourceChart

theorem negInv_negInv (z : ℂ) : -(-z⁻¹)⁻¹ = z := by rw [inv_neg, inv_inv, neg_neg]

theorem infinityReturnChart_lift_inv (w : ℂ) :
    infinityReturnChart.2.2 (infinityReturnChart.2.1 w) = infinitySourceChart.2.2 w := by
  change infinitySourceChart.2.2 (-(-w⁻¹)⁻¹) = _
  rw [negInv_negInv]

/-- The infinity-source lift `Im(−2 Log z)`. -/
theorem infinitySourceChart_lift (z : ℂ) : infinitySourceChart.2.2 z = -2 * Complex.arg z := by
  change (-2 * Complex.log z).im = _
  simp [Complex.mul_im, Complex.log_im]

theorem mem_H_ne_zero {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  rw [h] at hz; exact lt_irrefl _ (show (0 : ℝ) < 0 by simp [H] at hz)

theorem negInv_mem_H {z : ℂ} (hz : z ∈ H) : -z⁻¹ ∈ H := Chart.isConformal_infinitySourceChart.2.1 hz

theorem continuousOn_infinitySourceChart_lift' : ContinuousOn infinitySourceChart.2.2 H := by
  intro w hw
  have hslit : w ∈ Complex.slitPlane := Or.inr (ne_of_gt hw)
  change ContinuousWithinAt (fun w : ℂ => (-2 * Complex.log w).im) H w
  exact (Complex.continuous_im.continuousAt.comp
    (continuousAt_const.mul (continuousAt_clog hslit))).continuousWithinAt

theorem continuousOn_infinityReturnChart_lift :
    ContinuousOn (fun w => infinityReturnChart.2.2 (infinityReturnChart.2.1 w)) H := by
  simp_rw [infinityReturnChart_lift_inv]
  exact continuousOn_infinitySourceChart_lift'

theorem norm_deriv_negInv (z : ℂ) : ‖deriv (fun z : ℂ => -z⁻¹) z‖ = ‖z‖⁻¹ ^ 2 := by
  rw [deriv.fun_neg, deriv_inv, neg_neg, norm_inv, norm_pow, inv_pow]

theorem coe_dom_infinitySourceChart : (infinitySourceChart.dom : Set ℂ) = H := by
  rw [Chart.isConformal_infinitySourceChart.coe_dom]
  refine Subset.antisymm (fun _ ⟨w, hw, e⟩ => e ▸ negInv_mem_H hw) fun z hz =>
    ⟨-z⁻¹, negInv_mem_H hz, negInv_negInv z⟩

theorem coe_dom_infinityReturnChart : (infinityReturnChart.dom : Set ℂ) = H :=
  coe_dom_infinitySourceChart

/-- **The two transported test functions compose to the identity**: `|R'|² (|R'|² φ ∘ R) ∘ R = φ`. -/
theorem pushTest_return_pushTest (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest isConformal_infinityReturnChart (Chart.pushTest Chart.isConformal_infinitySourceChart φ) = φ := by
  ext z
  by_cases hz : z ∈ H
  · have hz' : z ∈ infinityReturnChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinityReturnChart]; exact hz
    have hRz : (-z⁻¹) ∈ infinitySourceChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinitySourceChart]; exact negInv_mem_H hz
    rw [Chart.pushTest_apply_of_mem _ _ hz']
    change ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2 * Chart.pushTest _ φ (-z⁻¹) = φ z
    rw [Chart.pushTest_apply_of_mem _ _ hRz]
    change ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2 * (‖deriv (fun z : ℂ => -z⁻¹) (-z⁻¹)‖ ^ 2 * φ (-(-z⁻¹)⁻¹)) = φ z
    rw [norm_deriv_negInv, norm_deriv_negInv, negInv_negInv, norm_neg, norm_inv, inv_inv, ← mul_assoc,
      ← mul_pow, ← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_H_ne_zero hz)), one_pow, one_pow, one_mul]
  · have hz' : z ∉ infinityReturnChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinityReturnChart]; exact hz
    rw [Chart.pushTest_apply_of_notMem _ _ hz']
    exact (φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)).symm

/-! ### The return field -/

/-- **The return field** `−h' ∘ R + a + k · lift`: the field whose infinity-source transport (coefficients `−1`, `a`,
`k`) is `h'`. -/
def returnField (a k : ℝ) (h' : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Chart.chartTransport isConformal_infinityReturnChart (-1) a k h'

theorem measurable_returnField (a k : ℝ) : Measurable (returnField a k) :=
  Chart.measurable_chartTransport _ _ _ _

theorem returnField_apply (a k : ℝ) (h' : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    returnField a k h' φ = -1 * h' (Chart.pushTest isConformal_infinityReturnChart φ) + a * (∫ w, φ w) +
      k * ∫ w, infinitySourceChart.2.2 w * φ w := by
  rw [returnField, Chart.chartTransport_apply _
    (Chart.locallyIntegrableOn_of_continuousOn continuousOn_infinityReturnChart_lift)]
  simp_rw [infinityReturnChart_lift_inv]

/-- **The return field satisfies the frozen infinity-source transport relation** with the field `h'`. -/
theorem isChartTransport_returnField (a k : ℝ) (h' : DistOn upperHalfPlaneOpens) :
    IsChartTransport infinitySourceChart (-1) a k (returnField a k h') h' := by
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest Chart.isConformal_infinitySourceChart hsupp hφ, returnField_apply,
    pushTest_return_pushTest]
  have e1 : ∫ w, Chart.pushTest Chart.isConformal_infinitySourceChart φ' w = ∫ w, φ' w := by
    have h := Chart.integral_mul_pushTest Chart.isConformal_infinitySourceChart φ' (fun _ => 1)
    simpa only [one_mul] using h
  have e2 := Chart.integral_mul_pushTest Chart.isConformal_infinitySourceChart φ' infinitySourceChart.2.2
  rw [e1, e2]
  ring

/-! ### The boundary data of the return field -/

/-- The boundary values of the infinity-source lift `Im(−2 Log z) = −2 arg z`: `0` on `ℝ₊`, `−2π` on `ℝ₋`. -/
def liftBoundary (x : ℝ) : ℝ := if x < 0 then -(2 * Real.pi) else 0

/-- **The boundary data of the return field** `x ↦ −g(−1/x) + a + k ℓ(x)`. -/
def returnData (a k : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := -g (-x⁻¹) + a + k * liftBoundary x

/-- The exceptional set `{0} ∪ R(S)` of the return data. -/
def returnExcept (S : Finset ℝ) : Finset ℝ := insert 0 (S.image fun w => -w⁻¹)

theorem ne_zero_of_notMem_returnExcept {S : Finset ℝ} {x : ℝ} (hx : x ∉ returnExcept S) : x ≠ 0 :=
  fun h => hx (Finset.mem_insert.2 (Or.inl h))

theorem negInv_notMem_of_notMem_returnExcept {S : Finset ℝ} {x : ℝ} (hx : x ∉ returnExcept S) : -x⁻¹ ∉ S :=
  fun h => hx (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-x⁻¹, h, by rw [inv_neg, inv_inv, neg_neg]⟩))

theorem tendsto_infinitySourceChart_lift {x : ℝ} (hx : x ≠ 0) :
    Tendsto infinitySourceChart.2.2 (𝓝[H] (x : ℂ)) (𝓝 (liftBoundary x)) := by
  have e : infinitySourceChart.2.2 = fun z => -2 * Complex.arg z := funext infinitySourceChart_lift
  rw [e]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h := Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := (x : ℂ)) (by simpa using hneg) (by simp)
    have h' := (h.mono_left (nhdsWithin_mono _
      (show H ⊆ {z : ℂ | 0 ≤ z.im} from fun z (hz : z ∈ H) => (show 0 < z.im from hz).le))).const_mul (-2)
    simp only [liftBoundary, hneg, ↓reduceIte, show -(2 * Real.pi) = -2 * Real.pi by ring]
    exact h'
  · have hslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
    have h := ((Complex.continuousAt_arg hslit).tendsto.mono_left (nhdsWithin_le_nhds (s := H))).const_mul (-2)
    rw [Complex.arg_ofReal_of_nonneg hpos.le, mul_zero] at h
    simp only [liftBoundary, not_lt.2 hpos.le, ↓reduceIte]
    exact h

theorem tendsto_negInv_nhdsWithin_H {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun z : ℂ => -z⁻¹) (𝓝[H] (x : ℂ)) (𝓝[H] ((-x⁻¹ : ℝ) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => negInv_mem_H hz⟩
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
  have h := ((continuousAt_inv₀ hx').neg).tendsto
  rw [show ((-x⁻¹ : ℝ) : ℂ) = -(x : ℂ)⁻¹ by push_cast; ring]
  exact h.mono_left nhdsWithin_le_nhds

theorem abs_infinitySourceChart_lift_le (z : ℂ) : |infinitySourceChart.2.2 z| ≤ 2 * Real.pi := by
  rw [infinitySourceChart_lift, abs_mul, abs_neg, abs_two]
  exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi z) zero_le_two

theorem harmonicOnNhd_infinitySourceChart_lift : InnerProductSpace.HarmonicOnNhd infinitySourceChart.2.2 H := by
  intro z hz
  have hslit : z ∈ Complex.slitPlane := Or.inr (ne_of_gt hz)
  exact (analyticAt_const.mul (analyticAt_clog hslit)).harmonicAt_im

/-- **The bounded harmonic extension of the return data** is `z ↦ −u(−1/z) + a + k Im(−2 Log z)`. -/
theorem isBoundedHarmonicExtension_return (a k : ℝ) {g : ℝ → ℝ} {S : Finset ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) :
    IsBoundedHarmonicExtension (returnData a k g) (returnExcept S)
      (fun z => -u (-z⁻¹) + a + k * infinitySourceChart.2.2 z) := by
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu
  have hcomp : InnerProductSpace.HarmonicOnNhd (u ∘ fun z : ℂ => -z⁻¹) H :=
    LQGMetric.harmonicOnNhd_comp_holo isOpen_H isOpen_H hharm Chart.isConformal_infinitySourceChart.1
      fun z hz => negInv_mem_H hz
  refine ⟨fun z hz => ?_, ⟨C + |a| + |k| * (2 * Real.pi), fun z hz => ?_⟩, fun x hx => ?_⟩
  · have h1 := ((hcomp z hz).neg.add (InnerProductSpace.harmonicAt_const a)).add
      ((harmonicOnNhd_infinitySourceChart_lift z hz).const_smul (c := k))
    convert h1 using 1
    funext w
    simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  · have h1 := hC _ (negInv_mem_H hz)
    have h2 := abs_infinitySourceChart_lift_le z
    calc |-u (-z⁻¹) + a + k * infinitySourceChart.2.2 z|
        ≤ |-u (-z⁻¹)| + |a| + |k * infinitySourceChart.2.2 z| := abs_add_three _ _ _
      _ ≤ C + |a| + |k| * (2 * Real.pi) := by
        rw [abs_neg, abs_mul]
        gcongr
  · have hx0 := ne_zero_of_notMem_returnExcept hx
    have h1 := (hlim _ (negInv_notMem_of_notMem_returnExcept hx)).comp (tendsto_negInv_nhdsWithin_H hx0)
    have h2 := tendsto_infinitySourceChart_lift hx0
    exact (h1.neg.add_const a).add (h2.const_mul k)

/-! ### Zero-boundary processes under negation -/

/-- The negative of a zero-boundary GFF process is one. -/
theorem isZBGFFProcess_neg {U : TopologicalSpace.Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : TestOn U → Ω → ℝ} (hX : LQGMetric.IsZBGFFProcess U X P) :
    LQGMetric.IsZBGFFProcess U (fun φ ω => -X φ ω) P where
  measurable φ := (hX.measurable φ).neg
  gaussian := by
    have h := hX.gaussian.smul (fun _ => (-1 : ℝ))
    simpa only [neg_one_smul] using h
  centered φ := by rw [integral_neg, hX.centered φ, neg_zero]
  covariance_eq φ ψ := by
    rw [covariance_fun_neg_left, covariance_fun_neg_right, neg_neg]
    exact hX.covariance_eq φ ψ

theorem infinityReturnChart_dom : infinityReturnChart.dom = upperHalfPlaneOpens :=
  SetLike.coe_injective coe_dom_infinityReturnChart

/-- **The return field of a GFF is a GFF** with the return data: if `h'` is a GFF on `ℍ` with data `g` off the
finite set `S` (and `g` has a bounded harmonic extension), then `−h' ∘ R + a + k · lift` is a GFF with data
`returnData a k g` off `returnExcept S` (conformal invariance of the zero-boundary GFF under `R`). -/
theorem isGFFWithBoundaryData_returnField (a k : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h' : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Finset ℝ}
    (hg : ∃ u, IsBoundedHarmonicExtension g S u) (hh : IsGFFWithBoundaryData P h' g S) :
    IsGFFWithBoundaryData P (fun ω => returnField a k (h' ω)) (returnData a k g) (returnExcept S) := by
  refine ⟨(measurable_returnField a k).comp hh.1, fun u₀ hu₀ => ?_⟩
  obtain ⟨u', hu'⟩ := hg
  have hu := isBoundedHarmonicExtension_return a k hu'
  have hbdd : ∀ {v : ℂ → ℝ}, (∃ C : ℝ, ∀ z ∈ H, |v z| ≤ C) → Bornology.IsBounded (v '' H) := by
    rintro v ⟨C, hC⟩
    exact isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact (hC z hz)⟩
  have heq : EqOn u₀ (fun z => -u' (-z⁻¹) + a + k * infinitySourceChart.2.2 z) H := by
    refine eqOn_of_tendsto_sub_H (returnExcept S) hu₀.1 hu.1 (hbdd hu₀.2.1) (hbdd hu.2.1) fun t ht => ?_
    simpa only [sub_self] using (hu₀.2.2 t ht).sub (hu.2.2 t ht)
  -- the zero-boundary process of `h'`, written on the return chart's domain
  have key : ∀ U : TopologicalSpace.Opens ℂ, U = upperHalfPlaneOpens → LQGMetric.IsZBGFFProcess U
      (fun ψ ω => h' ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, u' z * ψ z) P := by
    rintro U rfl
    have hid : ∀ ψ : TestOn upperHalfPlaneOpens,
        GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens ψ = ψ := fun ψ => by
      ext z
      exact congrFun (GFF.coe_testIncl le_rfl ψ) z
    simp only [hid]
    exact hh.2 u' hu'
  have hℓ := Chart.locallyIntegrableOn_of_continuousOn continuousOn_infinityReturnChart_lift
  have hX := isZBGFFProcess_neg (Chart.isZBGFFProcess_chartTransport isConformal_infinityReturnChart hℓ
    (m := u') 0 (key _ infinityReturnChart_dom))
  convert hX using 2 with φ
  funext ω
  have hcont : ContinuousOn (fun z => u' (-z⁻¹)) H :=
    hu'.1.continuousOn.comp Chart.isConformal_infinitySourceChart.1.continuousOn fun z hz => negInv_mem_H hz
  have hi1 : Integrable (fun z => u' (-z⁻¹) * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcont φ φ.tsupport_subset
  have hi2 : Integrable (fun z => infinitySourceChart.2.2 z * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn continuousOn_infinitySourceChart_lift' φ
      φ.tsupport_subset
  have hi3 : Integrable (fun z => a * φ z) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul a
  have e0 : ∫ z, u₀ z * φ z = ∫ z, (-u' (-z⁻¹) + a + k * infinitySourceChart.2.2 z) * φ z := by
    congr 1
    funext z
    by_cases hz : z ∈ H
    · rw [heq hz]
    · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
      rw [h0, mul_zero, mul_zero]
  have e1 : ∫ z, (-u' (-z⁻¹) + a + k * infinitySourceChart.2.2 z) * φ z =
      -(∫ z, u' (-z⁻¹) * φ z) + a * (∫ z, φ z) + k * ∫ z, infinitySourceChart.2.2 z * φ z := by
    have e : (fun z => (-u' (-z⁻¹) + a + k * infinitySourceChart.2.2 z) * φ z) =
        fun z => (-(u' (-z⁻¹) * φ z) + a * φ z) + k * (infinitySourceChart.2.2 z * φ z) := by
      funext z
      ring
    have hn : Integrable (fun z => -(u' (-z⁻¹) * φ z)) := hi1.neg
    rw [e, integral_add (f := fun z => -(u' (-z⁻¹) * φ z) + a * φ z)
      (g := fun z => k * (infinitySourceChart.2.2 z * φ z)) (hn.add hi3) (hi2.const_mul k),
      integral_add (f := fun z => -(u' (-z⁻¹) * φ z)) (g := fun z => a * φ z) hn hi3, integral_neg,
      integral_const_mul, integral_const_mul]
  rw [e0, e1, returnField_apply, Chart.chartTransport_apply']
  change _ = -(1 * h' ω (Chart.pushTest _ φ) + 0 * _ + 0 * _ -
    ((∫ w, u' (-w⁻¹) * φ w) + 0 * ∫ w, infinityReturnChart.2.2 (infinityReturnChart.2.1 w) * φ w))
  ring

/-! ### Inverting the return data; piecewise-constant data -/

/-- The data whose return data is `g` (`returnData_inverseData`): `inverseData a k g = returnData (a − 2πk) (−k) g`. -/
def inverseData (a k : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := returnData (a - 2 * Real.pi * k) (-k) g

theorem liftBoundary_add_liftBoundary_negInv {x : ℝ} (hx : x ≠ 0) :
    liftBoundary x + liftBoundary (-x⁻¹) = -(2 * Real.pi) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h1 : ¬ (-x⁻¹ < 0) := not_lt.2 (neg_nonneg.2 (inv_nonpos.2 hneg.le))
    simp only [liftBoundary, hneg, h1, ↓reduceIte, add_zero]
  · have h1 : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hpos)
    simp only [liftBoundary, not_lt.2 hpos.le, h1, ↓reduceIte, zero_add]

theorem returnData_inverseData (a k : ℝ) (g : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    returnData a k (inverseData a k g) x = g x := by
  have h := liftBoundary_add_liftBoundary_negInv hx
  simp only [returnData, inverseData, inv_neg, inv_inv, neg_neg]
  linear_combination k * h

theorem negInv_eventually_mem {y : ℝ} (hy : y ≠ 0) {T : Set ℝ} (hT : T ∈ 𝓝 (-y⁻¹)) :
    ∀ᶠ z in 𝓝 y, -z⁻¹ ∈ T :=
  ((continuousAt_inv₀ hy).neg).tendsto.eventually_mem hT

theorem eventually_liftBoundary_eq {y : ℝ} (hy : y ≠ 0) : ∀ᶠ z in 𝓝 y, liftBoundary z = liftBoundary y := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · filter_upwards [Iio_mem_nhds hneg] with z hz
    simp only [liftBoundary, show z < 0 from hz, hneg, ↓reduceIte]
  · filter_upwards [Ioi_mem_nhds hpos] with z hz
    simp only [liftBoundary, not_lt.2 (show (0 : ℝ) < z from hz).le, not_lt.2 hpos.le, ↓reduceIte]

/-- Return data of piecewise-constant data are piecewise constant off `returnExcept`. -/
theorem isPiecewiseConstant_returnData (a k : ℝ) {g : ℝ → ℝ} {J : Finset ℝ}
    (hg : IsPiecewiseConstantBoundaryData g J) :
    IsPiecewiseConstantBoundaryData (returnData a k g) (returnExcept J) := by
  intro y hy
  have hy0 := ne_zero_of_notMem_returnExcept hy
  have h1 := negInv_eventually_mem hy0 (hg _ (negInv_notMem_of_notMem_returnExcept hy))
  filter_upwards [h1, eventually_liftBoundary_eq hy0] with z hz hl
  simp only [returnData, hl, show g (-z⁻¹) = g (-y⁻¹) from hz]

theorem subset_returnExcept_returnExcept (J : Finset ℝ) : J ⊆ returnExcept (returnExcept J) := by
  intro x hx
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-x⁻¹, Finset.mem_insert_of_mem
    (Finset.mem_image.2 ⟨x, hx, rfl⟩), by rw [inv_neg, inv_inv, neg_neg]⟩)

/-! ### Changing the boundary data and the exceptional set -/

/-- A GFF with data `g'` off `S'` is one with data `g` off `S ⊆ S'` when `g = g'` off `S'`. -/
theorem isGFFWithBoundaryData_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {g g' : ℝ → ℝ} {S S' : Set ℝ} (hSS : S ⊆ S')
    (hg : ∀ x ∉ S', g' x = g x) (hh : IsGFFWithBoundaryData P h g' S') : IsGFFWithBoundaryData P h g S := by
  refine ⟨hh.1, fun u hu => hh.2 u ⟨hu.1, hu.2.1, fun x hx => ?_⟩⟩
  rw [hg x hx]
  exact hu.2.2 x fun h => hx (hSS h)

/-- The bounded harmonic extension of force boundary data exists (the landed `Impl` companion theorem; the data read
only the weights and the positions given). -/
theorem exists_isBoundedHarmonicExtension_forceBoundaryData (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u := by
  let F : Impl.ForceWord :=
    { nL := nL, nR := nR, xL := fun _ => 0, xR := fun _ => 0, ρL := ρL, ρR := ρR,
      antitone_xL := fun _ _ _ => le_rfl, xL_nonpos := fun _ => le_rfl,
      monotone_xR := fun _ _ _ => le_rfl, xR_nonneg := fun _ => le_rfl }
  obtain ⟨u, hu, -⟩ := Impl.existsUnique_isBoundedHarmonicExtension_forceBoundaryData κ F vL vR
  exact ⟨u, hu⟩

/-- **The field of a flow-line coupling at seed `0`, angle `0`, is a GFF with the word's data** `b` (off its jump
candidates): the force-word data of the flow-line word agree with `b` (PROVE-FLOWEXIST's
`eqOn_flowLine_harmonicExtension`). -/
theorem isGFFWithBoundaryData_of_flowLineGFF {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (forceBoundaryData κ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0))) :
    IsGFFWithBoundaryData P h b J := by
  refine ⟨hh.1, fun u₀ hu₀ => ?_⟩
  obtain ⟨uF, huF⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b J 0 0)
    (flowLineRhoR κ b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)
  have heq := Exist.eqOn_flowLine_harmonicExtension hκ hb 0 0 hu₀ huF
  convert hh.2 uF huF using 4 with φ ω
  congr 1
  funext z
  by_cases hz : z ∈ H
  · rw [heq hz]
    simp only [Complex.ofReal_zero, add_zero, zero_mul]
  · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
    rw [h0, mul_zero, mul_zero]

/-! ### Infinite lifetime -/

/-- **The continuation threshold is infinite** when both sides have group-end sums at least some `c > −2` (Aux.
lemma 6's lifetime argument). The same statement and proof as `ZhanGT4.IsIntegratedSLEEvolution.
ae_lifetime_eq_top_of_groupEndSums` (in flight in `Spec/ZhanGT4/WordsRef.lean`, which is not tracked yet and so is not
imported); every ingredient is a landed `Sec2`/`Sec4` lemma. -/
theorem ae_lifetime_eq_top_of_groupEndSums {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : ℝ} (hc : -2 < c)
    (hword : IsOrderedForceWord xL xR) (hL : Sec4.HasGroupEndSums c ρL (-xL)) (hR : Sec4.HasGroupEndSums c ρR xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hword
  have hsL := (Sec4.neg_two_lt_sum_of_hasGroupEndSums hc hL).ne'
  have hsR := (Sec4.neg_two_lt_sum_of_hasGroupEndSums hc hR).ne'
  filter_upwards [h.ae_tendsto_threshold_of_ne hsL hsR, h.ae_isIntegratedSLEPath] with ω hlim hp
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
  have hfp := hp.isForcePath
  rcases eq_zero_or_pos T with hT0 | hT0
  · have h0 : ζ ω = 0 := by rw [← hT, hT0, ENNReal.coe_zero]
    exact Sec4.not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR hxL hxR hxL0 hxR0
      (fun _ _ h => h) (fun _ _ h => h) (hfp.threshold_of_eq_zero h0)
  · obtain ⟨w₀, vL₀, vR₀, hlim', hth⟩ := hlim T hT0 hT
    have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hT]; exact_mod_cast ht
    have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := hlim'.fst_nhds
    have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.fst_nhds i
    have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.snd_nhds i
    refine Sec4.not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR ?_ ?_ ?_ ?_ ?_ ?_ hth
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvL j) (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht hij)
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij)
    · intro i
      exact le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
    · intro i
      exact le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
    · intro i j hij
      exact tendsto_nhds_unique (hvL i)
        ((hvL j).congr' (hev.mono fun t ht => (hp.vL_eq_of_xL_eq ht hij).symm))
    · intro i j hij
      exact tendsto_nhds_unique (hvR i)
        ((hvR j).congr' (hev.mono fun t ht => (hp.vR_eq_of_xR_eq ht hij).symm))

/-! ### The centred counterflow from Theorem 1.1 -/

/-- The parameter-field offset `a = −πχ(κ)` of the frozen `IsCenteredCounterflowDriver`. -/
def cfOffset (κ : ℝ) : ℝ := -(Real.pi * QuantumZipper.chiC κ)

/-- The parameter-field lift coefficient `χ(16/κ)` of the frozen `IsCenteredCounterflowDriver`. -/
def cfCoeff (κ : ℝ) : ℝ := QuantumZipper.chiC (16 / κ)

/-- **The boundary data `b'` of the counterflow parameter field** `F_d(h)^R` for flow-field data `b`
(`b'(w) = −b(−1/w) − πχ + χ(16/κ) ℓ(−1/w)` up to the constant fixed by `returnData_inverseData`). -/
def counterflowData (κ : ℝ) (b : ℝ → ℝ) : ℝ → ℝ := inverseData (cfOffset κ) (cfCoeff κ) b

/-- The exceptional set `{0} ∪ R(jumps)` of the counterflow data. -/
def counterflowJumps (jumps : Finset ℝ) : Finset ℝ := returnExcept jumps

theorem isPiecewiseConstant_counterflowData (κ : ℝ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) :
    IsPiecewiseConstantBoundaryData (counterflowData κ b) (counterflowJumps jumps) :=
  isPiecewiseConstant_returnData _ _ hb

/-- **The non-hit condition on the counterflow word** (the source's choice of heights, e.g. Aux. lemma 130's
`a, b ≥ λ + πχ/2`, `a', b' ≥ λ + 3πχ/2`): the flow-line word, at parameter `16/κ`, of the counterflow data has
group-end sums at least some `c > −2` on both sides. -/
def IsNonhitCounterflowWord (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∃ c : ℝ, -2 < c ∧
    Sec4.HasGroupEndSums c (flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0)
      (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0) ∧
    Sec4.HasGroupEndSums c (flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0)
      (flowLineXR (counterflowData κ b) (counterflowJumps jumps) 0)

theorem isTranslateAddConst_zero_self (h : DistOn upperHalfPlaneOpens) (c : ℝ) :
    IsTranslateAddConst 0 (0 * c) h h := by
  intro φ φ' hφ
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  rw [e, zero_mul, zero_mul, add_zero]

/-- **The centred counterflow coupling from Theorem 1.1** (packet item 1; `PROVE-STRIPSYS` §5 A without the
standard Borel requirement). For `0 < κ` and piecewise-constant flow-field data `b`, there are a probability space,
a GFF `h` on `ℍ` with data `b`, and the driver `W` (lifetime `ζ`) of the centred counterflow of `h`
(frozen `IsCenteredCounterflowDriver`). The coupling is Theorem 1.1's (assembled from Theorem 2.2's existence,
`Coupling.exists_isOptionalHullCoupling_of_thm22`) at parameter `16/κ` for the flow-line word of the counterflow data
`counterflowData κ b`, and `h` is the return field of its field. Under the non-hit condition the lifetime is
almost surely infinite. -/
theorem exists_isCenteredCounterflowDriver {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h b jumps ∧ IsCenteredCounterflowDriver κ P h W ζ ∧
        (IsNonhitCounterflowWord κ b jumps → ∀ᵐ ω ∂P, ζ ω = ⊤) := by
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  set b' := counterflowData κ b with hb'def
  set J' := counterflowJumps jumps with hJ'def
  have hb' : IsPiecewiseConstantBoundaryData b' J' := isPiecewiseConstant_counterflowData κ hb
  have hF := Theorem15.isOrderedForceWord_flowLine b' J' 0
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h', hC⟩ :=
    Coupling.exists_isOptionalHullCoupling_of_thm22.{u} hκ' hF
      (exists_isIntegratedSLEEvolution_assembled (ρL := flowLineRhoL (16 / κ) b' J' 0 0)
        (ρR := flowLineRhoR (16 / κ) b' J' 0 0) hκ' hF)
  refine ⟨Ω, mΩ, P, hP, fun ω => returnField (cfOffset κ) (cfCoeff κ) (h' ω), W, ζ, ?_, ?_, ?_⟩
  · -- the field: Theorem 1.1's GFF clause, the flow-line data, and the return transport
    have hh' : IsGFFWithBoundaryData P h' b' J' := isGFFWithBoundaryData_of_flowLineGFF hκ' hb' ⟨hC.2.1, hC.2.2.1⟩
    have hex : ∃ u, IsBoundedHarmonicExtension b' J' u := by
      obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
      exact ⟨u, hu⟩
    have hR := isGFFWithBoundaryData_returnField (cfOffset κ) (cfCoeff κ) hex hh'
    refine isGFFWithBoundaryData_of_subset (subset_returnExcept_returnExcept jumps) (fun x hx => ?_) hR
    exact returnData_inverseData _ _ b (ne_zero_of_notMem_returnExcept hx)
  · exact ⟨b', J', h', hb', fun ω => isChartTransport_returnField _ _ (h' ω),
      h', 𝓕, VL, VR, B, fun ω => isTranslateAddConst_zero_self (h' ω) _, hC⟩
  · rintro ⟨c, hc, hL, hR⟩
    exact ae_lifetime_eq_top_of_groupEndSums hc hF hL hR hC.1

end StripSysField

end Sec7

end InteractingSLE
