/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsChartTransport
import InteractingSLE.Frozen.Spec.Chart_id
import InteractingSLE.Frozen.Spec.Chart_recenter
import InteractingSLE.Frozen.Spec.Chart_loewner
import InteractingSLE.Frozen.Spec.infinitySourceChart
import InteractingSLE.GFF.Markov
import SupercriticalConformalCovariance.ZBConformal.Pullback
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.RS.GenerationBasic
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.Frozen.Spec.couplingMean
import SupercriticalConformalCovariance.GM24.TVReduce

/-!
# The field transported by a conformal chart: `h ∘ inv + k · (lift ∘ inv)` (deterministic part)

Packet PROVE-PUSHFWD. For a chart `c = (fwd, inv, lift)` of the exploration domain `U = inv '' ℍ ⊆ ℍ`
(frozen `Chart`) the frozen relation `IsChartTransport c σ a k h h'` says that `h'` is `(σ h + a) ∘ inv + k (lift ∘ inv)`
on `ℍ`, tested against the change-of-variables transport `φ = (φ' ∘ fwd) |fwd′|²` of `φ'` (Specification p. 2, (1.4)).
This file constructs that distribution and proves that it is the only one.

* `Chart.IsConformal c` : `inv` is holomorphic on `ℍ`, maps `ℍ` into `ℍ`, and `fwd ∘ inv = id` on `ℍ`
  (so `inv : ℍ → U` is a conformal bijection with inverse `fwd`); `Chart.dom c` is the open set `U`.
* `Chart.pushTest hc : 𝓓(ℍ) →L 𝓓(ℍ)`, `φ' ↦ 1_U |fwd′|² (φ' ∘ fwd)` (SupercriticalConformalCovariance's
  `confPushTest` of `inv`, extended by zero to `ℍ`), with `Chart.coe_pushTest`;
* `Chart.pullField hc h = h ∘ inv` (`h` tested against `pushTest`), equal to SupercriticalConformalCovariance's
  `distPullback` of `h|_U` (`pullField_eq_distPullback`);
* **`Chart.chartTransport hc σ a k h = σ (h ∘ inv) + a + k (lift ∘ inv)`** and
  **`Chart.isChartTransport_chartTransport`** (it satisfies the frozen relation whenever `lift ∘ inv` is locally
  integrable on `ℍ`), **`IsChartTransport.eq_chartTransport`** / `IsChartTransport.unique` (it is the only one), and
  `existsUnique_isChartTransport`;
* `measurable_chartTransport` (a fixed chart transports random distributions to random distributions);
* the charts of the specification are conformal: `Chart.isConformal_id`, `IsConformal.recenter`,
  `isConformal_infinitySourceChart`, `IsConformal.loewner` (centred Loewner maps of a continuous driver).

The random-chart versions (measurability in `ω`) are in `GFF/PushforwardMeas.lean`, the laws in
`GFF/PushforwardLaw.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H isOpen_H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

namespace InteractingSLE

/-- A chart `c = (fwd, inv, lift)` is **conformal** when `inv` is holomorphic on `ℍ`, maps `ℍ` into `ℍ`, and `fwd`
inverts it there. Then `inv` is a conformal bijection of `ℍ` onto the open set `U = inv '' ℍ ⊆ ℍ` with inverse
`fwd|_U` (holomorphic on `U`, `Chart.IsConformal.differentiableOn_fwd`). -/
def Chart.IsConformal (c : Chart) : Prop :=
  DifferentiableOn ℂ c.2.1 H ∧ MapsTo c.2.1 H H ∧ ∀ w ∈ H, c.1 (c.2.1 w) = w

/-- The chart domain `U = inv '' ℍ`, as an open set (`interior` keeps it open for every chart; for a conformal chart
it is `inv '' ℍ`, `Chart.IsConformal.coe_dom`). -/
def Chart.dom (c : Chart) : Opens ℂ :=
  ⟨interior (c.2.1 '' H), isOpen_interior⟩

namespace Chart

variable {c : Chart}

theorem IsConformal.injOn (hc : c.IsConformal) : InjOn c.2.1 H := fun w₁ hw₁ w₂ hw₂ h => by
  rw [← hc.2.2 w₁ hw₁, ← hc.2.2 w₂ hw₂, h]

theorem IsConformal.isOpen_image (hc : c.IsConformal) : IsOpen (c.2.1 '' H) :=
  SmallGammaGeodesics.CC.isOpen_image_conf isOpen_H hc.1 hc.injOn

theorem IsConformal.coe_dom (hc : c.IsConformal) : (c.dom : Set ℂ) = c.2.1 '' H :=
  hc.isOpen_image.interior_eq

theorem IsConformal.dom_subset (hc : c.IsConformal) : (c.dom : Set ℂ) ⊆ H := by
  rw [hc.coe_dom]
  exact hc.2.1.image_subset

theorem IsConformal.dom_le (hc : c.IsConformal) : c.dom ≤ upperHalfPlaneOpens :=
  hc.dom_subset

theorem IsConformal.inv_mem_dom (hc : c.IsConformal) {w : ℂ} (hw : w ∈ H) : c.2.1 w ∈ c.dom := by
  rw [SetLike.mem_coe.symm, hc.coe_dom]
  exact mem_image_of_mem _ hw

theorem IsConformal.fwd_mem (hc : c.IsConformal) {z : ℂ} (hz : z ∈ c.dom) : c.1 z ∈ H := by
  rw [← SetLike.mem_coe, hc.coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rwa [hc.2.2 w hw]

theorem IsConformal.inv_fwd (hc : c.IsConformal) {z : ℂ} (hz : z ∈ c.dom) : c.2.1 (c.1 z) = z := by
  rw [← SetLike.mem_coe, hc.coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [hc.2.2 w hw]

/-- Membership in the chart domain is decided pointwise by the chart maps. -/
theorem IsConformal.mem_dom_iff (hc : c.IsConformal) {z : ℂ} :
    z ∈ c.dom ↔ c.1 z ∈ H ∧ c.2.1 (c.1 z) = z := by
  refine ⟨fun hz => ⟨hc.fwd_mem hz, hc.inv_fwd hz⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← h₂]
  exact hc.inv_mem_dom h₁

theorem IsConformal.isConformalBijection (hc : c.IsConformal) :
    IsConformalBijection c.2.1 (upperHalfPlaneOpens : Set ℂ) (c.dom : Set ℂ) :=
  ⟨hc.1, by rw [hc.coe_dom]; exact hc.injOn.bijOn_image⟩

theorem IsConformal.differentiableOn_fwd (hc : c.IsConformal) : DifferentiableOn ℂ c.1 c.dom := by
  rw [hc.coe_dom]
  exact SmallGammaGeodesics.CC.differentiableOn_leftInv isOpen_H hc.1 hc.injOn hc.2.2

/-- On the chart domain, `fwd` is the inverse function of `inv` chosen by `invFunOn`. -/
theorem IsConformal.invFunOn_eq (hc : c.IsConformal) {z : ℂ} (hz : z ∈ c.dom) :
    Function.invFunOn c.2.1 H z = c.1 z := by
  rw [← SetLike.mem_coe, hc.coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [hc.injOn.leftInvOn_invFunOn hw, hc.2.2 w hw]

/-! ### The transported test function -/

/-- **The transported test function** `φ' ↦ 1_U |fwd′|² (φ' ∘ fwd)` on `ℍ` (`coe_pushTest`): the test-function side
of `h ↦ h ∘ inv`, SupercriticalConformalCovariance's `confPushTest` of `inv : ℍ → U` followed by the extension by
zero from `U` to `ℍ`. -/
def pushTest (hc : c.IsConformal) : TestOn upperHalfPlaneOpens →L[ℝ] TestOn upperHalfPlaneOpens :=
  (GFF.testIncl c.dom upperHalfPlaneOpens).comp (confPushTest hc.isConformalBijection)

theorem coe_pushTest (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    ⇑(pushTest hc φ) = (c.dom : Set ℂ).indicator fun z => ‖deriv c.1 z‖ ^ 2 * φ (c.1 z) := by
  change ⇑(GFF.testIncl c.dom upperHalfPlaneOpens (confPushTest hc.isConformalBijection φ)) = _
  rw [GFF.coe_testIncl hc.dom_le]
  funext z
  change (c.dom : Set ℂ).indicator (fun y => ‖deriv (Function.invFunOn c.2.1 H) y‖ ^ 2 *
    φ (Function.invFunOn c.2.1 H y)) z = _
  by_cases hz : z ∈ (c.dom : Set ℂ)
  · rw [indicator_of_mem hz, indicator_of_mem hz, hc.invFunOn_eq hz]
    have he : Function.invFunOn c.2.1 H =ᶠ[𝓝 z] c.1 :=
      Filter.eventuallyEq_of_mem (c.dom.isOpen.mem_nhds hz) fun y hy => hc.invFunOn_eq hy
    rw [he.deriv_eq]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

theorem pushTest_apply_of_mem (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) {z : ℂ}
    (hz : z ∈ c.dom) : pushTest hc φ z = ‖deriv c.1 z‖ ^ 2 * φ (c.1 z) := by
  rw [coe_pushTest, indicator_of_mem (show z ∈ (c.dom : Set ℂ) from hz)]

theorem pushTest_apply_of_notMem (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) {z : ℂ}
    (hz : z ∉ c.dom) : pushTest hc φ z = 0 := by
  rw [coe_pushTest, indicator_of_notMem (show z ∉ (c.dom : Set ℂ) from hz)]

theorem tsupport_pushTest_subset (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (pushTest hc φ) ⊆ c.dom := by
  have h := (confPushTest hc.isConformalBijection φ).tsupport_subset
  change tsupport ⇑(GFF.testIncl c.dom upperHalfPlaneOpens (confPushTest hc.isConformalBijection φ)) ⊆ _
  rwa [GFF.coe_testIncl hc.dom_le]

/-- **Change of variables** `z = inv w`: `∫ u · pushTest φ = ∫ (u ∘ inv) · φ` for every function `u`. -/
theorem integral_mul_pushTest (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) (u : ℂ → ℝ) :
    ∫ z, u z * pushTest hc φ z = ∫ w, u (c.2.1 w) * φ w := by
  have h := SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest
    hc.isConformalBijection φ u
  change ∫ z, u z * (GFF.testIncl c.dom upperHalfPlaneOpens
    (confPushTest hc.isConformalBijection φ)) z = _
  rw [GFF.coe_testIncl hc.dom_le]
  exact h

/-- A test function supported in the chart domain that is the transport of `φ'` there is `pushTest φ'`. -/
theorem eq_pushTest (hc : c.IsConformal) {φ φ' : TestOn upperHalfPlaneOpens}
    (hsupp : tsupport φ ⊆ c.2.1 '' H)
    (hφ : ∀ z ∈ c.2.1 '' H, φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2) : φ = pushTest hc φ' := by
  ext z
  by_cases hz : z ∈ c.dom
  · rw [pushTest_apply_of_mem hc φ' hz, mul_comm]
    exact hφ z (by rw [← hc.coe_dom]; exact hz)
  · rw [pushTest_apply_of_notMem hc φ' hz]
    exact image_eq_zero_of_notMem_tsupport fun h => hz (by
      rw [← SetLike.mem_coe, hc.coe_dom]; exact hsupp h)

/-! ### The transported field -/

/-- `h ∘ inv` on `ℍ`: the distribution `h` tested against the transported test functions. -/
def pullField (hc : c.IsConformal) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  h.comp (pushTest hc)

theorem pullField_apply (hc : c.IsConformal) (h : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) : pullField hc h φ = h (pushTest hc φ) := rfl

/-- `h ∘ inv` is SupercriticalConformalCovariance's conformal pullback of `h|_U` by `inv : ℍ → U`. -/
theorem pullField_eq_distPullback (hc : c.IsConformal) (h : DistOn upperHalfPlaneOpens) :
    pullField hc h = SupercriticalConformalCovariance.ZBConformal.distPullback hc.isConformalBijection
      (GFF.restrictDist c.dom h) := rfl

/-- The constant function `1` on `ℍ` as a distribution. -/
def oneDist : DistOn upperHalfPlaneOpens :=
  Distribution.ofFun upperHalfPlaneOpens (fun _ => (1 : ℝ)) volume ⊤

/-- The derivative lift written in the coordinate of `ℍ`, `lift ∘ inv`, as a distribution on `ℍ` (zero if it is not
locally integrable on `ℍ`). -/
def liftDist (c : Chart) : DistOn upperHalfPlaneOpens :=
  Distribution.ofFun upperHalfPlaneOpens (fun w => c.2.2 (c.2.1 w)) volume ⊤

theorem oneDist_apply (φ : TestOn upperHalfPlaneOpens) : oneDist φ = ∫ w, φ w := by
  rw [oneDist, Distribution.ofFun_apply (locallyIntegrableOn_const _)]
  simp only [smul_eq_mul, mul_one]

theorem liftDist_apply (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H)
    (φ : TestOn upperHalfPlaneOpens) : liftDist c φ = ∫ w, c.2.2 (c.2.1 w) * φ w := by
  rw [liftDist, Distribution.ofFun_apply hℓ]
  simp only [smul_eq_mul, mul_comm]

/-- **The chart transport** `σ (h ∘ inv) + a + k (lift ∘ inv)` of `σ h + a` (frozen `IsChartTransport`). -/
def chartTransport (hc : c.IsConformal) (σ a k : ℝ) (h : DistOn upperHalfPlaneOpens) :
    DistOn upperHalfPlaneOpens :=
  σ • pullField hc h + a • oneDist + k • liftDist c

theorem chartTransport_apply' (hc : c.IsConformal) (σ a k : ℝ) (h : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    chartTransport hc σ a k h φ = σ * h (pushTest hc φ) + a * oneDist φ + k * liftDist c φ := rfl

theorem chartTransport_apply (hc : c.IsConformal) (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H)
    (σ a k : ℝ) (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    chartTransport hc σ a k h φ =
      σ * h (pushTest hc φ) + a * (∫ w, φ w) + k * ∫ w, c.2.2 (c.2.1 w) * φ w := by
  rw [chartTransport_apply', oneDist_apply, liftDist_apply hℓ]

/-- **The chart transport satisfies the frozen relation** `IsChartTransport`. -/
theorem isChartTransport_chartTransport (hc : c.IsConformal)
    (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H) (σ a k : ℝ) (h : DistOn upperHalfPlaneOpens) :
    IsChartTransport c σ a k h (chartTransport hc σ a k h) := by
  intro φ φ' hsupp hφ
  rw [chartTransport_apply hc hℓ, eq_pushTest hc hsupp hφ]

/-- Any transport is given by the chart formula. -/
theorem _root_.InteractingSLE.IsChartTransport.apply_eq {σ a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (hc : c.IsConformal) (ht : IsChartTransport c σ a k h h') (φ' : TestOn upperHalfPlaneOpens) :
    h' φ' = σ * h (pushTest hc φ') + a * (∫ w, φ' w) + k * ∫ w, c.2.2 (c.2.1 w) * φ' w :=
  ht (pushTest hc φ') φ' (by rw [← hc.coe_dom]; exact tsupport_pushTest_subset hc φ')
    fun z hz => by
      rw [← hc.coe_dom] at hz
      rw [pushTest_apply_of_mem hc φ' hz, mul_comm]

/-- **Uniqueness**: a conformal chart determines the transported field. -/
theorem _root_.InteractingSLE.IsChartTransport.unique {σ a k : ℝ} {h h₁ h₂ : DistOn upperHalfPlaneOpens}
    (hc : c.IsConformal) (h₁t : IsChartTransport c σ a k h h₁) (h₂t : IsChartTransport c σ a k h h₂) :
    h₁ = h₂ := by
  ext φ'
  rw [h₁t.apply_eq hc, h₂t.apply_eq hc]

theorem _root_.InteractingSLE.IsChartTransport.eq_chartTransport {σ a k : ℝ}
    {h h' : DistOn upperHalfPlaneOpens} (hc : c.IsConformal)
    (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H) (ht : IsChartTransport c σ a k h h') :
    h' = chartTransport hc σ a k h :=
  ht.unique hc (isChartTransport_chartTransport hc hℓ σ a k h)

theorem isChartTransport_iff (hc : c.IsConformal) (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H)
    {σ a k : ℝ} {h h' : DistOn upperHalfPlaneOpens} :
    IsChartTransport c σ a k h h' ↔ h' = chartTransport hc σ a k h :=
  ⟨fun ht => ht.eq_chartTransport hc hℓ, fun e => e ▸ isChartTransport_chartTransport hc hℓ σ a k h⟩

theorem existsUnique_isChartTransport (hc : c.IsConformal)
    (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H) (σ a k : ℝ) (h : DistOn upperHalfPlaneOpens) :
    ∃! h' : DistOn upperHalfPlaneOpens, IsChartTransport c σ a k h h' :=
  ⟨_, isChartTransport_chartTransport hc hℓ σ a k h, fun _ ht => ht.eq_chartTransport hc hℓ⟩

/-- A continuous lift (in the coordinate of `ℍ`) is locally integrable. -/
theorem locallyIntegrableOn_of_continuousOn {ℓ : ℂ → ℝ} (hℓ : ContinuousOn ℓ H) :
    LocallyIntegrableOn ℓ H :=
  hℓ.locallyIntegrableOn isOpen_H.measurableSet

/-- A fixed chart transports random distributions measurably. -/
theorem measurable_chartTransport (hc : c.IsConformal) (σ a k : ℝ) :
    Measurable (chartTransport hc σ a k) :=
  LQGMetric.measurable_distOn_iff.2 fun φ =>
    (((LQGMetric.measurable_distOn_apply (pushTest hc φ)).const_mul σ).add_const _).add_const _

/-- The transport is affine in the field: `σ (h₁ + h₂) ∘ inv = σ h₁ ∘ inv + σ h₂ ∘ inv`. -/
theorem chartTransport_add (hc : c.IsConformal) (σ a k : ℝ) (h₁ h₂ : DistOn upperHalfPlaneOpens) :
    chartTransport hc σ a k (h₁ + h₂) = chartTransport hc σ a k h₁ + pullField hc (σ • h₂) := by
  ext φ
  simp only [chartTransport_apply', pullField_apply, add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem chartTransport_sub (hc : c.IsConformal) (σ a k : ℝ) (h₁ h₂ : DistOn upperHalfPlaneOpens) :
    chartTransport hc σ a k h₁ - chartTransport hc σ a k h₂ = pullField hc (σ • (h₁ - h₂)) := by
  ext φ
  simp only [chartTransport_apply', pullField_apply, sub_apply,
    smul_apply, smul_eq_mul]
  ring

/-! ### The charts of the specification are conformal -/

theorem isConformal_id : Chart.id.IsConformal :=
  ⟨differentiableOn_id, mapsTo_id _, fun _ _ => rfl⟩

/-- Recentring at a real point keeps a chart conformal. -/
theorem IsConformal.recenter (hc : c.IsConformal) (a : ℝ) : (c.recenter a).IsConformal := by
  have hm : MapsTo (fun z : ℂ => z + a) H H := fun z hz => by
    change 0 < (z + a).im
    rw [Complex.add_im, Complex.ofReal_im, add_zero]
    exact hz
  refine ⟨hc.1.comp (differentiableOn_id.add_const _) hm, hc.2.1.comp hm, fun w hw => ?_⟩
  change c.1 (c.2.1 (w + a)) - a = w
  rw [hc.2.2 _ (hm hw), add_sub_cancel_right]

/-- Recentring does not change the chart domain (real translations preserve `ℍ`). -/
theorem dom_recenter (c : Chart) (a : ℝ) : (c.recenter a).dom = c.dom := by
  have he : (c.recenter a).2.1 '' H = c.2.1 '' H := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w + a, ?_, rfl⟩
      change 0 < (w + a).im
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      exact hw
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w - a, ?_, ?_⟩
      · change 0 < (w - a).im
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
        exact hw
      · change c.2.1 (w - a + a) = c.2.1 w
        rw [sub_add_cancel]
  ext x
  change x ∈ interior ((c.recenter a).2.1 '' H) ↔ x ∈ interior (c.2.1 '' H)
  rw [he]

/-- The infinity-source chart `R(z) = −1/z` is conformal. -/
theorem isConformal_infinitySourceChart : infinitySourceChart.IsConformal := by
  have hm : MapsTo (fun z : ℂ => -z⁻¹) H H := fun z hz => by
    change 0 < (-z⁻¹).im
    have hz0 : z ≠ 0 := fun h => by
      rw [h] at hz; exact lt_irrefl _ (show (0 : ℝ) < 0 by simp [H] at hz)
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hz (Complex.normSq_pos.2 hz0)
  refine ⟨fun z hz => ?_, hm, fun w hw => ?_⟩
  · have hz0 : z ≠ 0 := fun h => by
      rw [h] at hz; exact lt_irrefl _ (show (0 : ℝ) < 0 by simp [H] at hz)
    exact (differentiableAt_inv hz0).neg.differentiableWithinAt
  · change -(-w⁻¹)⁻¹ = w
    rw [inv_neg, inv_inv, neg_neg]

/-- **The Loewner stage of a conformal chart is conformal**: `fwd ↦ f_t ∘ fwd`, `inv ↦ inv ∘ f_t⁻¹` for a continuous
driver with `W 0 = 0` and `t ≥ 0` (`f_t⁻¹ = fwdMapInv W t` is holomorphic on `ℍ`, maps `ℍ` into `ℍ`, and is a right
inverse of `f_t` there). -/
theorem IsConformal.loewner (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : (c.loewner W t).IsConformal := by
  have hm : MapsTo (QuantumZipper.fwdMapInv W t) H H := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hw
  refine ⟨hc.1.comp (QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 ht) hm, hc.2.1.comp hm,
    fun w hw => ?_⟩
  change QuantumZipper.fwdMap W t (c.1 (c.2.1 (QuantumZipper.fwdMapInv W t w))) = w
  rw [hc.2.2 _ (hm hw), QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hw]

/-! ### Continuity of the lifts in the coordinate of `ℍ` -/

theorem continuousOn_id_lift : ContinuousOn (fun w => Chart.id.2.2 (Chart.id.2.1 w)) H :=
  continuousOn_const

theorem continuousOn_recenter_lift {a : ℝ} (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) :
    ContinuousOn (fun w => (c.recenter a).2.2 ((c.recenter a).2.1 w)) H := by
  have hm : MapsTo (fun z : ℂ => z + a) H H := fun z hz => by
    change 0 < (z + a).im
    rw [Complex.add_im, Complex.ofReal_im, add_zero]
    exact hz
  exact hℓ.comp (continuousOn_id.add continuousOn_const) hm

theorem continuousOn_infinitySourceChart_lift :
    ContinuousOn (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w)) H := by
  intro w hw
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; exact lt_irrefl _ (show (0 : ℝ) < 0 by simp [H] at hw)
  have hR : (-w⁻¹) ∈ H := isConformal_infinitySourceChart.2.1 hw
  have hslit : (-w⁻¹) ∈ Complex.slitPlane := Or.inr (ne_of_gt hR)
  change ContinuousWithinAt (fun w : ℂ => (-2 * Complex.log (-w⁻¹)).im) H w
  refine (Complex.continuous_im.continuousAt.comp ?_).continuousWithinAt
  exact (continuousAt_const.mul ((continuousAt_clog hslit).comp (f := fun w : ℂ => -w⁻¹)
    (continuousAt_inv₀ hw0).neg))

/-- The lift of a Loewner stage, in the coordinate of `ℍ`, is continuous when the old lift is:
`lift'(inv' w) = Im log f_t′(F_t w) + lift(inv(F_t w))`, `F_t = f_t⁻¹`. -/
theorem IsConformal.continuousOn_loewner_lift (hc : c.IsConformal)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun w => (c.loewner W t).2.2 ((c.loewner W t).2.1 w)) H := by
  have hm : MapsTo (QuantumZipper.fwdMapInv W t) H H := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hw
  have he : EqOn (fun w => (c.loewner W t).2.2 ((c.loewner W t).2.1 w))
      (fun w => (QuantumZipper.logDerivFwd W t (QuantumZipper.fwdMapInv W t w)).im +
        c.2.2 (c.2.1 (QuantumZipper.fwdMapInv W t w))) H := fun w hw => by
    change (QuantumZipper.logDerivFwd W t (c.1 (c.2.1 (QuantumZipper.fwdMapInv W t w)))).im +
      c.2.2 (c.2.1 (QuantumZipper.fwdMapInv W t w)) = _
    rw [hc.2.2 _ (hm hw)]
  refine ContinuousOn.congr ?_ he
  refine ContinuousOn.add (fun w hw => ?_) (hℓ.comp (fun w hw =>
    (QuantumZipper.RS.continuousAt_fwdMapInv hW hW0 ht hw).continuousWithinAt) hm)
  have hF := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw
  exact (Complex.continuous_im.continuousAt.comp ((continuousAt_logDerivFwd hW ht hF).comp
    (QuantumZipper.RS.continuousAt_fwdMapInv hW hW0 ht hw))).continuousWithinAt

/-! ### Lifts continuous on the chart domain -/

/-- A lift continuous on the chart domain is continuous in the coordinate of `ℍ`. -/
theorem IsConformal.continuousOn_lift_inv (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom) :
    ContinuousOn (fun w => c.2.2 (c.2.1 w)) H :=
  hℓ.comp hc.1.continuousOn fun _ hw => hc.inv_mem_dom hw

/-- `lift · pushTest φ` is continuous on `ℂ` when the lift is continuous on the chart domain (`pushTest φ` vanishes
near every point off the domain). -/
theorem continuous_lift_mul_pushTest (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom)
    (φ : TestOn upperHalfPlaneOpens) : Continuous fun z => c.2.2 z * pushTest hc φ z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ c.dom
  · exact ((hℓ z hz).continuousAt (c.dom.isOpen.mem_nhds hz)).mul (pushTest hc φ).continuous.continuousAt
  · have h0 : (fun y => pushTest hc φ y) =ᶠ[𝓝 z] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h => hz (tsupport_pushTest_subset hc φ h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with y hy
    rw [hy, mul_zero]

/-- The lift distribution against the transported test function (change of variables). -/
theorem liftDist_eq_integral_pushTest (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom)
    (φ : TestOn upperHalfPlaneOpens) : liftDist c φ = ∫ z, c.2.2 z * pushTest hc φ z := by
  rw [liftDist_apply (locallyIntegrableOn_of_continuousOn (hc.continuousOn_lift_inv hℓ)),
    integral_mul_pushTest]

/-! ### Transported means -/

/-- A distribution given by a function on the chart domain transports to the function composed with `inv`. -/
theorem pullField_apply_of_eq_integral (hc : c.IsConformal) {T : DistOn upperHalfPlaneOpens} {m : ℂ → ℝ}
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.dom → T φ = ∫ z, m z * φ z)
    (φ : TestOn upperHalfPlaneOpens) : pullField hc T φ = ∫ w, m (c.2.1 w) * φ w := by
  rw [pullField_apply, hT _ (tsupport_pushTest_subset hc φ), integral_mul_pushTest]

/-- **The transported coupling mean is the harmonic extension.** For the Loewner chart `(f_t, f_t⁻¹, arg f_t′)` the
coupling mean `𝔥_t = u ∘ f_t − χ arg f_t′` (frozen `couplingMean`) transports, with coefficient `k = χ`, to `u`:
the derivative lift of the chart cancels the term `−χ arg f_t′`. -/
theorem chartTransport_loewner_couplingMean {κ : ℝ} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {u : ℂ → ℝ} (hu : ContinuousOn u H) {T : DistOn upperHalfPlaneOpens}
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (Chart.id.loewner W t).dom →
      T φ = ∫ z, couplingMean κ W t u z * φ z) (φ : TestOn upperHalfPlaneOpens) :
    chartTransport (isConformal_id.loewner hW hW0 ht) 1 0 (QuantumZipper.chiC κ) T φ = ∫ w, u w * φ w := by
  set hc := isConformal_id.loewner hW hW0 ht
  have hℓc := isConformal_id.continuousOn_loewner_lift continuousOn_id_lift hW hW0 ht
  rw [chartTransport_apply', ← pullField_apply, pullField_apply_of_eq_integral hc hT,
    liftDist_apply (locallyIntegrableOn_of_continuousOn hℓc)]
  have he : ∀ w, couplingMean κ W t u ((Chart.id.loewner W t).2.1 w) * φ w =
      u w * φ w - QuantumZipper.chiC κ *
        ((Chart.id.loewner W t).2.2 ((Chart.id.loewner W t).2.1 w) * φ w) := fun w => by
    by_cases hw : w ∈ H
    · change (u (QuantumZipper.fwdMap W t (QuantumZipper.fwdMapInv W t w)) -
        QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd W t (QuantumZipper.fwdMapInv W t w)).im) * φ w =
        u w * φ w - QuantumZipper.chiC κ *
          (((QuantumZipper.logDerivFwd W t (QuantumZipper.fwdMapInv W t w)).im + 0) * φ w)
      rw [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hw]
      ring
    · have h0 : φ w = 0 := φ.zero_on_compl hw
      rw [h0]
      ring
  simp_rw [he]
  have hi₁ : Integrable fun w => u w * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (B := upperHalfPlaneOpens) hu φ
    simpa only [mul_comm] using this
  have hi₂ : Integrable fun w => (Chart.id.loewner W t).2.2 ((Chart.id.loewner W t).2.1 w) * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (B := upperHalfPlaneOpens) hℓc φ
    simpa only [mul_comm] using this
  rw [integral_sub hi₁ (hi₂.const_mul _), integral_const_mul]
  ring

end Chart

end InteractingSLE
