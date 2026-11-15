/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Trans
import InteractingSLE.Spec.Sec7.LocalExtDCov

/-!
# The kernel at the stop at the pushed (random) test function

Packet PROVE-STAGEDLAW3. The field read in the record chart pairs the flow-line field with the test function pushed by
the record chart, a random test function. Given a σ-algebra `𝓗`, an `𝓗`-measurable version `R'` of the record on an
event `F` (with an `𝓗`-measurable version `F'` of `F`), and the kernel at the stop at every fixed test function
(`ae_condExp_cexp_stop`), the kernel holds at the pushed test function (`MartMeans2.condExp_cexp_apply_ae_eq_of_local`
with the random open sets `ℍ ∖ K_T` and the local Gaussian laws `exists_gaussLocalLaw`):

* `measurable_chartShift`: the shift is a measurable function of the record;
* **`ae_condExp_cexp_pushTest`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

/-! ### Measurability of the record chart -/

theorem measurableSet_mem_dom_recChart (z : ℂ) : MeasurableSet {r : RecData | z ∈ (recChart r).dom} :=
  measurable_recHist (LocalExt.measurableSet_mem_dom_histChart z)

theorem measurable_indicator_fwd_recChart (z : ℂ) :
    Measurable ({r : RecData | z ∈ (recChart r).dom}.indicator fun r => (recChart r).1 z) :=
  (LocalExt.measurable_indicator_fwd_histChart (nL := 0) (nR := 0) z).comp measurable_recHist

theorem measurable_indicator_lift_recChart (z : ℂ) :
    Measurable ({r : RecData | z ∈ (recChart r).dom}.indicator fun r => (recChart r).2.2 z) :=
  (LocalExt.measurable_indicator_lift_histChart (nL := 0) (nR := 0) z).comp measurable_recHist

theorem measurable_pushTest_recChart (φ : TestOn upperHalfPlaneOpens) (z : ℂ) :
    Measurable fun r : RecData => Chart.pushTest (isConformal_recChart r) φ z :=
  Chart.measurable_pushTest_apply (c := recChart) isConformal_recChart measurableSet_mem_dom_recChart
    measurable_indicator_fwd_recChart φ z

/-- **The shift is a measurable function of the record.** -/
theorem measurable_chartShift (κ θ : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun r : RecData => chartShift κ θ r φ := by
  have h := Chart.measurable_chartTransport_random' (c := recChart) isConformal_recChart
    measurableSet_mem_dom_recChart measurable_indicator_fwd_recChart measurable_indicator_lift_recChart
    (fun r => LocalExt.continuousOn_lift_histChart (recHist r)) (h := fun _ => (0 : DistOn upperHalfPlaneOpens))
    measurable_const 1 0 (chiC κ)
  have h2 := (measurable_distOn_apply φ).comp h
  have e : (fun r : RecData => chartShift κ θ r φ) =
      fun r => Chart.chartTransport (isConformal_recChart r) 1 0 (chiC κ) 0 φ - θ * chiC κ * ∫ w, φ w := by
    funext r
    have hℓ : LocallyIntegrableOn (fun w => (recChart r).2.2 ((recChart r).2.1 w)) H :=
      Chart.locallyIntegrableOn_of_continuousOn
        ((isConformal_recChart r).continuousOn_lift_inv (LocalExt.continuousOn_lift_histChart (recHist r)))
    rw [Chart.chartTransport_apply (isConformal_recChart r) hℓ, chartShift]
    simp only [zero_apply, mul_zero, zero_mul, zero_add]
  rw [e]
  exact h2.sub_const _

/-! ### The kernel at the pushed test function -/

/-- **The kernel at the stop at the test function pushed by the record chart.** -/
theorem ae_condExp_cexp_pushTest {Ω : Type*} {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] (h𝓗 : 𝓗 ≤ mΩ) {h' : Ω → DistOn upperHalfPlaneOpens}
    (hh' : Measurable h') {R R' : Ω → RecData} (hR' : Measurable[𝓗] R') {F F' : Set Ω}
    (hFF' : ∀ᵐ ω ∂Q, ω ∈ F' ↔ ω ∈ F) (hRR' : ∀ᵐ ω ∂Q, ω ∈ F → R' ω = R ω)
    {M : RecData → ℂ → ℝ} (hM : ∀ r, ContinuousOn (M r) (H \ stopHull r))
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q, ω ∈ F → tsupport ψ ⊆ H \ stopHull (R ω) →
      Q[fun ω' => Complex.exp (Complex.I * (h' ω' ψ : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * ((∫ z, M (R ω) z * ψ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ stopHull (R ω)) ψ ψ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, ω ∈ F →
      Q[fun ω' => Complex.exp (Complex.I * (h' ω' (Chart.pushTest (isConformal_recChart (R' ω')) φ) : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * ((∫ z, M (R ω) z * Chart.pushTest (isConformal_recChart (R ω)) φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ stopHull (R ω)) (Chart.pushTest (isConformal_recChart (R ω)) φ)
            (Chart.pushTest (isConformal_recChart (R ω)) φ) : ℝ) : ℂ)) := by
  classical
  set U : Ω → Set ℂ := fun ω => if ω ∈ F' then H \ stopHull (R' ω) else ∅ with hUdef
  have hUsub : ∀ ω, U ω ⊆ H \ stopHull (R' ω) := fun ω => by
    by_cases hω : ω ∈ F'
    · simp only [hUdef, hω, ↓reduceIte, subset_refl]
    · simp only [hUdef, hω, ↓reduceIte, empty_subset]
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hω : ω ∈ F'
    · simp only [hUdef, hω, ↓reduceIte]; exact isOpen_compl_stopHull _
    · simp only [hUdef, hω, ↓reduceIte, isOpen_empty]
  have hUH : ∀ ω, U ω ⊆ H := fun ω => (hUsub ω).trans sdiff_subset
  have hUV : ∀ ω, U ω ⊆ (upperHalfPlaneOpens : Set ℂ) := hUH
  set Ψ : Ω → TestOn upperHalfPlaneOpens → ℂ := fun ω ψ =>
    Complex.exp (Complex.I * ((∫ z, M (R' ω) z * ψ z : ℝ) : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov (U ω) ψ ψ : ℝ) : ℂ)) with hΨdef
  have hT : ∀ z, Measurable[𝓗] fun ω => Chart.pushTest (isConformal_recChart (R' ω)) φ z := fun z =>
    (measurable_pushTest_recChart φ z).comp hR'
  have hRT := Coupling.MartMeans2.condExp_cexp_apply_ae_eq_of_local (P := Q) h𝓗 hh' hUo hUV (Ψ := Ψ)
    (Eventually.of_forall fun ω R hR => by
      have hRH : R ≤ upperHalfPlaneOpens := fun x hx => hUH ω (hR hx)
      obtain ⟨μ, hμP, hμ⟩ := Coupling.MartMeans2.exists_gaussLocalLaw (U := ⟨U ω, hUo ω⟩) (hUH ω) (R := R) hR
        (((hM (R' ω)).mono (hR.trans (hUsub ω))).locallyIntegrableOn R.isOpen.measurableSet)
      refine ⟨μ, hμP, fun ψ => ?_⟩
      rw [hμ ψ, hΨdef]
      simp only [GFF.coe_testIncl hRH ψ]
      rfl)
    (fun ψ => by
      by_cases hψ : (tsupport ψ).Nonempty
      · filter_upwards [hker ψ, hFF', hRR'] with ω hk hF hR hsupp
        by_cases hω : ω ∈ F'
        · have hωF := hF.1 hω
          have hRω := hR hωF
          have hU : U ω = H \ stopHull (R' ω) := by simp only [hUdef, hω, ↓reduceIte]
          rw [hU, hRω] at hsupp
          rw [hk hωF hsupp, hΨdef]
          simp only [hU, hRω]
        · have hU : U ω = ∅ := by simp only [hUdef, hω, ↓reduceIte]
          rw [hU, subset_empty_iff] at hsupp
          exact absurd hsupp hψ.ne_empty
      · have hψ0 : ψ = 0 := by
          ext z
          exact image_eq_zero_of_notMem_tsupport fun hz => hψ ⟨z, hz⟩
        subst hψ0
        refine Eventually.of_forall fun ω _ => ?_
        have h0 : zeroGFFTestCov (U ω) ⇑(0 : TestOn upperHalfPlaneOpens) ⇑(0 : TestOn upperHalfPlaneOpens) = 0 := by
          have := LocalExt.zeroGFFTestCov_smul_left (hUo ω) (hUH ω) (0 : ℝ) (0 : TestOn upperHalfPlaneOpens)
            (0 : TestOn upperHalfPlaneOpens)
          rwa [zero_smul, zero_mul] at this
        simp only [hΨdef, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, h0]
        rw [condExp_const h𝓗]
        simp)
    hT
  filter_upwards [hRT, hFF', hRR'] with ω h1 hF hR hωF
  have hω : ω ∈ F' := hF.2 hωF
  have hRω := hR hωF
  have hU : U ω = H \ stopHull (R' ω) := by simp only [hUdef, hω, ↓reduceIte]
  have hsupp : tsupport (Chart.pushTest (isConformal_recChart (R' ω)) φ) ⊆ U ω := by
    rw [hU, ← coe_dom_recChart]
    exact Chart.tsupport_pushTest_subset _ φ
  rw [h1 hsupp, hΨdef]
  simp only [hU]
  rw [hRω]

end StagedLaw

end Exist

end InteractingSLE
