/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGen
import InteractingSLE.Spec.Restart.DomainMarkovMeanLoc
import InteractingSLE.Spec.Sec7.LocalExtCKernel

/-!
# K2's input (S) for a relative exploration read through a fixed chart and a time change

Packet PROVE-HULLDET. A **relative exploration** of an optional hull coupling `(h, W, …)` (the physical coupling) is
a driver `W̃` whose hull at the relative capacity time `q` is the image, under a fixed conformal chart `c`, of the
physical hull at a stopping time `ℓ q` of the physical driving filtration (the inverse of the relative clock):
`c.inv (ℍ ∖ K̃_q) = ℍ ∖ K_{ℓ q}`. Read through the chart, the physical conditional law at `ℓ q` (the coupling's
conditional-law clause) is the conditional law of the transported field `X = chartTransport c 1 a k h`:

* the covariance transports by conformal invariance of the zero-boundary covariance
  (`DomainMarkov.Mean.zeroGFFTestCov_pushTest_of_subset`, `WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov`);
* the mean transports by the change of variables `Chart.integral_mul_pushTest`; with the **pointwise mean
  identity** `𝔥_{ℓ q} ∘ c.inv + a + k · lift ∘ c.inv = 𝔥̃_q` on `ℍ ∖ K̃_q` (a deterministic statement about the two
  chains) it is the relative coupling mean.

**`hasSafeLaw_of_timeChange`**: K2's input (S) (`DomainMarkov.K2.HasSafeLaw`) for `X` and `W̃`, for every filtration
`𝓗` below the stopped σ-algebras at `ℓ q`. Deterministic charts suffice for the target change of Corollary BR4a
(`w ↦ mob v w`); the identity chart and `ℓ q = q` give (S) for a coupling's own driver.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.HullDetGen

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Coupling

/-! ### Test functions transported by a chart -/

/-- **The transported test function is supported in the image of any set containing the support.** -/
theorem tsupport_pushTest_subset_image {c : Chart} (hc : c.IsConformal) {ψ : TestOn upperHalfPlaneOpens}
    {V : Set ℂ} (hψ : tsupport ψ ⊆ V) :
    tsupport (Chart.pushTest hc ψ) ⊆ c.2.1 '' V := by
  intro z hz
  have hzdom : z ∈ c.dom := Chart.tsupport_pushTest_subset hc ψ hz
  have hzimg : z ∈ c.2.1 '' H := by rw [← hc.coe_dom]; exact hzdom
  obtain ⟨w, hwH, rfl⟩ := hzimg
  refine ⟨w, ?_, rfl⟩
  by_contra hwV
  have hwψ : w ∉ tsupport ψ := fun h => hwV (hψ h)
  -- `ψ` vanishes near `w`; so the transported function vanishes near `c.inv w`
  have hN : ∀ᶠ y in 𝓝 w, ψ y = 0 := by
    have := (isOpen_compl_iff.2 (isClosed_tsupport (ψ : ℂ → ℝ))).mem_nhds hwψ
    filter_upwards [this] with y hy using image_eq_zero_of_notMem_tsupport hy
  obtain ⟨N, hNsub, hNo, hwN⟩ := mem_nhds_iff.1 (hN.and (QuantumZipper.isOpen_H.mem_nhds hwH))
  have hNH : N ⊆ H := fun y hy => (hNsub hy).2
  have hNimg : IsOpen (c.2.1 '' N) := Restart.DomainMarkov.Mean.isOpen_image_inv hc hNo hNH
  have hzero : ∀ y ∈ c.2.1 '' N, Chart.pushTest hc ψ y = 0 := by
    rintro y ⟨n, hn, rfl⟩
    have hndom : c.2.1 n ∈ c.dom := hc.inv_mem_dom (hNH hn)
    rw [Chart.pushTest_apply_of_mem hc ψ hndom]
    have hfi : c.1 (c.2.1 n) = n := hc.2.2 n (hNH hn)
    rw [hfi, (hNsub hn).1, mul_zero]
  have : c.2.1 w ∉ tsupport (Chart.pushTest hc ψ) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hNimg.mem_nhds ⟨w, hwN, rfl⟩] with y hy using hzero y hy
  exact this hz

/-- A continuous function on `ℍ` times a test function is integrable. -/
theorem integrable_mul_test_of_continuousOn {f : ℂ → ℝ} (hf : ContinuousOn f H) (ψ : TestOn upperHalfPlaneOpens) :
    Integrable fun w => f w * ψ w := by
  have hK : IsCompact (tsupport (ψ : ℂ → ℝ)) := ψ.hasCompactSupport.isCompact
  have hc : ContinuousOn (fun w => f w * ψ w) (tsupport (ψ : ℂ → ℝ)) :=
    (hf.mono (Coupling.tsupport_subset_H ψ)).mul ψ.continuous.continuousOn
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 (hc.integrableOn_compact hK)
  intro z hz
  refine subset_tsupport _ ?_
  intro h0
  exact hz (by simp only [h0, mul_zero])


/-- **The transported mean phase.** If `mO ∘ c.inv + a + k · lift ∘ c.inv = mN` on a set containing the support of
`ψ`, and `mN · ψ` is integrable, then the deterministic constant of the chart transport plus the physical phase at
the transported test function is the relative phase. -/
theorem phase_transport {c : Chart} (hc : c.IsConformal) (hliftc : ContinuousOn c.2.2 c.dom) (a k : ℝ)
    {ψ : TestOn upperHalfPlaneOpens} {V : Set ℂ} (hψV : tsupport ψ ⊆ V) {mO mN : ℂ → ℝ}
    (hNI : Integrable fun w => mN w * ψ w) (hpt : ∀ w ∈ V, mO (c.2.1 w) + a + k * c.2.2 (c.2.1 w) = mN w) :
    a * Chart.oneDist ψ + k * Chart.liftDist c ψ + ∫ z, mO z * Chart.pushTest hc ψ z = ∫ w, mN w * ψ w := by
  have hLI : Integrable fun w => c.2.2 (c.2.1 w) * ψ w :=
    integrable_mul_test_of_continuousOn (hc.continuousOn_lift_inv hliftc) ψ
  have hψI : Integrable fun w => ψ w := ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hpt' : (fun w => mO (c.2.1 w) * ψ w) =
      fun w => mN w * ψ w - (a * ψ w + k * (c.2.2 (c.2.1 w) * ψ w)) := by
    funext w
    by_cases hw : ψ w = 0
    · rw [hw]; ring
    · rw [← hpt w (hψV (subset_tsupport _ hw))]; ring
  have hg : Integrable fun w => a * ψ w + k * (c.2.2 (c.2.1 w) * ψ w) := (hψI.const_mul a).add (hLI.const_mul k)
  rw [Chart.oneDist_apply, Chart.liftDist_eq_integral_pushTest hc hliftc, Chart.integral_mul_pushTest,
    Chart.integral_mul_pushTest, hpt', integral_sub hNI hg,
    integral_add (hψI.const_mul a) (hLI.const_mul k), integral_const_mul, integral_const_mul]
  ring

/-! ### The time-changed conditional law -/

section Law

variable {κ : ℝ} {nL nR mL mR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **K2's input (S) for a relative exploration through a fixed chart and a time change.** Let `(h, W, …)` be an
optional hull coupling whose driver is continuous before its lifetime and starts at `0`, `ℓ q` stopping times of its
driving filtration before its lifetime, and `𝓗` a filtration below the stopped σ-algebras at `ℓ q`. Let `c` be a
conformal chart with continuous lift and `Wr` a driver regular on `F`, with force processes `VLr`, `VRr` and lifetime
`ζr`, such that almost surely on `F ∩ {q < ζr}`: the chart carries the relative active domain onto the physical one at
`ℓ q`, and the pointwise mean identity holds there. Then the transported field `chartTransport c 1 a k h` has K2's
input (S) for `Wr`. -/
theorem hasSafeLaw_of_timeChange (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hW : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hX : IsMeasurableKilledDriving W VL VR ζ) {ℓ : ℝ≥0 → Ω → WithTop ℝ≥0}
    (hℓ : ∀ q, IsStoppingTime (drivingFiltration P hX) (ℓ q))
    (hℓζ : ∀ q, ∀ᵐ ω ∂P, ((ℓ q ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝓗 : ∀ q, 𝓗 q ≤ (hℓ q).measurableSpace)
    {c : Chart} (hc : c.IsConformal) (hliftc : ContinuousOn c.2.2 c.dom) (a k : ℝ)
    {ρLr : Fin mL → ℝ} {ρRr : Fin mR → ℝ} {F : Set Ω} {ζr : Ω → ℝ≥0∞} {Wr : ℝ≥0 → Ω → ℝ}
    {VLr : Fin mL → ℝ≥0 → Ω → ℝ} {VRr : Fin mR → ℝ≥0 → Ω → ℝ}
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → Mean.IsDrvReg Wr ζr ω)
    (hK : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζr ω →
      c.2.1 '' (H \ fwdHull (fun s : ℝ => Wr s.toNNReal ω) q) =
        H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((ℓ q ω).untopD 0 : ℝ≥0))
    (hmean : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζr ω →
      ∀ w ∈ H \ fwdHull (fun s : ℝ => Wr s.toNNReal ω) q,
        couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((ℓ q ω).untopD 0 : ℝ≥0)
            (bheProc κ ρL ρR W VL VR ω ((ℓ q ω).untopD 0)) (c.2.1 w) + a + k * c.2.2 (c.2.1 w) =
          couplingMean κ (fun s : ℝ => Wr s.toNNReal ω) q (bheProc κ ρLr ρRr Wr VLr VRr ω q) w) :
    HasSafeLaw κ ρLr ρRr P 𝓗 F ζr Wr VLr VRr fun ω => Chart.chartTransport hc 1 a k (h ω) := by
  have hhm : Measurable h := hC.2.1
  have hXm : Measurable fun ω => Chart.chartTransport hc 1 a k (h ω) :=
    (Chart.measurable_chartTransport hc 1 a k).comp hhm
  refine Mean.hasSafeLaw_of_ae_condExp hXm (fun _ q => (hℓ q).measurableSpace) (fun _ q => h𝓗 q)
    (fun _ q => (hℓ q).measurableSpace_le) ?_
  intro ψ q D hD hDa
  set φ := Chart.pushTest hc ψ with hφ
  set τ : Ω → WithTop ℝ≥0 := ℓ q with hτ
  obtain ⟨-, -, -, hX', hcl⟩ := hC
  have h1 := (hcl τ (hℓ q) (hℓζ q)).2 (fun ω => bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0))
    (fun ω => isBoundedHarmonicExtension_bheProc ω _) φ
  -- the transported field is the physical field at `φ` plus a deterministic constant
  set C : ℝ := a * Chart.oneDist ψ + k * Chart.liftDist c ψ with hC
  have hsplit : (fun ω => Complex.exp (Complex.I * (Chart.chartTransport hc 1 a k (h ω) ψ : ℂ))) =
      fun ω => Complex.exp (Complex.I * (C : ℂ)) * Complex.exp (Complex.I * (h ω φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add, Chart.chartTransport_apply', hC]
    congr 1
    push_cast
    ring
  have hsm : (hℓ q).measurableSpace ≤ mΩ := (hℓ q).measurableSpace_le
  have hcexp := condExp_smul (μ := P) (Complex.exp (Complex.I * (C : ℂ)))
    (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) (hℓ q).measurableSpace
  filter_upwards [h1, hDa, hreg, hK q, hmean q, hW, hℓζ q, hcexp] with ω h1ω hDaω hregω hKω hmω hWω hℓω hcω hωD
  obtain ⟨hωF, hav⟩ := hDaω hωD
  obtain ⟨hqζ, hdisj⟩ := hav
  have hregω' := hregω hωF
  have hKω' := hKω hωF hqζ
  have hmω' := hmω hωF hqζ
  -- supports
  have hVo : IsOpen (H \ fwdHull (fun s : ℝ => Wr s.toNNReal ω) q) :=
    Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath hregω'.1 hqζ
  have hψV : tsupport ψ ⊆ H \ fwdHull (fun s : ℝ => Wr s.toNNReal ω) q := fun z hz =>
    ⟨Coupling.tsupport_subset_H ψ hz, fun hzK => Set.disjoint_left.1 hdisj hz hzK⟩
  have hφV : tsupport φ ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
    rw [← hKω']
    exact tsupport_pushTest_subset_image hc hψV
  have hφdisj : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :=
    Set.disjoint_left.2 fun z hz hzK => (hφV hz).2 hzK
  -- the conditional expectation
  rw [hsplit]
  rw [show (fun ω => Complex.exp (Complex.I * (C : ℂ)) * Complex.exp (Complex.I * (h ω φ : ℂ))) =
    Complex.exp (Complex.I * (C : ℂ)) • fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) from rfl]
  rw [hcω, Pi.smul_apply, h1ω hφdisj, smul_eq_mul, ← Complex.exp_add]
  simp only [cfAt]
  congr 1
  -- the energies
  have hτζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    have key : ∀ x : WithTop ℝ≥0, ((x : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω →
        ((x.untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      intro x hx
      induction x with
      | top => exact absurd hx (not_lt.2 le_top)
      | coe r => rw [WithTop.untopD_coe]; exact hx
    exact key _ hℓω
  have hE1 : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ =
      zeroGFFTestCov (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) φ φ :=
    WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hWω.2 hWω.1 hτζ φ hφdisj
  have hE2 : loewnerGreenEnergy (fun s : ℝ => Wr s.toNNReal ω) q ψ =
      zeroGFFTestCov (H \ fwdHull (fun s : ℝ => Wr s.toNNReal ω) q) ψ ψ :=
    WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hregω'.1 hregω'.2 hqζ ψ hdisj
  have hE3 := Mean.zeroGFFTestCov_pushTest_of_subset hc hVo sdiff_subset hψV
  rw [hKω'] at hE3
  -- the means
  have hwc : ContinuousOn (Ito.rpath fun t => Wr t ω) (Icc 0 (q : ℝ)) := by
    refine hregω'.1.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζr ω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hqζ
  have hNI : Integrable fun w => couplingMean κ (fun s : ℝ => Wr s.toNNReal ω) q
      (bheProc κ ρLr ρRr Wr VLr VRr ω q) w * ψ w :=
    LocalExt.integrable_couplingMean_mul (κ := κ) hwc (isBoundedHarmonicExtension_bheProc
      (κ := κ) (ρL := ρLr) (ρR := ρRr) (W := Wr) (VL := VLr) (VR := VRr) ω q).1 hdisj
  have hmeanI := phase_transport hc hliftc a k hψV hNI hmω'
  rw [hE1, hE3, ← hE2, ← hmeanI, hC]
  push_cast
  ring

/-- **K2's input (L) for a relative exploration through a fixed chart and a time change.** Setting of
`hasSafeLaw_of_timeChange` (`κ > 0`), with a harmonic lift and, for every relative time `s`, a hitting-measurable
relatively closed random set `Bs s` that is almost surely the physical hull at `ℓ s` (a measurable version). The
physical hull at the stopping time `ℓ s` is a history-marked local set for the stopped σ-algebra
(`WholeField.isHistoryAvoidanceLocal_hull`); read through the chart it gives (L)
(`DomainMarkov.Mean.hasSafeMembers_chartTransport`). -/
theorem hasSafeMembers_of_timeChange (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {ℓ : ℝ≥0 → Ω → WithTop ℝ≥0}
    (hℓ : ∀ q, IsStoppingTime (drivingFiltration P hX) (ℓ q))
    (hℓζ : ∀ q, ∀ᵐ ω ∂P, ((ℓ q ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝓗 : ∀ q, 𝓗 q ≤ (hℓ q).measurableSpace)
    {c : Chart} (hc : c.IsConformal) (hliftc : ContinuousOn c.2.2 c.dom)
    (hlift : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom) (a k : ℝ)
    {F : Set Ω} {ζr : Ω → ℝ≥0∞} {Wr : ℝ≥0 → Ω → ℝ}
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → Mean.IsDrvReg Wr ζr ω)
    (hK : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζr ω →
      c.2.1 '' (H \ fwdHull (fun s : ℝ => Wr s.toNNReal ω) q) =
        H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((ℓ q ω).untopD 0 : ℝ≥0))
    (Bs : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ s, Measurable[mΩ, hittingSigma] (Bs s))
    (hBc : ∀ s ω, Bs s ω ⊆ H ∧ IsOpen (H \ Bs s ω))
    (hBK : ∀ s, ∀ᵐ ω ∂P, Bs s ω = fwdHull (fun r : ℝ => W r.toNNReal ω) ((ℓ s ω).untopD 0 : ℝ≥0)) :
    HasSafeMembers P 𝓗 F ζr Wr fun ω => Chart.chartTransport hc 1 a k (h ω) := by
  obtain ⟨u₀, hu₀⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hhm : Measurable h := hC.2.1
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hloc : ∀ s, WholeField.IsHistoryAvoidanceLocal (hℓ s).measurableSpace (Bs s) (WholeField.centredField h u₀) P :=
    fun s => WholeField.isHistoryAvoidanceLocal_hull hC hκ hu₀ hX (hℓ s) (hℓζ s) (hBm s) (hBK s)
  have hcc : ∀ _ω : Ω, c.IsConformal := fun _ => hc
  have hdom : ∀ z, MeasurableSet[⊥] {_ω : Ω | z ∈ c.dom} := fun z => by
    by_cases hz : z ∈ c.dom
    · simp only [hz, ofPred_true, MeasurableSet.univ]
    · simp only [hz, ofPred_false, MeasurableSet.empty]
  have hind : ∀ {β : Type} [Zero β] [MeasurableSpace β] (z : ℂ) (f : ℂ → β),
      Measurable[⊥] ({_ω : Ω | z ∈ c.dom}.indicator fun _ => f z) := by
    intro β _ _ z f
    by_cases hz : z ∈ c.dom
    · simp only [hz, ofPred_true, indicator_univ]
      exact measurable_const
    · simp only [hz, ofPred_false, indicator_empty]
      exact measurable_const
  have hBK' : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (s : ℝ≥0∞) < ζr ω →
      H \ Bs s ω = c.2.1 '' (H \ fwdHull (fun r : ℝ => Wr r.toNNReal ω) s) := by
    intro s
    filter_upwards [hK s, hBK s] with ω h1 h2 hωF hs
    rw [h1 hωF hs, h2]
  exact Mean.hasSafeMembers_chartTransport (𝒢 := ⊥) bot_le hhm hu₀.1 hh0 (c := fun _ => c) hcc hdom
    (fun z => hind z c.1) (fun z => hind z c.2.2) (fun _ => hliftc) (fun _ => hlift) a k
    (fun s => (hℓ s).measurableSpace) h𝓗 (fun s => (hℓ s).measurableSpace_le) Bs hBm hBc hloc hBK' hreg

end Law

end InteractingSLE.Supp8.HullDetGen
