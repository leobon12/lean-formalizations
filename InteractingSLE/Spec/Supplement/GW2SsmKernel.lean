/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SsmMean

/-!
# GW2's stage mean: (G1) for the canonical stage mean from the conditional kernel

Packet PROVE-GW2-STAGEMEAN, stage-mean round. The kernel route delivers the conditional law of the centred field
under `μ_{ω₀} = condExpKernel P 𝒢 ω₀`, in the kernel-route chart (`caMean`). This file moves it to `P` in the
canonical stage-chart form (`GW2Ssm.stageMean`), which is what `StageInst.stagePhysLawAt_of_stageLaw` consumes:

* **`ae_ae_condExpKernel_of_ae`**: a `P`-almost-sure property holds `μ_{ω₀}`-almost surely for `P`-a.e. `ω₀`
  (`condExpKernel_comp_trim`, `Measure.ae_ae_of_ae_comp`, `ae_of_ae_trim`); so the per-sample dilation identity
  `caMean = stageMean` (true `P`-a.s.) can be used under the kernel;
* **`ae_gaussLaw_of_kernel`**: the Gaussian conditional characteristic function moves from the kernel to `P` on an
  `𝓗`-event, given an `𝓗`-measurable mean and a nonnegative `𝓗`-measurable variance
  (`GW2Scl.ae_condExp_eq_on_of_ae_condExpKernel`);
* **`StageInst.stageLaw_of_kernel_caLaw`**: (G1) for `stageMean` under `P`, from (G1) for `caMean` under the kernel,
  the dilation data and the stage shape (under `P`), and the `ℋ t`-measurability of the stage event
  `E_φ = {ω ∈ G, supp φ ⊆ ℍ ∖ B t}` and of the restrictions to `E_φ` of `ω ↦ ∫ stageMean ω · φ` and of
  `ω ↦ Cov_{ℍ∖B t}(φ, φ)`;
* **`StageInst.stagePhysLawAt_of_kernel`**: hence `GW2Spm.StagePhysLawAt`.

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Ssm

/-- **A `P`-almost-sure property holds almost surely under the conditional kernel, for `P`-a.e. `ω₀`.** -/
theorem ae_ae_condExpKernel_of_ae {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), p ω := by
  have h' : ∀ᵐ ω ∂(condExpKernel P 𝒢 ∘ₘ P.trim h𝒢), p ω := by
    rw [condExpKernel_comp_trim h𝒢]
    exact h
  exact ae_of_ae_trim h𝒢 (Measure.ae_ae_of_ae_comp h')

/-- **The Gaussian conditional characteristic function moves from the kernel to `P` on an `𝓗`-event.** -/
theorem ae_gaussLaw_of_kernel {Ω : Type*} {𝒢 𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (h𝓗 : 𝓗 ≤ mΩ)
    {Y m v : Ω → ℝ} (hY : Measurable Y) (hm : Measurable[𝓗] m) (hv : Measurable[𝓗] v) (hv0 : ∀ ω, 0 ≤ v ω)
    {E : Set Ω} (hE : MeasurableSet[𝓗] E) (ρ : ℝ)
    (hk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ E →
      (condExpKernel P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' : ℝ) : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * ((ρ * m ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (ρ ^ 2 * v ω)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' : ℝ) : ℂ)) | 𝓗] ω =
      Complex.exp (Complex.I * ((ρ * m ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (ρ ^ 2 * v ω)) : ℝ) : ℂ) := by
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I x
  have hfm : Measurable fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_const.mul hY)))
  have hFm : Measurable[𝓗] fun ω => Complex.exp (Complex.I * ((ρ * m ω : ℝ) : ℂ)) *
      ((Real.exp (-(1 / 2) * (ρ ^ 2 * v ω)) : ℝ) : ℂ) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul hm)))).mul (Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hv))))
  refine GW2Scl.ae_condExp_eq_on_of_ae_condExpKernel h𝒢 h𝓗 (C := 1) hfm.stronglyMeasurable
    (fun ω => (hnorm _).le) hFm.stronglyMeasurable (fun ω => ?_) hE hk
  rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.exp_le_one_iff]
  have := mul_nonneg (sq_nonneg ρ) (hv0 ω)
  linarith

/-- **The same, with the mean and the variance only read on the event** (`𝓗`-measurability of their restrictions). -/
theorem ae_gaussLaw_of_kernel_on {Ω : Type*} {𝒢 𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (h𝓗 : 𝓗 ≤ mΩ)
    {Y m v : Ω → ℝ} (hY : Measurable Y) {E : Set Ω} (hE : MeasurableSet[𝓗] E) (hm : Measurable[𝓗] (E.indicator m))
    (hv : Measurable[𝓗] (E.indicator v)) (hv0 : ∀ ω ∈ E, 0 ≤ v ω) (ρ : ℝ)
    (hk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ E →
      (condExpKernel P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' : ℝ) : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * ((ρ * m ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (ρ ^ 2 * v ω)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' : ℝ) : ℂ)) | 𝓗] ω =
      Complex.exp (Complex.I * ((ρ * m ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (ρ ^ 2 * v ω)) : ℝ) : ℂ) := by
  have hv0' : ∀ ω, 0 ≤ E.indicator v ω := fun ω => by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      exact hv0 ω hω
    · rw [indicator_of_notMem hω]
  have hk' : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ E →
      (condExpKernel P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' : ℝ) : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * ((ρ * E.indicator m ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * E.indicator v ω)) : ℝ) : ℂ) := by
    filter_upwards [hk] with ω₀ h0
    filter_upwards [h0] with ω h1 hωE
    rw [indicator_of_mem hωE, indicator_of_mem hωE]
    exact h1 hωE
  filter_upwards [ae_gaussLaw_of_kernel h𝒢 h𝓗 hY hm hv hv0' hE ρ hk'] with ω h1 hωE
  rw [h1 hωE, indicator_of_mem hωE, indicator_of_mem hωE]

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 LocalSets WholeField GW2Spm GW2Sdl
  GW2Sdm GW2Smk

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **(G1) for the canonical stage mean under `P`, from (G1) for the kernel-route mean under the conditional kernel.**
The dilation data and the stage shape hold `P`-a.s. (hence under the kernel for a.e. `ω₀`); the stage event, the
stage-mean pairing and the covariance are `ℋ t`-measurable. -/
theorem StageInst.stageLaw_of_kernel_caLaw [StandardBorelSpace Ω] [IsProbabilityMeasure c.P] (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0)
    (h𝒢 : 𝒢 ≤ mΩ) (hℋ : I.ℋ t ≤ mΩ) {G : Set Ω}
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationOnAt I c r l w t G ca Sn lam Uca)
    (hBo : ∀ ω, IsOpen (H \ I.B t ω))
    (hev : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[I.ℋ t] {ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω})
    (hmm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => ∫ z, stageMean I c r l w t ω z * φ z))
    (hcm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => zeroGFFTestCov (H \ I.B t ω) φ φ))
    (hk : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P 𝒢 ω₀),
      ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      ((condExpKernel c.P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ))
        | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca Sn lam Uca t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, stageMean I c r l w t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ) := by
  have heqK := ae_ae_condExpKernel_of_ae h𝒢 (StageInst.ae_eqOn_caMean_stageMean I hv hpre w t hshape hdil)
  have hk' : ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P 𝒢 ω₀), ω ∈ {ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω} →
      ((condExpKernel c.P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ))
        | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, stageMean I c r l w t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ) := by
    filter_upwards [hk φ ρ, heqK] with ω₀ h1 h2
    filter_upwards [law_congr_of_eqOn h2 h1] with ω h hE
    exact h hE.1 hE.2
  have hY : Measurable fun ω => centredField c.h I.u₀ ω φ :=
    (Sobolev.measurable_distOn_apply φ).comp (WholeField.measurable_centredField c.hh.1 I.u₀)
  have h := ae_gaussLaw_of_kernel_on h𝒢 hℋ hY (hev φ) (hmm φ) (hcm φ)
    (fun ω _ => LocalSets.zeroGFFTestCov_self_nonneg (hBo ω) sdiff_subset φ) ρ hk'
  filter_upwards [h] with ω hω hωG hsupp
  exact hω ⟨hωG, hsupp⟩

/-- **`GW2Spm.StagePhysLawAt` from the kernel route**: (G1) for the kernel-route mean under the conditional kernel,
the dilation data and the stage shape under `P`, and the `ℋ t`-measurability of the stage event, the stage-mean pairing
and the covariance. No harmonicity input. -/
theorem StageInst.stagePhysLawAt_of_kernel [StandardBorelSpace Ω] [IsProbabilityMeasure c.P] (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0)
    (h𝒢 : 𝒢 ≤ mΩ) (hℋ : I.ℋ t ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationOnAt I c r l w t G ca Sn lam Uca)
    (hBo : ∀ ω, IsOpen (H \ I.B t ω))
    (hev : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[I.ℋ t] {ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω})
    (hmm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => ∫ z, stageMean I c r l w t ω z * φ z))
    (hcm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => zeroGFFTestCov (H \ I.B t ω) φ φ))
    (hk : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P 𝒢 ω₀),
      ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      ((condExpKernel c.P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ))
        | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca Sn lam Uca t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ)) :
    StagePhysLawAt I c r l w t :=
  StageInst.stagePhysLawAt_of_stageLaw I hv hpre hu₀ w t hG hlive
    (StageInst.stageLaw_of_kernel_caLaw I hv hpre w t h𝒢 hℋ hshape hdil hBo hev hmm hcm hk) hshape

/-- **`GW2Spm.StagePhysLawAt` from the kernel route and `GW2Smk.StageGeomAt`.** -/
theorem StageInst.stagePhysLawAt_of_kernel_geom [StandardBorelSpace Ω] [IsProbabilityMeasure c.P]
    (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0)
    (h𝒢 : 𝒢 ≤ mΩ) (hℋ : I.ℋ t ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {R : Ω → ℝ≥0 → ℝ} {q : Ω → ℝ≥0}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hgeom : StageGeomAt I c t G ca R q)
    (hBo : ∀ ω, IsOpen (H \ I.B t ω))
    (hev : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[I.ℋ t] {ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω})
    (hmm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => ∫ z, stageMean I c r l w t ω z * φ z))
    (hcm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => zeroGFFTestCov (H \ I.B t ω) φ φ))
    (hk : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P 𝒢 ω₀),
      ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      ((condExpKernel c.P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ))
        | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca (fun ω s => R ω s.toNNReal) (kLam I c ca)
          (kUca I c r l w ca R q) t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ)) :
    StagePhysLawAt I c r l w t :=
  StageInst.stagePhysLawAt_of_kernel I hv hpre hu₀ w t h𝒢 hℋ hG hlive hshape
    (StageInst.stageDilationOnAt_of_geom I hv hpre w t hshape hgeom) hBo hev hmm hcm hk

end InteractingSLE.Theorem14.GW2Ssm
