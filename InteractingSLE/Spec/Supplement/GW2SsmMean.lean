/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SmkGeom

/-!
# GW2's stage mean: the canonical stage-chart mean, harmonic at every sample

Packet PROVE-GW2-STAGEMEAN, stage-mean round. `GW2Spm.StagePhysLawAt` lets the physical mean `M` be chosen. This file
chooses it CANONICALLY from the instance's own stage objects (stage chart `cs`, stage driver `S`, flowed typed stage
word `U`, clock `Q`):

`stageMean … ω x = couplingMean κ S Q U (cs.1 x) − u₀ x − σa − kc · cs.2.2 x`.

* the reading clause (G2) holds by definition (`cs.1 ∘ cs.2.1 = id` on `ℍ`);
* **`harmonicOnNhd_stageMean`**: `stageMean` is harmonic on `cs.2.1 '' (ℍ ∖ K^S_Q)` at EVERY sample (the stage chart
  is conformal with a harmonic lift at every sample, `GW2Rd.isMeasChart_stgChart`; the coupling mean is harmonic off
  the hull, `Sec7.SideHeight.harmonicOnNhd_couplingMean`), hence on `ℍ ∖ B t` wherever the stage shape holds;
* **`StageInst.stagePhysLawAt_of_stageLaw`**: `StagePhysLawAt` from (G1) for `stageMean` and the stage shape alone —
  no harmonicity input, no reading input;
* **`law_congr_of_eqOn`** (any measure): the conditional-law statement only reads the mean on `ℍ ∖ B`;
  **`StageInst.ae_eqOn_caMean_stageMean`**: on `ℍ ∖ B t`, `caMean = stageMean` under the dilation data;
* **`StageInst.stagePhysLawAt_of_caLaw`** and **`StageInst.stagePhysLawAt_of_geom_caLaw`**: the law from (G1) for the
  kernel-route mean `caMean`, the stage shape and the dilation data (resp. `GW2Smk.StageGeomAt`), with NO harmonicity
  hypothesis (supersedes the `hMh` binders of `GW2Sdm.stagePhysLawAt_of_dilationOn` and
  `GW2Smk.StageInst.stagePhysLawAt_of_geom_ae`).

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Ssm

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 LocalSets WholeField GW2Spm GW2Sdl
  GW2Sdm GW2Smk

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- The flowed typed stage word's harmonic function at the clock (the `U` of the stage coupling mean). -/
abbrev stageU (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (t : ℝ≥0) (ω : Ω) : ℂ → ℝ :=
  bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
    (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
      (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
    (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
      (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω (I.clock c t ω).toNNReal

/-- **The canonical stage-chart mean** of the centred field at stage time `t`. -/
def stageMean (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (t : ℝ≥0) (ω : Ω) (x : ℂ) : ℝ :=
  couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ) (stageU I c r l w t ω)
      ((I.chart c ω).1 x) - I.u₀ x - I.σa - I.kc * (I.chart c ω).2.2 x

/-- **`stageMean` is harmonic off the stage hull read in the stage chart, at every sample.** -/
theorem harmonicOnNhd_stageMean (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (stageMean I c r l w t ω)
      ((I.chart c ω).2.1 '' (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ))) := by
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  have hcs := hmc.1 ω
  rintro x ⟨z, hz, rfl⟩
  have hdom : (I.chart c ω).2.1 z ∈ (I.chart c ω).dom := hcs.inv_mem_dom hz.1
  have hSc : Continuous fun s : ℝ => I.drv c s.toNNReal ω :=
    (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
  have hf := hcs.differentiableOn_fwd.analyticAt ((I.chart c ω).dom.isOpen.mem_nhds hdom)
  have hU : InnerProductSpace.HarmonicOnNhd (stageU I c r l w t ω) H := (isBoundedHarmonicExtension_bheProc ω _).1
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := c.κ) hSc (NNReal.coe_nonneg _) hU z hz
  rw [← hcs.2.2 z hz.1] at hcm
  have hm := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf hcm
  have harg : InnerProductSpace.HarmonicAt (fun x => I.kc * (I.chart c ω).2.2 x) ((I.chart c ω).2.1 z) := by
    have he : (I.kc • (I.chart c ω).2.2) = (fun x => I.kc * (I.chart c ω).2.2 x) := by
      funext x
      rfl
    simpa only [he] using (hmc.2.2.1 ω _ hdom).const_smul (c := I.kc)
  have hu := hu₀ _ (hcs.2.1 hz.1)
  exact ((hm.sub hu).sub (InnerProductSpace.harmonicAt_const I.σa)).sub harg

/-- **The physical law of a stage at time `t` from (G1) for the canonical stage mean** (no harmonicity, no reading
input): `GW2Spm.StagePhysLawAt` from the conditional law (G1) with mean `stageMean` and the stage shape. -/
theorem StageInst.stagePhysLawAt_of_stageLaw (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0) {G : Set Ω}
    (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, stageMean I c r l w t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ))) :
    StagePhysLawAt I c r l w t := by
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  refine stagePhysLawAt_of_ae_harmonic I w t hG hlive ?_ hlaw ?_
  · filter_upwards [hshape] with ω hsh hωG
    rw [hsh hωG]
    exact harmonicOnNhd_stageMean I hv hpre hu₀ w t ω
  · filter_upwards with ω _ z hz
    rw [stageMean, (hmc.1 ω).2.2 z hz.1]
    ring

/-- **The conditional-law statement only reads the mean off `B`** (any measure). -/
theorem law_congr_of_eqOn {μ : Measure Ω} {ℋ : MeasurableSpace Ω} {Y : Ω → DistOn upperHalfPlaneOpens}
    {B : Ω → Set ℂ} {G : Set Ω} {M M' : Ω → ℂ → ℝ} (heq : ∀ᵐ ω ∂μ, ω ∈ G → EqOn (M ω) (M' ω) (H \ B ω))
    {φ : TestOn upperHalfPlaneOpens} {ρ : ℝ}
    (hlaw : ∀ᵐ ω ∂μ, ω ∈ G → tsupport φ ⊆ H \ B ω →
      (μ[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, M ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ B ω) φ φ)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂μ, ω ∈ G → tsupport φ ⊆ H \ B ω →
      (μ[fun ω' => Complex.exp (Complex.I * ((ρ * Y ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, M' ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ B ω) φ φ)) : ℝ) : ℂ) := by
  filter_upwards [hlaw, heq] with ω h he hωG hsupp
  have hint : ∫ z, M ω z * φ z = ∫ z, M' ω z * φ z := by
    congr 1
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [he hωG (hsupp hz)]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [h hωG hsupp, hint]

/-- **Per sample: the kernel-route mean is the canonical stage mean off `B t`**, under the stage shape and the
dilation data at `ω`. -/
theorem StageInst.eqOn_caMean_stageMean_of (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0)
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ} (ω : Ω)
    (hsh : H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hlam : 0 < lam ω)
    (hch : ∀ x ∈ H \ I.B t ω, (ca ω).1 x = (lam ω : ℂ) * (I.chart c ω).1 x ∧ (ca ω).2.2 x = (I.chart c ω).2.2 x)
    (hS : EqOn (fun s : ℝ => I.drv c s.toNNReal ω) (fun s => Sn ω (lam ω ^ 2 * s) / lam ω)
      (Icc 0 ((I.clock c t ω).toNNReal : ℝ)))
    (hU : EqOn (fun w => Uca ω (lam ω * w)) (stageU I c r l w t ω) H) :
    EqOn (caMean I c ca Sn lam Uca t ω) (stageMean I c r l w t ω) (H \ I.B t ω) := by
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  have hcs := hmc.1 ω
  have hSc : Continuous fun s : ℝ => I.drv c s.toNNReal ω :=
    (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
  intro x hx
  have hx' := hx
  rw [hsh] at hx'
  obtain ⟨z, hz, rfl⟩ := hx'
  have h1 := read_of_dilation_eqOn (κ := c.κ) (σa := I.σa) (kc := I.kc) (u₀ := I.u₀) hcs hlam
    (NNReal.coe_nonneg _) (D := H \ I.B t ω) (fun z hz => by rw [hsh]; exact mem_image_of_mem _ hz)
    (fun x hx => (hch x hx).1) (fun x hx => (hch x hx).2) hS hSc hU z hz
  have h2 : stageMean I c r l w t ω ((I.chart c ω).2.1 z) + I.u₀ ((I.chart c ω).2.1 z) + I.σa +
      I.kc * (I.chart c ω).2.2 ((I.chart c ω).2.1 z) =
        couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)
          (stageU I c r l w t ω) z := by
    rw [stageMean, hcs.2.2 z hz.1]
    ring
  unfold caMean
  linarith

/-- **Almost surely on `G`, the kernel-route mean is the canonical stage mean off `B t`.** -/
theorem StageInst.ae_eqOn_caMean_stageMean (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0) {G : Set Ω}
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationOnAt I c r l w t G ca Sn lam Uca) :
    ∀ᵐ ω ∂c.P, ω ∈ G → EqOn (caMean I c ca Sn lam Uca t ω) (stageMean I c r l w t ω) (H \ I.B t ω) := by
  filter_upwards [hshape, hdil] with ω hsh hd hωG
  obtain ⟨hlam, hch, hS, hU⟩ := hd hωG
  exact StageInst.eqOn_caMean_stageMean_of I hv hpre w t ω (hsh hωG) hlam hch hS hU

/-- **The physical law from (G1) for the kernel-route mean and the dilation data, with no harmonicity input.** -/
theorem StageInst.stagePhysLawAt_of_caLaw (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0) {G : Set Ω}
    (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca Sn lam Uca t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationOnAt I c r l w t G ca Sn lam Uca) :
    StagePhysLawAt I c r l w t :=
  StageInst.stagePhysLawAt_of_stageLaw I hv hpre hu₀ w t hG hlive
    (fun φ ρ => law_congr_of_eqOn (StageInst.ae_eqOn_caMean_stageMean I hv hpre w t hshape hdil) (hlaw φ ρ))
    hshape

/-- **The physical law from (G1) for the kernel-route mean and `GW2Smk.StageGeomAt`, with no harmonicity input.** -/
theorem StageInst.stagePhysLawAt_of_geom_caLaw (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0) {G : Set Ω}
    (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {R : Ω → ℝ≥0 → ℝ} {q : Ω → ℝ≥0}
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca (fun ω s => R ω s.toNNReal) (kLam I c ca)
          (kUca I c r l w ca R q) t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hgeom : StageGeomAt I c t G ca R q) :
    StagePhysLawAt I c r l w t :=
  StageInst.stagePhysLawAt_of_caLaw I hv hpre hu₀ w t hG hlive hlaw hshape
    (StageInst.stageDilationOnAt_of_geom I hv hpre w t hshape hgeom)

end InteractingSLE.Theorem14.GW2Ssm
