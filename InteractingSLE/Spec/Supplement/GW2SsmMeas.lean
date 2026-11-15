/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SsmKernel

/-!
# GW2's stage mean: the stage event and the covariance are measurable for the marks

Packet PROVE-GW2-STAGEMEAN, stage-mean round. `GW2Ssm.StageInst.stagePhysLawAt_of_kernel` takes the `ℋ t`-measurability
of the stage event `{ω ∈ G, supp φ ⊆ ℍ ∖ B t}` and of the covariance `ω ↦ Cov_{ℍ∖B t}(φ, φ)`. Both follow from the
`ℋ t`-hitting-measurability of the stage union `B t` (RELDET's `hBℋ`):

* `measurableSet_compact_subset_H_diff`: for a compact `K ⊆ ℍ`, `{ω | K ⊆ ℍ ∖ A ω}` is measurable (the argument of
  `GW2Spm.measurableSet_tsupport_subset_H_diff`, for any compact subset of `ℍ`);
* **`measurable_zeroGFFTestCov_of_hitting`** (`QuantumZipper.K3.measurable_zeroGFFTestCov` with the test family);
* **`StageInst.stagePhysLawAt_of_kernel_hit`**: `StagePhysLawAt` from the kernel route with `hBℋ` and the shape of
  `B t` in place of the event and covariance inputs; the only measurability input left is the stage-mean pairing
  `ω ↦ ∫ stageMean ω z φ z` restricted to the stage event.

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Ssm

open LocalSets

/-- **Avoidance of a compact subset of `ℍ` is measurable** for a hitting-measurable random set with open
complement in `ℍ`. -/
theorem measurableSet_compact_subset_H_diff {Ω : Type*} {m : MeasurableSpace Ω} {A : Ω → Set ℂ}
    (hA : Measurable[m, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) : MeasurableSet[m] {ω | K ⊆ H \ A ω} := by
  set U : ℕ → Set ℂ := fun n => thickening (1 / ((n : ℝ) + 1)) K ∩ H with hUdef
  have hUo : ∀ n, IsOpen (U n) := fun n => isOpen_thickening.inter QuantumZipper.isOpen_H
  have e : {ω | K ⊆ H \ A ω} = ⋃ n, A ⁻¹' {S : Set ℂ | Disjoint S (U n)} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open (hAc ω).2 hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      refine mem_iUnion.2 ⟨n, ?_⟩
      change Disjoint (A ω) (U n)
      rw [Set.disjoint_left]
      intro z hzA hzU
      exact (hsub (thickening_mono hn.le K hzU.1)).2 hzA
    · intro hω
      obtain ⟨n, hn⟩ := mem_iUnion.1 hω
      intro z hz
      refine ⟨hKH hz, fun hzA => ?_⟩
      have hzU : z ∈ U n := ⟨self_subset_thickening (by positivity) K hz, hKH hz⟩
      exact Set.disjoint_left.1 hn hzA hzU
  rw [e]
  exact MeasurableSet.iUnion fun n => hA (measurableSet_avoid (hUo n) inter_subset_right)

/-- **The covariance off a hitting-measurable random set is measurable.** -/
theorem measurable_zeroGFFTestCov_of_hitting {Ω : Type*} {m : MeasurableSpace Ω} {A : Ω → Set ℂ}
    (hA : Measurable[m, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens) :
    Measurable[m] fun ω => zeroGFFTestCov (H \ A ω) φ φ := by
  have hE : ∀ j, MeasurableSet[m] {ω | tsupport (QuantumZipper.K3.testFamily j) ⊆ H \ A ω} := fun j => by
    have hj := QuantumZipper.K3.testFamily_mem j
    exact measurableSet_compact_subset_H_diff hA hAc hj.2.1.isCompact hj.2.2
  exact @QuantumZipper.K3.measurable_zeroGFFTestCov Ω m (fun ω => H \ A ω) (fun ω => ⟨(hAc ω).2, sdiff_subset⟩) hE
    (toTestFunH φ) (toTestFunH φ)

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 WholeField GW2Spm GW2Sdl GW2Sdm GW2Smk

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {c : SourceData Ω}
  {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}

/-- **`GW2Spm.StagePhysLawAt` from the kernel route, with the stage union hitting-measurable for the marks.** -/
theorem StageInst.stagePhysLawAt_of_kernel_hit [StandardBorelSpace Ω] [IsProbabilityMeasure c.P] (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0)
    (h𝒢 : 𝒢 ≤ mΩ) (hℋ : I.ℋ t ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationOnAt I c r l w t G ca Sn lam Uca)
    (hBℋ : Measurable[I.ℋ t, hittingSigma] (I.B t)) (hBc : ∀ ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hmm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => ∫ z, stageMean I c r l w t ω z * φ z))
    (hk : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P 𝒢 ω₀),
      ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      ((condExpKernel c.P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ))
        | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca Sn lam Uca t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ)) :
    StagePhysLawAt I c r l w t :=
  StageInst.stagePhysLawAt_of_kernel I hv hpre hu₀ w t h𝒢 hℋ hG hlive hshape hdil (fun ω => (hBc ω).2)
    (fun φ => hG.inter (measurableSet_compact_subset_H_diff hBℋ hBc φ.hasCompactSupport.isCompact
      (Coupling.tsupport_subset_H φ)))
    hmm (fun φ => (measurable_zeroGFFTestCov_of_hitting hBℋ hBc φ).indicator
      (hG.inter (measurableSet_compact_subset_H_diff hBℋ hBc φ.hasCompactSupport.isCompact
        (Coupling.tsupport_subset_H φ)))) hk

/-- **`GW2Spm.StagePhysLawAt` from the kernel route and `GW2Smk.StageGeomAt`, with the stage union
hitting-measurable for the marks.** -/
theorem StageInst.stagePhysLawAt_of_kernel_geom_hit [StandardBorelSpace Ω] [IsProbabilityMeasure c.P]
    (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H) (w : WordType) (t : ℝ≥0)
    (h𝒢 : 𝒢 ≤ mΩ) (hℋ : I.ℋ t ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {R : Ω → ℝ≥0 → ℝ} {q : Ω → ℝ≥0}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hgeom : StageGeomAt I c t G ca R q)
    (hBℋ : Measurable[I.ℋ t, hittingSigma] (I.B t)) (hBc : ∀ ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hmm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[I.ℋ t] ({ω | ω ∈ G ∧ tsupport φ ⊆ H \ I.B t ω}.indicator
      fun ω => ∫ z, stageMean I c r l w t ω z * φ z))
    (hk : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P 𝒢 ω₀),
      ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      ((condExpKernel c.P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ))
        | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca (fun ω s => R ω s.toNNReal) (kLam I c ca)
          (kUca I c r l w ca R q) t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ)) :
    StagePhysLawAt I c r l w t :=
  StageInst.stagePhysLawAt_of_kernel_hit I hv hpre hu₀ w t h𝒢 hℋ hG hlive hshape
    (StageInst.stageDilationOnAt_of_geom I hv hpre w t hshape hgeom) hBℋ hBc hmm hk

end InteractingSLE.Theorem14.GW2Ssm
