/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GRecReference
import InteractingSLE.Spec.Sec5.CrossCondThetaMean

/-! # Actual own and counterflow references on the glued coupling space

The θ-dependent word, both smaller local-set means, and their physical
pairings are obtained from the landed coupling theorems. The common harmonic base is restored
explicitly. These supply the two physical reference branches of the patch
constructor, without an assumed smaller-mean pairing identity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Sec5.Aux61GRec
open WangWu LocalSets GlueCond LawUnique Sec4 WholeField Cond44Ref CrossCond.Theta

universe u
variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {Bm : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} [mΩ₂ : MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k]
  {u₀ : ℂ → ℝ}

/-- Both physical reference means on the θ-glued space, with
harmonicity and all test pairings. Infinite own life is the nonboundary
coupling input already returned by UNIONLOC's source construction. -/
theorem exists_physical_references_gluedT
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) u₀) (q s : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
        (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
        (forceJumpFinset xL xR)) u')
    {v : Ω → ℂ → ℝ}
    (hv : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (v ω)) :
    let μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)
    let h₀ := fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))
    ∃ gA gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p => hullAt q (killedHistory W VL VR ζ p.1)) h₀ μ gA ∧
      IsLocalSetMean (fun p => cfHullQ s p.2) h₀ μ gG ∧
      (∀ᵐ p ∂μ,
        InnerProductSpace.HarmonicOnNhd
          (couplingMean κ (fun t : ℝ => W t.toNNReal p.1) q (v p.1))
          (H \ hullAt q (killedHistory W VL VR ζ p.1)) ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ p.1) →
            (gA p + smoothDist upperHalfPlaneOpens u₀) φ =
              ∫ z, couplingMean κ (fun t : ℝ => W t.toNNReal p.1) q (v p.1) z * φ z) ∧
      (∀ᵐ p ∂μ,
        InnerProductSpace.HarmonicOnNhd
          (fun z => cfMeanQ κ
            (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
            (forceJumpFinset xL xR) u' s p.2 z + u₀ z) (H \ cfHullQ s p.2) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ s p.2 →
          (gG p + smoothDist upperHalfPlaneOpens u₀) φ =
            ∫ z, (cfMeanQ κ
              (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
              (forceJumpFinset xL xR) u' s p.2 z + u₀ z) * φ z) := by
  dsimp only
  have hXm := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨gA, hgA, hpA⟩ := exists_isLocalSetMean_flowHull_glueT (θ := θ) (k := k) hC hκ hζ hu₀ q hv
  obtain ⟨gG, hgG, hpG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  have hAh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd
      (couplingMean κ (fun t : ℝ => W t.toNNReal ω) q (v ω))
      (H \ hullAt q (killedHistory W VL VR ζ ω)) := by
    filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hω
    rw [hullAt, Aux50Hit.regHull_stopHistory_cstop hω q]
    exact Sec7.SideHeight.harmonicOnNhd_couplingMean hω.continuous_rpath q.coe_nonneg (hv ω).1
  refine ⟨gA, gG, hgA, hgG, ?_, ?_⟩
  · filter_upwards [hpA, ae_glue_fst (μ := P) k hXm hAh] with p hp hh
    refine ⟨hh, fun φ hφ => ?_⟩
    have hm := hh.sub (hu₀.1.mono sdiff_subset)
    have he := add_base_pairings hm hu₀.1 hp φ hφ
    simpa only [Pi.sub_apply, sub_add_cancel] using he
  · filter_upwards [hpG] with p hp
    have hm := harmonicOnNhd_cfMeanQ κ
      (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
      (forceJumpFinset xL xR) hu'.1 s p.2
    refine ⟨hm.add (hu₀.1.mono sdiff_subset), fun φ hφ => ?_⟩
    exact add_base_pairings hm hu₀.1 hp φ hφ

end InteractingSLE.Sec5.Aux61GRec
