/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedTheta

/-!
# Proposition 5.9, S2: the union mean has the flow side's boundary values (the source of `hFl`)

Packet PROVE-STAGED6 (S2 on the glued space, PROVE-STAGED5 §5.1 item 2, PROVE-CROSSCOND-STAGED4 §5.1 item 2;
R71 Part (3) §3.1, "an additional disjoint reveal preserves the switch-point data"). On the θ-glued space of the
field and the counterflow of `h − θχ`, let the flow side be an arbitrary recorded local set `𝔄 (Yf ω)` (for
Proposition 5.9: the
staged prefix hull `StagedGlue.recHull s n (pastMap … (n+1) ω)`, PROVE-STAGED5's `exists_flowSide_schedule`), with a
harmonic representative `wA` of its own local-set mean (for the staged prefix: `stageMeanW − 𝔥₀`,
PROVE-CROSSCOND-STAGED4's `exists_rep_stageMeanW`). Then almost surely the local-set mean of the union with the
counterflow hull `G_s` has a harmonic representative `w` with

* `w − wA → 0` at every point of `𝔄 (Yf ω) ∪ ℝ` near which `G_s` lies inside the flow side (Proposition 3.8 for the
  flow side; this is the hypothesis `hFl` of `StagedFinal.eqOn_imgChart_pastWord` at the prefix points away from the
  counterflow hull),
* `w − cfMeanQ → 0` at every point of `G_s ∪ ℝ` near which the flow side lies inside `G_s` (the counterflow side,
  `hwG` of the θ-template).

Main result: **`ae_union_mean_cfGlueT_flowSide`** (the θ-template `Theta.ae_union_mean_cfGlueT` with the flow hull
`hullAt q (killedHistory …)` replaced by an arbitrary recorded flow-side local set).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedAdapt

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets Theta

section Union

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {γ : Type*} [mγ : MeasurableSpace γ] {Yf : Ω → γ} {𝔄 : γ → Set ℂ}

/-- **The union mean on the θ-glued space for an arbitrary recorded flow side** (θ-template
`Theta.ae_union_mean_cfGlueT` with the flow hull replaced by `𝔄 ∘ Yf`): if `𝔄 ∘ Yf` is a local set of the centred
field on `(Ω, P)` whose lower union has no bounded component, and `wA` represents its own local-set mean `gA`
almost surely, then almost surely on the glued space the local-set mean `g` of `𝔄 (Yf p.1) ∪ G_s` has a harmonic
representative `w` with `w − wA → 0` at the points of `𝔄 (Yf p.1) ∪ ℝ` near which `G_s` lies inside the flow side,
and `w − cfMeanQ → 0` at the points of `G_s ∪ ℝ` near which the flow side lies inside `G_s`. -/
theorem ae_union_mean_cfGlueT_flowSide (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hYf : Measurable Yf) (h𝔄 : Measurable[mγ, hittingSigma] 𝔄)
    (hAl : IsLocalSet (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (𝔄 (Yf ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (𝔄 (Yf ω))) z))
    {gA : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P gA)
    {wA : Ω → ℂ → ℝ} (hwA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (wA ω) (H \ 𝔄 (Yf ω)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ 𝔄 (Yf ω) → gA ω φ = ∫ z, wA ω z * φ z)
    (s : ℝ≥0) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    {g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1) ∪ cfHullQ s p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (𝔄 (Yf p.1) ∪ cfHullQ s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (𝔄 (Yf p.1) ∪ cfHullQ s p.2) → g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ 𝔄 (Yf p.1) ∪ {z : ℂ | z.im = 0}, (∃ r > 0, cfHullQ s p.2 ∩ ball z₀ r ⊆ 𝔄 (Yf p.1)) →
          Tendsto (fun z => w z - wA p.1 z) (𝓝[H \ (𝔄 (Yf p.1) ∪ cfHullQ s p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ s p.2 ∪ {z : ℂ | z.im = 0}, (∃ r > 0, 𝔄 (Yf p.1) ∩ ball z₀ r ⊆ cfHullQ s p.2) →
          Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
              (forceJumpFinset xL xR) u' s p.2 z)
            (𝓝[H \ (𝔄 (Yf p.1) ∪ cfHullQ s p.2)] z₀) (𝓝 0)) := by
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hAm : Measurable[mΩ, hittingSigma] fun ω => 𝔄 (Yf ω) := h𝔄.comp hYf
  have hAg := IsLocalSet.glue_fst hXm₀ k (T := cenTT κ θ u₀) hAl
  have hGg := IsLocalSet.glue_snd hXm₀ k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenTT κ θ u₀) (measurable_cfHullQ s) MeasurableSet.univ (fun y _ => cfHullQ_relClosed s y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenTT hcf hreg₂ hu₀.1 s)
  have hgA' := IsLocalSetMean.comp measurable_fst (glueMeasure_fst (μ := P) k hXm₀) hAm
    ((measurable_cenTT κ θ u₀).comp hXm₀) hgA
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  have hbd := ae_union_boundary_glue hXm₀ k (measurable_cenTT κ θ u₀) (measurable_cenTT' κ θ u₀)
    (cenTT'_cenTT κ θ u₀) hF hAm (measurable_cfHullQ s) hAg hGg (ae_glue_fst (μ := P) k hXm₀ hunb)
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_image_negInv (isHPHull_hullAt _ _)) hg hgA' hgG
  filter_upwards [hbd, ae_glue_fst (μ := P) k hXm₀ hwA, hidG] with p hp hwAp hidGp
  exact hp (wA p.1) _ hwAp.1 hwAp.2 (harmonicOnNhd_cfMeanQ _ _ _ hu'.1 s p.2) hidGp

end Union

end InteractingSLE.Sec5.CrossCond.StagedAdapt
