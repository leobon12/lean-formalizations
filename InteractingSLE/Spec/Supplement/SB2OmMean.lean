/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2OmZero

/-!
# SB2(2)'s line mean `hmean` (K2) from the S2 data at the times of positive relative clock

Packet PROVE-GW2-GEOM2, round 9 (PROVE-SB2-LCMEAN's handoff R13.8, item 1). **`hmean_of_stageS2`** is the hypothesis
`hmean` of `Mu.ae_isStopDrvMatch_of_lines` (exact form, angle `ψ = −π/2`), assembled from

* `ae_lineMean_zero` at the samples with `a t = 0` (the retained law and the line family's union locality);
* `ae_lineMean_pos` at the samples with `0 < a t` (Ln's union mean through B's stage chart, the bridge configuration
  from the S2 data `IsStageS2`, the three word identities).

The inputs other than `IsStageS2` are the line family (`Ml.exists_sb2LineFamily_cf`), the version (F2b′), F3 read in
the canonical chart and the retained law (LCMEAN's induction): all owned elsewhere and named in the consumer.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Om

open Restart Exist Exist.StagedLaw Restart.DomainMarkov Supp8.Q3Stop Sec7.PocketTraversal LocalSets Lv Ms

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **SB2(2)'s line mean (K2's `hmean`)** from the S2 data at the samples of positive relative clock: the exact
hypothesis `hmean` of `Mu.ae_isStopDrvMatch_of_lines` at the angle `−π/2`. -/
theorem hmean_of_stageS2 (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L
      relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hA₁m : ∀ t, Measurable[mΩ, hittingSigma] (A₁ t)) (hA₂m : ∀ t, Measurable[mΩ, hittingSigma] (A₂ t))
    (hUm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hd₁ : ∀ t, MeasurableSpace.comap (A₁ t) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hcU : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hl₁ : ∀ t, IsLocalSet (A₁ t) (WholeField.centredField h u₀) P)
    (hl₂ : ∀ t, IsLocalSet (A₂ t) (WholeField.centredField h u₀) P)
    (hlU : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hunb₁ : ∀ t, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ t ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ t ω)) z))
    (hunb₂ : ∀ t, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ t ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ t ω)) z))
    {c : Ω → Chart} {wB : ℝ≥0 → Ω → ℝ → ℝ} {sB : ℝ≥0 → Ω → ℝ} {recB : ℝ≥0 → Ω → RecData}
    {C : ℝ≥0 → Set Ω}
    (hpb : ∀ t, ∀ᵐ ω ∂P, ω ∈ C t → ∃ gb : ℂ → ℂ, Ln.IsStagePullback (c ω) gb (A₁ t ω) (A₂ t ω)
      {z | (c ω).2.1 z ∈ A₁ t ω} (fwdHull (wB t ω) (sB t ω)))
    (hrw : ∀ t, ∀ᵐ ω ∂P, ω ∈ C t → rdrv (recB t ω) = wB t ω)
    (hrt : ∀ t, ∀ᵐ ω ∂P, ω ∈ C t → rtime (recB t ω) = sB t ω)
    (hind₂ : ∀ t, ∀ g₂ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₂ t) (WholeField.centredField h u₀) P g₂ →
      ∃ βB : Ω → BoundaryWord, ∀ᵐ ω ∂P, ω ∈ C t → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t ω → g₂ ω φ = ∫ z, v z * φ z) →
        EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (βB ω, -(Real.pi / 2), recB t ω)).mean
          (fwdMap (wB t ω) (sB t ω) ((c ω).1 z)) -
            chiC κ * ((logDerivFwd (wB t ω) (sB t ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ t ω))
    (hfill : ∀ t, ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ t ω)
    (hF3 : ∀ t, ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ t) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ F → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ t ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z) (fun z => (β₁ ω).mean ((Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z) -
          chiC κ * (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) (H \ A₁ t ω))
    (hlaw : ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω)
      (fun ω' => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω') 1 0 (chiC κ) (h ω'))
      (β₁ ω).fn (β₁ ω).jumps)
    (hC : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ F w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → ω ∈ C t)
    (hS2 : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ F w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
      IsStageS2 (c ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (wB t ω) (sB t ω)
        (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) :
    ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
        ω ∈ seedCell κ (-(Real.pi / 2)) β₁ F w → (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W
              (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w))
              (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  intro g hg m w hw t φ
  have hpos := ae_lineMean_pos hκ hh hu₀ S hKc hKp hsort hA₁m hA₂m hd₁ hl₁ hl₂ hlU hunb₁ hunb₂ hpb hrw hrt hind₂
    hfill hF3 hC hS2 g hg m w hw t
  have hzero := ae_lineMean_zero hκ hh hu₀ S hK hKc hKp hx₀ hβ₁ hF hsort hUm hcU hloc hlaw g hg m w hw t φ
  filter_upwards [hpos, hzero] with ω h1 h2 hcell hlt hdisj
  rcases eq_zero_or_pos ((S.ver m).a t ω) with h0 | h0
  · exact h2 hcell hlt h0
  · exact h1 hcell hlt h0 φ hdisj

end InteractingSLE.Theorem14.SB.Om
