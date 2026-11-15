/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CiK2
import InteractingSLE.Spec.Supplement.SB2OmMean

/-!
# GEOM2's line mean from the S2 record, over NOJUMP's version structures

Packet PROVE-SB2-CONDFIN (round 3, D39). GEOM2's `Om.ae_lineMean_pos`, `Om.ae_lineMean_zero` and
`Om.hmean_of_stageS2`, verbatim, over `Na.StageVersionS` (no proof reads `trace`). Generated from the landed originals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Ci

open Om hiding ae_lineMean_pos ae_lineMean_zero hmean_of_stageS2

section Line
open Restart Exist Exist.StagedLaw Restart.DomainMarkov Supp8.Q3Stop Sec7.PocketTraversal LocalSets Lv Ms
open Supp8.Q3Chain (flowedData flowedJumps)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

omit [StandardBorelSpace Ω] in
/-- **The line mean at the times of positive relative clock** (K2's `hmean` equation on
`seedCell ∩ {0 < a t < Λ}`), from the line family's union-mean inputs, the stage pull-back and explored mean through
B's stage chart, the version, F3 read in the canonical chart and the S2 data at each sample. -/
theorem ae_lineMean_pos (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L
      relLife)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hA₁m : ∀ t, Measurable[mΩ, hittingSigma] (A₁ t)) (hA₂m : ∀ t, Measurable[mΩ, hittingSigma] (A₂ t))
    (hd₁ : ∀ t, MeasurableSpace.comap (A₁ t) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hl₁ : ∀ t, IsLocalSet (A₁ t) (WholeField.centredField h u₀) P)
    (hl₂ : ∀ t, IsLocalSet (A₂ t) (WholeField.centredField h u₀) P)
    (hlU : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
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
    (hC : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ F w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → ω ∈ C t)
    (hS2 : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ F w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
      IsStageS2 (c ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (wB t ω) (sB t ω)
        (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal)
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t))
    (m : ℕ) (w : WordType) (hw : w ∈ types) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ F w → (S.ver m).a t ω < (S.ver m).Λ w ω →
      0 < (S.ver m).a t ω → ∀ φ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w))
            (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hA₁m t) (hl₁ t)
  obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hA₂m t) (hl₂ t)
  obtain ⟨βB, hβB⟩ := hind₂ t g₂ hg₂
  set D : Set Ω := seedCell κ (-(Real.pi / 2)) β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
    {ω | 0 < (S.ver m).a t ω} with hD
  have hΦc : ∀ ω, (Mo.hullChart (fillH (K ω)) (x₀ ω)).IsConformal := Mu.isConformal_canon x₀ hKc hKp
  have hΦℓ : ∀ ω, ContinuousOn (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2
      (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom := fun ω =>
    Mo.continuousOn_lift_hullChart (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω)
  have hDF : ∀ ω ∈ D, ω ∈ F := fun ω hω => hω.1.1.1.1
  -- the hypotheses of the record lemma on `D`
  have hpb' : ∀ᵐ ω ∂P, ω ∈ D → ∃ gb : ℂ → ℂ, Ln.IsStagePullback (c ω) gb (A₁ t ω) (A₂ t ω)
      {z | (c ω).2.1 z ∈ A₁ t ω} (fwdHull (wB t ω) (sB t ω)) := by
    filter_upwards [hpb t, hC m w hw t] with ω h1 h2 hωD
    exact h1 (h2 hωD.1.1 hωD.1.2)
  have hdom : ∀ᵐ ω ∂P, ω ∈ D → ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) = H \ A₁ t ω := by
    filter_upwards [hfill t] with ω h1 hωD
    rw [← h1 (hDF ω hωD)]
    exact Mo.coe_dom_hullChart (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω)
  have hrec : ∀ᵐ ω ∂P, ω ∈ D → ∃ d, IsCfg κ (-(Real.pi / 2)) (c ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω)
      (wB t ω) (sB t ω)
      (fun s : ℝ => (S.ver m).W s.toNNReal ω) (((S.ver m).a t ω).toNNReal : ℝ) (β₁ ω)
      (fun z => (stopWord κ (βB ω, (-(Real.pi / 2)), recB t ω)).mean z)
      (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w))
        (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w)) ω ((S.ver m).a t ω).toNNReal) d := by
    filter_upwards [hS2 m w hw t, hC m w hw t, hrw t, hrt t] with ω h2 hCω hrwω hrtω hωD
    have hS := h2 hωD.1.1 hωD.1.2 hωD.2
    have hCt := hCω hωD.1.1 hωD.1.2
    have hcell : ω ∈ wordTypeCell κ (-(Real.pi / 2)) β₁ F w := hωD.1.1.1
    have hxL := (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := (-(Real.pi / 2))) (nL := w.1) (nR := w.2.1)
      (ρL := typedRhoL w) (ρR := typedRhoR w) (β₁ ω)).2.1
    have hxR := (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := (-(Real.pi / 2))) (nL := w.1) (nR := w.2.1)
      (ρL := typedRhoL w) (ρR := typedRhoR w) (β₁ ω)).2.2.2
    have hFO := Theorem15.isOrderedForceWord_flowLine (βB ω).fn (βB ω).jumps 0
    refine exists_isCfg_of_stageS2 hS (ρL := typedRhoL w) (ρR := typedRhoR w) (xL := cellXL κ (-(Real.pi / 2)) β₁ w ω)
      (xR := cellXR κ (-(Real.pi / 2)) β₁ w ω) (ρL' := flowLineRhoL κ (βB ω).fn (βB ω).jumps 0 (-(Real.pi / 2)))
      (ρR' := flowLineRhoR κ (βB ω).fn (βB ω).jumps 0 (-(Real.pi / 2))) (xL' := flowLineXL (βB ω).fn (βB ω).jumps 0)
      (xR' := flowLineXR (βB ω).fn (βB ω).jumps 0) hxL hxR hFO.2.1 hFO.2.2.2
      (fun G hG => eqOn_typed_mean hκ hcell (hsort ω) hG) (fun G hG => ?_) (fun G hG => ?_)
    · rw [← hrwω hCt, ← hrtω hCt] at hG
      exact eqOn_explored_mean (βB ω) (recB t ω) hG
    · exact Lv.eqOn_bheProc_of_flowedData (typedRhoL w) (typedRhoR w) (S.ver m).W_cont (S.ver m).W_zero hxL hxR
        (((S.ver m).W_cont ω).comp continuous_real_toNNReal) (by simp [(S.ver m).W_zero ω])
        (fun r _ => rfl) hG
  have hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ t ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ t ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => (β₁ ω).mean ((Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z) -
        chiC κ * (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) (H \ A₁ t ω) := by
    filter_upwards [hF3 t g₁ hg₁] with ω h1 hωD
    exact h1 (hDF ω hωD)
  have hind₂' : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ t ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => (fun z => (stopWord κ (βB ω, (-(Real.pi / 2)), recB t ω)).mean z)
        (fwdMap (wB t ω) (sB t ω) ((c ω).1 z)) -
          chiC κ * ((logDerivFwd (wB t ω) (sB t ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ t ω) := by
    filter_upwards [hβB, hC m w hw t] with ω h1 h2 hωD
    exact h1 (h2 hωD.1.1 hωD.1.2)
  have hmain := ae_chartTransport_eq_of_cfg (κ := κ) (ψ := (-(Real.pi / 2))) hh0 hu₀.1 hu₀.2.1 (hA₁m t) (hA₂m t)
    (hd₁ t) (hl₁ t) (hl₂ t) (hlU t) (hunb₁ t) (hunb₂ t) (hg t) hg₁ hg₂ (c := c) (wB := wB t) (sB := sB t)
    (D := D) hpb' hΦc hΦℓ hdom hrec hind₁ hind₂'
  filter_upwards [hmain] with ω hω hcell hlt hpos φ hφ
  have hωD : ω ∈ D := ⟨⟨hcell, hlt⟩, hpos⟩
  have e : h ω - WholeField.centredField h u₀ ω = smoothDist upperHalfPlaneOpens u₀ := by
    simp only [WholeField.centredField, sub_sub_cancel]
  rw [e]
  exact hω hωD φ hφ

end Line

section Zero
open Restart Exist Exist.StagedLaw Restart.DomainMarkov Supp8.Q3Stop Sec7.PocketTraversal LocalSets Lv Ms

section Zero

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **The line mean at the times of zero relative clock** (K2's `hmean` equation on
`seedCell ∩ {a t < Λ} ∩ {a t = 0}`): from the line family's union locality (marks `𝓖 t`), the version's hull clause
and the retained law of the canonical chart field given `lineFiltC 𝓖 0` (the word `β₁`). -/
theorem ae_lineMean_zero {ψ : ℝ} (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hUm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hcU : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hlaw : ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω)
      (fun ω' => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω') 1 0 (chiC κ) (h ω'))
      (β₁ ω).fn (β₁ ω).jumps)
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t))
    (m : ℕ) (w : WordType) (hw : w ∈ types) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → (S.ver m).a t ω < (S.ver m).Λ w ω → (S.ver m).a t ω = 0 →
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ β₁ w))
            (geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hΦ : ∀ ω, (Mo.hullChart (fillH (K ω)) (x₀ ω)).IsConformal := Mu.isConformal_canon x₀ hKc hKp
  obtain ⟨-, hliftc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hK hKc hKp hx₀
  -- the σ-algebras: `lineFiltC 0 ≤ lineFiltC t ≤ germ ⊔ lineFiltC t`
  have h01 : lineFiltC P 𝓖 0 ≤ lineFiltC P 𝓖 t := (lineFiltC P 𝓖).mono (zero_le (a := t))
  have hm : lineFiltC P 𝓖 0 ≤
      germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t :=
    h01.trans le_sup_right
  have hm₁ : lineFiltC P 𝓖 t ≤ mΩ := (lineFiltC P 𝓖).le t
  have hm'Ω : germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t ≤ mΩ :=
    sup_le (germSigma_le (hUm t) hh0.measurable) hm₁
  have hloc₁ : WholeField.IsHistoryAvoidanceLocal (lineFiltC P 𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P := Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma (hloc t)
  -- the event
  have hE₀m : MeasurableSet[germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔
      lineFiltC P 𝓖 t] (seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
        {ω | (S.ver m).a t ω = 0}) := by
    have h1 : MeasurableSet[lineFiltC P 𝓖 0] (seedCell κ ψ β₁ F w) := measurableSet_seedCell hβ₁ hF w
    have h2 : MeasurableSet[lineFiltC P 𝓖 t] {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} := by
      have := (S.ver m).safeS w hw 0 t
      have e : {ω | (S.ver m).a t ω < (S.ver m).Λ w ω ∧ Disjoint (tsupport ⇑(0 : TestOn upperHalfPlaneOpens))
          (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal)} =
          {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} := by
        ext ω
        simp only [mem_ofPred_eq, and_iff_left_iff_imp]
        intro _
        have e0 : tsupport ⇑(0 : TestOn upperHalfPlaneOpens) = ∅ := by
          rw [show ⇑(0 : TestOn upperHalfPlaneOpens) = (0 : ℂ → ℝ) from rfl, tsupport_zero]
        rw [e0]
        exact Set.empty_disjoint _
      rwa [e] at this
    have h3 : MeasurableSet[lineFiltC P 𝓖 t] {ω | (S.ver m).a t ω = 0} :=
      ((S.ver m).clock_meas t) (measurableSet_singleton 0)
    exact ((hm _ h1).inter (le_sup_right (a := germSigma _ _) _ h2)).inter (le_sup_right (a := germSigma _ _) _ h3)
  -- the union's kernel given its germ and the completed marks at `t`
  have hker : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ' : ℂ)) |
        germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + smoothDist upperHalfPlaneOpens u₀) φ' : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (H \ (A₁ t ω ∪ A₂ t ω)) φ' φ' : ℝ) : ℂ)) := fun φ' =>
    GW4Fix.ae_condExp_cexp_boundary_marked hu₀.1 hh0 (hUm t) (hcU t) hm₁ hloc₁ (hg t) φ'
  -- on `{a t = 0}` the union's complement is the chart domain
  have hcomp : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
      {ω | (S.ver m).a t ω = 0} →
      H \ (A₁ t ω ∪ A₂ t ω) = ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) := by
    filter_upwards [(S.ver m).hull w hw t] with ω hω hE
    have h0 : (S.ver m).a t ω = 0 := hE.2
    have hc : Continuous fun s : ℝ => (S.ver m).W s.toNNReal ω :=
      ((S.ver m).W_cont ω).comp continuous_real_toNNReal
    rw [hω hE.1.1 hE.1.2, h0, ENNReal.toNNReal_zero, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hc,
      sdiff_empty, (hΦ ω).coe_dom]
  have hcond : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩ {ω | (S.ver m).a t ω = 0} →
      tsupport φ' ⊆ (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ' : ℂ)) |
        germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + smoothDist upperHalfPlaneOpens u₀) φ' : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) φ' φ' : ℝ) : ℂ)) := by
    intro φ'
    filter_upwards [hker φ', hcomp] with ω h1 h2 hE _
    rw [h1, h2 hE]
  -- the chart field's conditional law on the event, given the finer σ-algebra
  have hR1 := fun ψ' => Restart.ae_condExp_cexp_chartTransport_random_on (P := P) hm'Ω hΦ
    (fun z => hm _ (hdom z)) (fun z => (hfwd z).mono hm le_rfl) (fun z => (hliftm z).mono hm le_rfl) hliftc
    hh.1 (chiC κ) hE₀m (M := fun ω => g t ω + smoothDist upperHalfPlaneOpens u₀) hcond ψ'
  -- the measurability inputs
  have hm₀Ω : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hY : Measurable fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' hΦ (fun z => hm₀Ω _ (hdom z)) (fun z => (hfwd z).mono hm₀Ω le_rfl)
      (fun z => (hliftm z).mono hm₀Ω le_rfl) hliftc hh.1 1 0 (chiC κ)
  have hgm : Measurable[germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔
      lineFiltC P 𝓖 t] fun ω => g t ω + smoothDist upperHalfPlaneOpens u₀ := by
    exact (WholeField.measurable_add_dist _).comp ((hg t).1.mono le_sup_left le_rfl)
  have hM' : ∀ ψ' : TestOn upperHalfPlaneOpens, Measurable[germSigma (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t]
      fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (g t ω + smoothDist upperHalfPlaneOpens u₀) ψ' := fun ψ' =>
    (LQGMetric.measurable_distOn_apply ψ').comp (@Chart.measurable_chartTransport_random' Ω
      (germSigma (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t) _ hΦ
      (fun z => hm _ (hdom z)) (fun z => (hfwd z).mono hm le_rfl) (fun z => (hliftm z).mono hm le_rfl) hliftc
      _ hgm 1 0 (chiC κ))
  have hc : ∀ ψ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ F →
      P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hΦ ω') 1 0 (chiC κ) (h ω') ψ' : ℂ)) |
        lineFiltC P 𝓖 0] ω = gaussCF (β₁ ω) ψ' := by
    intro ψ'
    have hXm : Measurable fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (h ω) ψ' :=
      (LQGMetric.measurable_distOn_apply ψ').comp hY
    filter_upwards [hlaw, condExp_ae_eq_integral_condExpKernel hm₀Ω (GFF.integrable_exp_I_mul (P := P) hXm)]
      with ω h1 h2 hωF
    rw [h2]
    exact Exist.StagedLaw.integral_cexp_eq_gaussCF (hsort ω) (h1 hωF) ψ'
  have hGL : seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩ {ω | (S.ver m).a t ω = 0} ⊆ F :=
    fun ω hω => hω.1.1.1.1
  have hpair := ae_pairing_eq_of_le_on hm hm'Ω hY hβ₁ hM' hF hE₀m hGL hc hR1 φ
  -- the equation
  filter_upwards [hpair] with ω hω hcell hlt h0
  have hωE : ω ∈ seedCell κ ψ β₁ F w ∩ {ω | (S.ver m).a t ω < (S.ver m).Λ w ω} ∩
      {ω | (S.ver m).a t ω = 0} := ⟨⟨hcell, hlt⟩, h0⟩
  have e : h ω - WholeField.centredField h u₀ ω = smoothDist upperHalfPlaneOpens u₀ := by
    simp only [WholeField.centredField, sub_sub_cancel]
  rw [e]
  have e1 : Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
      (g t ω + smoothDist upperHalfPlaneOpens u₀) φ =
      Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (g t ω + smoothDist upperHalfPlaneOpens u₀) φ +
        ψ * chiC κ * ∫ z, φ z := by
    rw [Chart.chartTransport_apply', Chart.chartTransport_apply', Chart.oneDist_apply]
    ring
  rw [e1, hω hωE, h0, ENNReal.toNNReal_zero, NNReal.coe_zero]
  -- the coupling mean at time `0`
  have hW0 : (fun s : ℝ => (S.ver m).W s.toNNReal ω) 0 = 0 := by simp [(S.ver m).W_zero ω]
  have hxL := (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := ψ) (nL := w.1) (nR := w.2.1)
    (ρL := typedRhoL w) (ρR := typedRhoR w) (β₁ ω)).2.1
  have hxR := (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := ψ) (nL := w.1) (nR := w.2.1)
    (ρL := typedRhoL w) (ρR := typedRhoR w) (β₁ ω)).2.2.2
  have hbhe := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := typedRhoL w) (ρR := typedRhoR w)
    (W := (S.ver m).W) (VL := geomLW (S.ver m).W (cellXL κ ψ β₁ w))
    (VR := geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω 0
  have eL : (fun i => geomLW (S.ver m).W (cellXL κ ψ β₁ w) i 0 ω - (S.ver m).W 0 ω) = cellXL κ ψ β₁ w ω := by
    funext i
    rw [geomLW_zero (S.ver m).W_cont (S.ver m).W_zero (hxL i), (S.ver m).W_zero ω, sub_zero]
  have eR : (fun j => geomRW (S.ver m).W (cellXR κ ψ β₁ w) j 0 ω - (S.ver m).W 0 ω) = cellXR κ ψ β₁ w ω := by
    funext j
    rw [geomRW_zero (S.ver m).W_cont (S.ver m).W_zero (hxR j), (S.ver m).W_zero ω, sub_zero]
  rw [eL, eR] at hbhe
  have hmean := eqOn_typed_mean hκ hcell.1 (hsort ω) hbhe
  have hcont : ContinuousOn (β₁ ω).mean H :=
    Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (BoundaryWord.isBoundedHarmonicExtension_mean _ (hsort ω)).1
  have hi₁ : Integrable fun z => (β₁ ω).mean z * φ z := integrable_mul_testOn_of_continuousOn hcont φ
  have hi₂ : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hRHS : ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((0 : ℝ≥0) : ℝ)
      (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ β₁ w))
        (geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω 0) z * φ z =
      ∫ z, ((β₁ ω).mean z * φ z + ψ * chiC κ * φ z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · have hzH : z ∈ H := φ.tsupport_subset hz
      have hz0 : z ≠ 0 := fun h' => by rw [h'] at hzH; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
      show couplingMean κ _ ((0 : ℝ≥0) : ℝ) _ z * φ z = _
      rw [NNReal.coe_zero, Coupling.MartMeans2.couplingMean_zero κ hW0 _ hz0, hmean hzH]
      ring
    · show _ * φ z = (β₁ ω).mean z * φ z + ψ * chiC κ * φ z
      rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  rw [NNReal.coe_zero] at hRHS
  rw [hRHS, integral_add hi₁ (hi₂.const_mul _), integral_const_mul]

end Zero

end Zero

section Mean
open Restart Exist Exist.StagedLaw Restart.DomainMarkov Supp8.Q3Stop Sec7.PocketTraversal LocalSets Lv Ms

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **SB2(2)'s line mean (K2's `hmean`)** from the S2 data at the samples of positive relative clock: the exact
hypothesis `hmean` of `Mu.ae_isStopDrvMatch_of_lines` at the angle `−π/2`. -/
theorem hmean_of_stageS2 (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L
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
  have hpos := Ci.ae_lineMean_pos hκ hh hu₀ S hKc hKp hsort hA₁m hA₂m hd₁ hl₁ hl₂ hlU hunb₁ hunb₂ hpb hrw hrt hind₂
    hfill hF3 hC hS2 g hg m w hw t
  have hzero := Ci.ae_lineMean_zero hκ hh hu₀ S hK hKc hKp hx₀ hβ₁ hF hsort hUm hcU hloc hlaw g hg m w hw t φ
  filter_upwards [hpos, hzero] with ω h1 h2 hcell hlt hdisj
  rcases eq_zero_or_pos ((S.ver m).a t ω) with h0 | h0
  · exact h2 hcell hlt h0
  · exact h1 hcell hlt h0 φ hdisj

end Mean

end InteractingSLE.Theorem14.SB.Ci
