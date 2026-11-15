/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrVer
import InteractingSLE.Spec.Supplement.SB2CiMean

/-!
# The root's line mean at positive relative clock, in B's own time

Packet PROVE-SB2-CONDFIN (round 8, D44). GEOM2's `Om.ae_lineMean_pos` as retyped in `Ci.ae_lineMean_pos`, over the
root's versions `Cr.RootVersionS` with the live event the root event. The proof reads only the version's clock,
driver and lifetime (`a`, `W`, `W_cont`, `W_zero`, `Λ`), which `Cr.RootVersionG` has verbatim. Generated from the
landed `SB2CiMean` (the theorem's text with the structure renamed); with B's own-time line family (LCMEAN's tail
family at `ℓ = relOff`) the line sets' inputs are the tails'.

* **`ae_lineMean_pos_root`**.
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

namespace InteractingSLE.Theorem14.SB.Cr

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
theorem ae_lineMean_pos_root (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : RootVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L
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

end InteractingSLE.Theorem14.SB.Cr
