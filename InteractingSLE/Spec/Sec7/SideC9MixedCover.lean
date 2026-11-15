/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC9IncomingOwn
import InteractingSLE.Spec.Sec7.R5SameCover

/-!
# A mixed incoming-wall and exposed-hull reference cover

PROVE-SIDE-COLLAR2. R5-SAMETIME supplies the exposed-hull heights. The
incoming-wall heights follow from the initial mean and the landed
arbitrary-version transport. The remaining two cover hypotheses are
purely pathwise; no positive reference mean height is an input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Current.SideTest LocalSets WholeField Sec7 Sec7.PocketStopSide
  Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C Sec7.PocketStopWallsFin Sec7.Aux119Heights

/-- The unproved incoming-wall access selection: each relevant access
landing outside the open pocket has a surviving initial real coordinate
and an earlier visit reference. This names only pathwise geometry and
jump exclusions, not a local-mean height or an increment law. -/
def VisitReferenceIncomingAccessCoverPosExc {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → ∀ ξ : ℝ,
      ξ ∉ (j.target i d).jumps q ω →
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉
        X j q ω →
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉
        (j.target i d).domain ω →
      ∃ (r : ℕ) (W : ℝ → ℝ) (q' x : ℝ) (a : ℝ → ℂ),
        d.curve ω (s j r) ∈ (j.target i d).domain ω ∧
        (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧
        Continuous W ∧ W 0 = 0 ∧ (q : ℝ) < q' ∧
        EqOn (fun t : ℝ => segDriver ((j.target i d).curve ω) t.toNNReal) W (Icc 0 q') ∧
        QuantumZipper.IsForwardSol W x q a ∧ (a q).re = ξ ∧
        x ∉ forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω) ∧
        x ∉ (j.target i d).jumps 0 ω ∧
        (a (j.visitCapacity d ω (s j r)).toNNReal).re ∉
          (j.target i d).jumps (j.visitCapacity d ω (s j r)).toNNReal ω

/-- A mixed pathwise cover gives all positive-reference own heights,
using the actual initial mean formula and the landed ambient comparison.
The ambient cover is required only at physical landings inside the pocket. -/
theorem visitReferenceHeightCoverPosExc_of_initial_and_exposed
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ j : SideTest Ω, j.Ready d → ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ j : SideTest Ω, j.Ready d → ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j : SideTest Ω, j.Ready d → ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hFormula : InitialPocketMeanFormula i d side G)
    (hIncoming : VisitReferenceIncomingAccessCoverPosExc i d s X)
    (hExposed : VisitReferenceAmbientCoverPosExc i d side s
      (fun j q ω => X j q ω ∪ ((j.target i d).domain ω)ᶜ)) :
    VisitReferenceHeightCoverPosExc i d side s X := by
  have hInitial := initialReferenceHeightsExc_of_meanFormula i d side G hKilled
    hRc hLc hRm hLm hCoupling hFormula (fun _ _ _ => ∅)
  have hExposedHeight := visitReferenceHeightCoverPosExc_of_ambient i d side s
    (fun j q ω => X j q ω ∪ ((j.target i d).domain ω)ᶜ)
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife
    hCont hStart hMeas hDetermined hLocal hHarm hExposed
  intro j hj target e zL zR q hq gB hgB
  have hg₀ := (hFormula j hj).1
  have hInitialω := hInitial j hj (G j) hg₀
  have hInitial' : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ,
      x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω)
        (j.target i d).harmonic (harmRep (G j ω) (H \ j.capacityReference i d 0 ω)))
        (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d (side j) 0 ω x)) := by
    filter_upwards [hInitialω] with ω hHeight hω x hx
    exact hHeight hω x hx (Set.notMem_empty _)
  have hOwn := ae_reference_incoming_own_heights_of_initial hj hTransport hTranslate hu hh
    hCoupling hu' hKilled hLife (hCont j hj) (hStart j hj) (hMeas j hj)
    (hDetermined j hj) (hLocal j hj) (side j) hHarm (s j) hg₀ hgB hInitial'
  filter_upwards [hOwn, hIncoming j hj q hq, hExposedHeight j hj q hq gB hgB]
    with ω hOwnω hIncomingω hExposedω hω hLive current ξ hξ hX
  by_cases hInside : extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω
  · exact hExposedω hω hLive ξ hξ (fun h => h.elim hX (fun h => h hInside))
  · obtain ⟨r, W, q', x, a, hVisit, hOrder, hW, hW0, hqq', hEq, ha, haξ, hx, hx₀, hxB⟩ :=
      hIncomingω hω hLive ξ hξ hX hInside
    have hOwnHeight := hOwnω hω r hVisit q hOrder W hW hW0 q' hqq' hEq x a ha hx hx₀ hxB
    obtain ⟨ε, hε, hCollar, hTransition, -, hWord⟩ :=
      reference_incoming_geometry_and_word hj hRc (hLc j.seed) (side j) hω (s j r) q hOrder
        hW hW0 hqq' hEq ha hx hxB (by simpa only [haξ, SideTarget.jumps] using hξ)
    rw [haξ] at hTransition hWord
    exact ⟨r, _, ε, _, hVisit, hOrder, hε, hCollar, hTransition, hOwnHeight, hWord⟩

end InteractingSLE.Wire
