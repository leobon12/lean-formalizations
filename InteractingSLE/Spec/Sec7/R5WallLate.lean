/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC9MixedCover

/-!
# The late R.5 cover split in three pieces (rulings R86, R86a)

Packet PROVE-R5-WALL (third round). SIDE-COLLAR2's late mixed cover
(`Wire.visitReferenceHeightCoverPosExc_of_initial_and_exposed`) splits by the landing place: exposed hull landings
(ambient references, R5-SAMETIME) and incoming landings outside the pocket, for which it asks a surviving initial
coordinate (`VisitReferenceIncomingAccessCoverPosExc`). As on the R.7 tests (R5-WALL, ruling R86a), an exposed
coordinate can land on the pocket boundary; there no surviving initial coordinate exists (the landing is a visited
wall point in the closure of the hull) and the heights are the counterflow's. The split is therefore by three pieces:

* `VisitReferenceIncomingWallCoverPosExc` (named pathwise input): the incoming selection only at the coordinates
  outside the open seed interval (where `R5Wall.exists_surviving_of_wall` supplies the surviving point);
* `VisitReferenceHeightCoverOuterPosExc` (named input): the heights at the exposed coordinates landing outside the
  pocket (the late twin of `R5Wall.r5Cover_exposedOuter`);
* **`visitReferenceHeightCoverPosExc_of_wall_split`**: `VisitReferenceHeightCoverPosExc` from the initial mean formula,
  the hull cover (SIDE-COLLAR2/SAMETIME, exceptional set enlarged by the pocket's complement) and the two pieces.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
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

/-- **The incoming access selection at the wall coordinates** (named pathwise input; ruling R86a): SIDE-COLLAR2's
`VisitReferenceIncomingAccessCoverPosExc` required only at the coordinates OUTSIDE the open seed interval, where the
current coordinate is the image of a surviving initial real point (`R5Wall.exists_surviving_of_wall`). -/
def VisitReferenceIncomingWallCoverPosExc {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → ∀ ξ : ℝ,
      ξ ∉ (j.target i d).jumps q ω →
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉
        X j q ω →
      ξ ∉ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
          (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
        (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
          (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q) →
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

/-- **The late reference heights at the exposed coordinates landing outside the pocket** (named input; ruling
R86a): `VisitReferenceHeightCoverPosExc` at the exposed current coordinates whose landing is on the pocket boundary
(the late twin of `R5Wall.r5Cover_exposedOuter`: counterflow heights by the per-prime-end Proposition 3.8). -/
def VisitReferenceHeightCoverOuterPosExc {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q → ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ r, IsLocalSetMean (j.capacityReference i d (s j r))
      target.zeroField d.measure (gB r)) →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        ξ ∈ Ioo (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω - segDriver (target.curve ω) q)
          (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω - segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ target.domain ω →
        ∃ (r : ℕ) (x ε b : ℝ), let old := j.referenceVisitChart i d ω (s j r);
          d.curve ω (s j r) ∈ target.domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧ 0 < ε ∧
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
          Tendsto (fun z => old.1 (current.2.1 z))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (sideMean target.kappa old target.harmonic
            (harmRep (gB r ω) (H \ j.capacityReference i d (s j r) ω)))
            (𝓝[H] (x : ℂ)) (𝓝 b) ∧
          b = forceBoundaryData target.kappa target.rhoL target.rhoR
            (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
              target.marksL a q ω - segDriver (target.curve ω) q)
            (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
              target.marksR a q ω - segDriver (target.curve ω) q)
            ξ + e.phase q ω * (Ioo
              (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                segDriver (target.curve ω) q)
              (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                segDriver (target.curve ω) q)).indicator 1 ξ - e.offset

/-- **The late reference heights from the three-piece split cover** (rulings R86, R86a): SIDE-COLLAR2's
`visitReferenceHeightCoverPosExc_of_initial_and_exposed` with its incoming input (false at exposed coordinates
landing on the pocket boundary) replaced by the incoming selection at the wall coordinates only and the late heights
at the exposed coordinates landing outside the pocket. -/
theorem visitReferenceHeightCoverPosExc_of_wall_split
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
    (hIncoming : VisitReferenceIncomingWallCoverPosExc i d s X)
    (hOuter : VisitReferenceHeightCoverOuterPosExc i d side s X)
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
  filter_upwards [hOwn, hIncoming j hj q hq, hExposedHeight j hj q hq gB hgB, hOuter j hj q hq gB hgB]
    with ω hOwnω hIncomingω hExposedω hOuterω hω hLive current ξ hξ hX
  by_cases hInside : extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω
  · exact hExposedω hω hLive ξ hξ (fun h => h.elim hX (fun h => h hInside))
  · by_cases hSeed : ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
                  (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
            (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
                  (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
    · exact hOuterω hω hLive ξ hξ hX hSeed hInside
    obtain ⟨r, W, q', x, a, hVisit, hOrder, hW, hW0, hqq', hEq, ha, haξ, hx, hx₀, hxB⟩ :=
      hIncomingω hω hLive ξ hξ hX hSeed
    have hOwnHeight := hOwnω hω r hVisit q hOrder W hW hW0 q' hqq' hEq x a ha hx hx₀ hxB
    obtain ⟨ε, hε, hCollar, hTransition, -, hWord⟩ :=
      reference_incoming_geometry_and_word hj hRc (hLc j.seed) (side j) hω (s j r) q hOrder
        hW hW0 hqq' hEq ha hx hxB (by simpa only [haξ, SideTarget.jumps] using hξ)
    rw [haξ] at hTransition hWord
    exact ⟨r, _, ε, _, hVisit, hOrder, hε, hCollar, hTransition, hOwnHeight, hWord⟩

end InteractingSLE.Wire
