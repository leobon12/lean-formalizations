/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovGeom
import InteractingSLE.Spec.Sec7.R5WallLate

/-!
# The late reference heights at the exposed wall landings (`hOuter` of R5-WALL's late split; ruling R86a)

Packet PROVE-COLLAR-COVER. R5-WALL's late split (`Wire.visitReferenceHeightCoverPosExc_of_wall_split`) takes the
heights at the exposed current coordinates whose landing lies on the pocket boundary as the named input
`Wire.VisitReferenceHeightCoverOuterPosExc`. Here it is proved, as R5-WALL's R.7 twin `R5Wall.r5Cover_exposedOuter`,
from the per-prime-end heights and a lift input:

* `LateOuterLiftWord` (def, **named pathwise input**; the late twin of `R5Wall.R7OuterLiftWord` and the outer twin of
  `R5Ref.LateAmbientLiftWord`): on every selected collar at an exposed wall landing, the limit `ℓ` of "old lift −
  ambient lift" along the old approach and the word identity `β_s(x′) + χ ℓ = current word + phase − offset`;
* **`visitReferenceHeightCoverOuterPosExc_of_liftWord`**: the cover at the exposed wall landings, with the exceptional
  set containing `lateExc ∪ lateOuterExc` (geometry `late_exists_outer_cover`, heights
  `ae_tendsto_harmRep_capacityReference_comp`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketStopWallsFin
  R5Ref
open Wire.Current.SideTest (rationalOriginalTime)
open LocalSets Aux119Heights WholeField
open Theorem14.SB.FinRel (freeNear freeNear_subset)

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The lift-difference limit and the word identity at the late exposed wall landings** (named pathwise input; the
late twin of `R5Wall.R7OuterLiftWord`): for every exposed current coordinate (open seed interval) off the jumps whose
landing lies outside the pocket, off `X`, and every rational original visit with an `IsRefCollar` collar there, the
landing in `K_s` and an ambient image `x′` off the ambient jumps reached by `f_s` along both approaches: the limit `ℓ`
of "old lift − ambient lift" along the old approach and `β_s(x′) + χ ℓ = current word + phase − offset`. -/
def LateOuterLiftWord (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q →
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
        ∀ (r : ℕ) (x ε x' : ℝ), let s := rationalOriginalTime r; let old := j.referenceVisitChart i d ω s;
          let w : ℝ → ℝ := fun t => d.driver t.toNNReal ω;
          d.curve ω s ∈ target.domain ω →
          (j.visitCapacity d ω s).toNNReal ≤ q →
          IsRefCollar old current ξ (extendFrom H current.2.1 (ξ : ℂ)) x ε →
          extendFrom H current.2.1 (ξ : ℂ) ∈ regHull d.driver d.lifetime s ω →
          x' ∉ forceJumpSet (fun a => d.forceL a s ω - d.driver s ω) (fun a => d.forceR a s ω - d.driver s ω) →
          Tendsto (fun y => fwdMap w s (current.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) →
          Tendsto (fun y => fwdMap w s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
          ∃ ℓ : ℝ,
          Tendsto (fun y => old.2.2 (old.2.1 y) - (logDerivFwd w s (old.2.1 y)).im) (𝓝[H] (x : ℂ)) (𝓝 ℓ) ∧
          forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a s ω - d.driver s ω)
              (fun a => d.forceR a s ω - d.driver s ω) x' + chiC i.kappa * ℓ =
            forceBoundaryData target.kappa target.rhoL target.rhoR
              (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
                target.marksL a q ω - segDriver (target.curve ω) q)
              (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
                target.marksR a q ω - segDriver (target.curve ω) q)
              ξ + e.phase q ω * (Ioo
                (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                  segDriver (target.curve ω) q)
                (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                  segDriver (target.curve ω) q)).indicator 1 ξ - e.offset

/-- **R5-WALL's `hOuter` on the late side tests from the outer lift input** (ruling R86a): at the exposed coordinates
landing on the pocket boundary, with the exceptional set containing `lateExc ∪ lateOuterExc`, the reference heights
read in the old chart's own lift are the current word. -/
theorem visitReferenceHeightCoverOuterPosExc_of_liftWord (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
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
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hX : ∀ j q ω, lateExc j d q ω ∪ lateOuterExc j d q ω ⊆ X j q ω)
    (hLW : LateOuterLiftWord i d side X) :
    VisitReferenceHeightCoverOuterPosExc i d side (fun _ => rationalOriginalTime) X := by
  intro j hj target e zL zR q hq gB hgB
  have hall := ae_all_iff.2 fun r => ae_tendsto_harmRep_capacityReference_comp hj hTransport hTranslate hu hh
    hCoupling hu' hKilled hLife (hCont j hj) (hStart j hj) (hMeas j hj) (hDetermined j hj) (hLocal j hj)
    (rationalOriginalTime r) (hgB r)
  filter_upwards [hall, hLW j hj q hq, hCoupling.1.2.2.2.2] with ω hH hlw hp hωE hlive current ξ hξ hXξ hSeed hOut
  have hωE' : ω ∈ j.event := by rwa [target_event] at hωE
  obtain ⟨r, x, ε, x', ρ, hv, hcap, hcol, hpK, hρ, hfree, hjump, hcur, hold⟩ :=
    late_exists_outer_cover hj hRc (hLc j.seed) hωE hp hlive ξ (fun h => hXξ (hX j q ω (Or.inl h)))
      (fun h => hXξ (hX j q ω (Or.inr h))) hSeed hOut
  obtain ⟨ℓ, hℓ, hword⟩ := hlw hωE hlive ξ hξ hXξ hSeed hOut r x ε x' hv hcap hcol hpK hjump hcur hold
  have hHt := hH r hωE' _ hpK ρ hρ _ (x : ℂ) x' hjump (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1 hfree hold
  have hsum := hHt.add (hℓ.const_mul (chiC i.kappa))
  rw [hword] at hsum
  refine ⟨r, x, ε, _, hv, hcap, hcol.1, hcol.2.1, hcol.2.2.1, hsum.congr' ?_, rfl⟩
  filter_upwards [hfree] with y hy
  have hyH := (freeNear_subset hy).1
  have hk : (j.target i d).kappa = i.kappa := by
    rw [Late.target_kappa]
    have := i.kappa_gt_four
    field_simp
  have hharmT : (j.target i d).harmonic = d.harmonic := by
    cases h : j.twoLeft <;> simp only [SideTest.target, h, Bool.false_eq_true, ↓reduceIte]
  have htg : target = j.target i d := rfl
  simp only [sideMean, htg, hk, hharmT, hHarm hyH]
  ring

end InteractingSLE.Sec7.ColCov
