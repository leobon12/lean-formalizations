/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5SameLate
import InteractingSLE.Spec.Sec7.R5WallOuterHeight

/-!
# The late reference heights at the pocket boundary, per prime end (ruling R86a)

Packet PROVE-COLLAR-COVER. R5-SAMETIME's late heights (`R5Same.ae_tendsto_harmRep_capacityReference`) compare the
mean of the late old reference `j.capacityReference i d s = E ∪ K_s` (`E` the pocket exterior filled on the test
event, `K_s` the counterflow hull at the original time `s`) with the ambient coupling at hull points `z₀` inside the
pocket. At a point of a pocket wall visited by the counterflow `E` reaches `z₀` from outside the pocket, so the
comparison is made per prime end, along the `E`-free components of `(ℍ ∖ K_s) ∩ B(z₀, ρ)` (`freeNear`), with
R5-WALL's component form `R5Wall.ae_tendsto_harmRep_unionMean_comp` (the per-prime-end Proposition 3.8, ruling R84).

* **`ae_tendsto_harmRep_capacityReference_comp`**: almost surely on the test event, at every point `z₀ ∈ K_s` (inside
  the pocket or on its walls), along every approach that eventually stays in `freeNear E K_s z₀ ρ` and whose image
  under `f_s` tends to a real non-jump point `x`, `harmRep g + 𝔥₀ + χ arg f_s′ → β_s(x)`.

The inputs are exactly those of `Wire.Current.SideTest.raw_reference_law_at_original_time`. Ruling R48: nothing here
uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open LocalSets WholeField Aux119Heights PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop
  PocketWordPerQ PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C PocketUnionPt R5Same
open Wire Wire.Current Wire.Current.SideTest
open Theorem14.SB.FinRel (freeNear)

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}

/-- **R.5's late old reference at an original time keeps the ambient word at every hull point, per prime end**: for a
`Ready` side test and every local-set mean `g` of the late old reference `j.capacityReference i d s`, almost surely on
the test event, at every point `z₀` of the counterflow hull `K_s`, along every approach `F` (within `ℍ` at `ξ`) that
eventually stays in a component of `(ℍ ∖ K_s) ∩ B(z₀, ρ)` missing the pocket exterior and whose image under `f_s`
tends to a real point `x` off the jump set at time `s`: `harmRep g + 𝔥₀ + χ arg f_s′ → β_s(x)`. -/
theorem ae_tendsto_harmRep_capacityReference_comp [IsProbabilityMeasure d.measure] (hj : j.Ready d)
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
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure) (s : ℝ≥0) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (j.capacityReference i d s) (j.target i d).zeroField d.measure g) :
    ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ z₀ ∈ regHull d.driver d.lifetime s ω, ∀ ρ > 0,
      ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun a => d.forceL a s ω - d.driver s ω) (fun a => d.forceR a s ω - d.driver s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) →
      (∀ᶠ y in 𝓝[H] ξ, F y ∈ freeNear (eventFilled j.event (j.target i d).domain (fun _ => ∅) ω)
        (regHull d.driver d.lifetime s ω) z₀ ρ) →
      Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ j.capacityReference i d s ω) (F y) + d.coupledMean (F y) +
          chiC i.kappa * (logDerivFwd (fun t : ℝ => d.driver t.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a s ω - d.driver s ω)
          (fun a => d.forceR a s ω - d.driver s ω) x)) := by
  obtain ⟨hEm, hEd, hEl⟩ := initialReference_facts hj hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont
    hStart hMeas hDetermined hLocal
  rw [target_zeroField] at hEd hEl hg
  have hKH : ∀ ω, regHull d.driver d.lifetime s ω ⊆ H := fun ω z hz => hz.1
  have hunion : (fun ω => eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∪ regHull d.driver d.lifetime s ω) =
      j.capacityReference i d s := funext (eventFilled_empty_union hKH)
  have hg' : IsLocalSetMean (fun ω => eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∪
      regHull d.driver d.lifetime s ω) (centredField d.translatedField d.coupledMean) d.measure g := by
    rw [hunion]
    exact hg
  have hKm : Measurable[mΩ, hittingSigma] (regHull d.driver d.lifetime s) :=
    measurable_regHull (T := fun _ => s) hKilled measurable_const
  have hsζ : ∀ᵐ ω ∂d.measure, (s : ℝ≥0∞) < d.lifetime ω := by
    filter_upwards [hLife] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hKeq : ∀ᵐ ω ∂d.measure, regHull d.driver d.lifetime s ω = fwdHull (fun t : ℝ => d.driver t.toNNReal ω) s := by
    filter_upwards [hLife, hCoupling.1.2.2.2.2] with ω hζω hp
    have hcont : Continuous fun t => d.driver t ω := by
      rw [← continuousOn_univ]
      refine hp.2.2.2.1.mono fun t _ => ?_
      show ((t : ℝ≥0∞)) < d.lifetime ω
      rw [hζω]
      exact ENNReal.coe_lt_top
    exact regHull_eq hcont hζω s
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  filter_upwards [R5Wall.ae_tendsto_harmRep_unionMean_comp hCoupling hκ hu' hKilled s hsζ hKm hKeq hEm hEd hEl hg']
    with ω hω _ z₀ hz₀ ρ hρ F ξ x hx hF hFU hfF
  have hcap : j.capacityReference i d s ω =
      eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∪ regHull d.driver d.lifetime s ω :=
    (eventFilled_empty_union (M := j.event) (C := (j.target i d).domain) hKH ω).symm
  rw [hcap]
  exact hω z₀ hz₀ ρ hρ F ξ x hx hF hFU hfF

end InteractingSLE.Sec7.ColCov
