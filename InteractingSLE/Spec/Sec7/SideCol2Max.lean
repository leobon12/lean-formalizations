/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideCol2MaxInf
import InteractingSLE.Spec.Sec7.PocketStopSideEndMax
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm
import InteractingSLE.Spec.Sec7.PocketWordPerQSigma

/-!
# The maximum-reference law at a fixed relative capacity for actual late side tests

PROVE-SIDE-COLLAR2. For either pocket shape, retain an ordinary reference stop
and apply the marked optional union law at its maximum with the inverse capacity
clock. Fill the pocket exterior before transferring from the left end to the
right end of the erased fibre (R67). The reference stop may in particular be any
fixed rational original time. No law at a deterministic time is evaluated at a
random time, and no later interior-visit event is conditioned on.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 LocalSets WholeField PocketStopField PocketCoupling Lemma71C PocketCoord
  PocketJordan PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketTraversal
  PocketAdapt PocketStopSide PocketWordPerQ PocketStopWallsFin PocketMarks

/-- The marked maximum-reference law on every Ready native side test. All laws
are those of the original optional coupling and its two incoming flow walls.
Both the reference's stopped information and the relative prefix are retained. -/
theorem pocketStopUnionLaw_reference {Ω : Type} [mΩ : MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (j : SideTest Ω) (hj : j.Ready d)
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant
      (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField d.field d.originalMean) d.measure)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension
      (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hζ : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hR0 : ∀ ω, d.rightWall ω 0 = 0)
    (hL0 : ∀ ω, d.leftWall j.seed ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall j.seed ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall
      (centredField d.field d.originalMean) d.measure)
    (hlocL : Sec6.IsEntranceHistoryLocal (d.leftWall j.seed)
      (centredField d.field d.originalMean) d.measure)
    (q : ℝ≥0)
    (hpre : locPrefixSigma (j.target i d).walls (j.target i d).event
      (j.target i d).curve q ≤ mΩ)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration d.measure hX)
      fun ω => (τ ω : WithTop ℝ≥0)) :
    PocketStopUnionLaw ((j.target i d).walls ⊔ hτ.measurableSpace) d.measure
      (j.target i d).event (j.target i d).curve (j.target i d).domain
      (fun ω => j.hull d q ω ∪ regHull d.driver d.lifetime (τ ω) ω)
      (j.target i d).zeroField q := by
  have hRm' := measurable_right_wallsSigma (P := d.measure) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := d.measure) hRc hLc
  have h𝓦 := wallsSigma_le_drivingFiltration (P := d.measure) hX d.rightWall (d.leftWall j.seed)
  have h𝓦m := wallsSigma_le (P := d.measure) hRm hLm
  have h𝓦ℳ : wallsSigma d.measure d.rightWall (d.leftWall j.seed) ≤
      wallsSigma d.measure d.rightWall (d.leftWall j.seed) ⊔ hτ.measurableSpace := le_sup_left
  have hℳm := sup_le h𝓦m hτ.measurableSpace_le
  have hpre' : locPrefixSigma ((j.target i d).walls ⊔ hτ.measurableSpace)
      (j.target i d).event (j.target i d).curve q ≤ mΩ := by
    rw [locPrefixSigma_sup_info]
    exact sup_le hpre hτ.measurableSpace_le
  have hz : (j.target i d).zeroField = centredField d.translatedField d.coupledMean := by
    cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]
  rcases hj with ⟨-, hGm, -, hG, hζG, hcfg, hcfgI, hAm, hAG, -, hJ, hJm, -⟩
  rw [target_walls, target_event, target_curve] at hpre'
  rw [target_walls, target_event, target_curve, target_domain, hz]
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte, hull] at hAG hJ hJm hpre' ⊢
    have hGp := (measurableSet_rightLo_pos_and
      (mΩ := wallsSigma d.measure d.rightWall (d.leftWall j.seed)) hRm' hLm' hGm
      (fun ω hω => (hG ω hω).1)).1
    have hcfgA := fun ω hω => hcfg ω (hAG hω).1 (hAG hω).2
    have hW := pocketStopWallsLaw_stopHull0_reference_marked
      hT' hTr hu₀ hh hC (lt_trans (by norm_num) i.kappa_gt_four) hu₀' hX hζ
      hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm'
      hGp (fun ω hω => (hG ω hω.1).1) hAm hAG hcfgA
      (fun ω hω => hζG ω (hAG hω).1) hJ hJm q hτ
    apply pocketStopUnionLaw_stopHull_reference_of_stopHull0 hcfgA
    exact pocketStopUnionLaw_cfPocket hℳm
      (fun t => (hRm' t).mono le_sup_left le_rfl)
      (fun t => (hLm' t).mono le_sup_left le_rfl)
      (h𝓦ℳ _ hGp) (fun ω hω => (hG ω hω.1).1)
      (h𝓦ℳ _ hAm) hAG hpre' hW
  · simp only [hI, ↓reduceIte, hull] at hAG hJ hJm hpre' ⊢
    have hGp := (measurableSet_rightLo_pos_and
      (mΩ := wallsSigma d.measure d.rightWall (d.leftWall j.seed)) hRm' hLm' hGm
      (fun ω hω => (hG ω hω).1)).1
    have hG0 : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
        {ω | ω ∈ j.outerEvent ∧ ¬ 0 < rightLo (d.rightWall ω)
          (d.leftWall j.seed ω) (StripSys.rt j.seed)} := by
      convert hGm.diff hGp using 1
      ext ω
      simp only [mem_ofPred_eq, Set.mem_sdiff]
      tauto
    have hcfgA : ∀ ω ∈ j.event, IsCfPocketConfigInf (d.rightWall ω)
        (d.leftWall j.seed ω) (StripSys.rt j.seed)
        (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) := by
      intro ω hω
      exact hcfgI ω (hAG hω).1 (le_antisymm (le_of_not_gt (hAG hω).2)
        (hG ω (hAG hω).1).1.changeCorner_props.1.1)
    have hW := pocketStopWallsLaw_stopHull0Inf_reference_marked
      hT' hTr hu₀ hh hC (lt_trans (by norm_num) i.kappa_gt_four) hu₀' hX hζ
      hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm'
      hG0 (fun ω hω => (hG ω hω.1).1) hAm hAG hcfgA
      (fun ω hω => hζG ω (hAG hω).1) hJ hJm q hτ
    apply pocketStopUnionLaw_stopHullInf_reference_of_stopHull0Inf hcfgA
    exact pocketStopUnionLaw_cfPocket hℳm
      (fun t => (hRm' t).mono le_sup_left le_rfl)
      (fun t => (hLm' t).mono le_sup_left le_rfl)
      (h𝓦ℳ _ hG0) (fun ω hω => (hG ω hω.1).1)
      (h𝓦ℳ _ hAm) hAG hpre' hW

end InteractingSLE.Wire.Current.SideTest
