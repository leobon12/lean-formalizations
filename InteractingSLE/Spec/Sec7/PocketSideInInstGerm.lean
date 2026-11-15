/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGeometry
import InteractingSLE.Spec.Sec7.PocketStopSideCloseLaws
import InteractingSLE.Spec.Sec7.PocketStopSideFinalGeometry

/-!
# Actual pocket germs from the marked maximum-stop law

PROVE-POCKET-SIDEIN. Instantiate the marked-union boundary comparison on the
actual `SideTest` traversal and filled hull. No residual increment law or
conditional independence of the nested sets is an input. The raw maximum
law and its two retained set marks remain the probabilistic source inputs.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketWordAssembly Sec7.PocketSeedOpen
  Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketUnionPt Sec7.PocketStopField
  Sec7.PocketCoupling Sec7.Lemma71C Sec7.PocketStop LocalSets

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow}
  {d : WordObjects Ω}

/-- Both actual pocket shapes give a driven erased traversal from `Ready`. -/
theorem isDrivenCurve_target (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event, IsDrivenCurve ((j.target i d).curve ω) := by
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -⟩
  rw [target_event, target_curve]
  cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ ⊢
  · intro ω hω
    exact ((hcfg ω (hAG hω).1 (hAG hω).2).isDrivenCurve (hJ ω hω)).1
  · intro ω hω
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2)
      (hG ω (hAG hω).1).1.changeCorner_props.1.1
    exact ((hcfgI ω (hAG hω).1 hzero).isDrivenCurve (hJ ω hω)).1

/-- R.5 for the actual stopped traversal, uniformly over its reference labels
and incident landings. The geometric separation is only inside the pocket. -/
theorem ae_reference_germ_of_raw_laws [IsProbabilityMeasure (j.target i d).measure]
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {q : ℝ≥0}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (j.target i d).zeroField (j.target i d).measure)
    (hpre : locPrefixSigma (j.target i d).walls (j.target i d).event
      (j.target i d).curve q ≤ mΩ)
    (hRaw : PocketStopUnionLaw (j.target i d).walls (j.target i d).measure
      (j.target i d).event (j.target i d).curve (j.target i d).domain (j.hull d q)
      (j.target i d).zeroField q)
    {Fold : ℚ≥0 → Ω → Set ℂ} {ℳ : CoverRef → MeasurableSpace Ω}
    (hMaximumLaw : ∀ a, PocketStopUnionLaw (ℳ a) (j.target i d).measure
      (j.target i d).event (j.target i d).curve (j.target i d).domain
      (fun ω => j.hull d q ω ∪ referenceHull Fold a ω) (j.target i d).zeroField q)
    (hTwoSetMarks : ∀ a,
      MeasurableSpace.comap (activeCompl (j.target i d).event (j.target i d).curve
        (j.target i d).baseChart q) hittingSigma ⊔
      MeasurableSpace.comap (referenceSet (j.target i d).domain Fold a) hittingSigma ≤
        locPrefixSigma (ℳ a) (j.target i d).event (j.target i d).curve q)
    (hBm : ∀ a, Measurable[mΩ, hittingSigma] (referenceSet (j.target i d).domain Fold a))
    (hBloc : ∀ a, IsLocalSet (referenceSet (j.target i d).domain Fold a)
      (j.target i d).zeroField (j.target i d).measure)
    (hBunb : ∀ a, ∀ᵐ ω ∂(j.target i d).measure,
      ∀ z ∈ lowerUnion (referenceSet (j.target i d).domain Fold a ω),
        ¬ IsBounded (connectedComponentIn
          (lowerUnion (referenceSet (j.target i d).domain Fold a ω)) z))
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ a, IsLocalSetMean (referenceSet (j.target i d).domain Fold a)
      (j.target i d).zeroField (j.target i d).measure (gB a))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (activeCompl (j.target i d).event (j.target i d).curve
      (j.target i d).baseChart q) (j.target i d).zeroField (j.target i d).measure g) :
    ∀ᵐ ω ∂(j.target i d).measure, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → ∀ a (v vB : ℂ → ℝ),
      InnerProductSpace.HarmonicOnNhd v (H \ activeCompl (j.target i d).event
        (j.target i d).curve (j.target i d).baseChart q ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ activeCompl (j.target i d).event
        (j.target i d).curve (j.target i d).baseChart q ω → g ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ referenceSet (j.target i d).domain Fold a ω) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ referenceSet (j.target i d).domain Fold a ω →
          gB a ω φ = ∫ z, vB z * φ z) → ∀ (ξ : ℝ) (p : ℂ) (r : ℝ), 0 < r →
      p ∈ activeCompl (j.target i d).event (j.target i d).curve
        (j.target i d).baseChart q ω ∪ {z : ℂ | z.im = 0} →
      Tendsto (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1
        (𝓝[H] (ξ : ℂ)) (𝓝 p) → referenceHull Fold a ω ⊆ j.hull d q ω →
      Disjoint ((j.target i d).domain ω ∩ (j.hull d q ω \ referenceHull Fold a ω)) (ball p r) →
      Tendsto (fun z => v ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z) -
        vB ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hchart := isPocketChartOn hj hRc hLc (i := i)
  have hact := activeDom_eq hj hRc hLc (i := i) (q := q)
  have hCo := isOpen_domain hj (i := i)
  have hFo : ∀ ω ∈ (j.target i d).event,
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → IsOpen (H \ j.hull d q ω) :=
    fun ω hω _ => isOpen_hull_compl hj q ω hω (i := i)
  obtain ⟨hKm, hKloc⟩ := activeCompl_localFacts_of_unionLaw hh hpre hact hCo hFo hRaw
  have hγ := isDrivenCurve_target hj (i := i)
  have hKunb : ∀ᵐ ω ∂(j.target i d).measure,
      ∀ z ∈ lowerUnion (activeCompl (j.target i d).event (j.target i d).curve
        (j.target i d).baseChart q ω), ¬ IsBounded (connectedComponentIn
          (lowerUnion (activeCompl (j.target i d).event (j.target i d).curve
            (j.target i d).baseChart q ω)) z) := Eventually.of_forall
    (not_isBounded_lowerUnion_activeCompl (q := q) hγ (fun ω hω => (hchart.1 ω hω).1))
  have hpair := fun a => isHistoryAvoidanceLocal_active_reference_of_unionLaw hact
    (fun _ => inter_subset_left) (fun _ _ _ => rfl) (hTwoSetMarks a) (hMaximumLaw a)
  have hcmp := ae_all_iff.2 fun a => ae_tendsto_sub_of_marked_union hh hKm (hBm a)
    hKloc (hBloc a) (hpair a) hKunb (hBunb a) hg (hgB a)
  filter_upwards [hcmp] with ω hω hωA hq a v vB hv hvr hvB hvBr ξ p r hr hp hland hsub haway
  have hK := activeCompl_eq_liveExt hact
  have hKeq := congrFun hK ω
  rw [liveExt_of_live ⟨hωA, hq⟩] at hKeq
  have heq : activeCompl (j.target i d).event (j.target i d).curve
      (j.target i d).baseChart q ω ∩ ball p r =
      referenceSet (j.target i d).domain Fold a ω ∩ ball p r := by
    rw [hKeq]
    exact extHullSet_inter_ball_eq_of_pocket hsub haway
  have hpB : p ∈ referenceSet (j.target i d).domain Fold a ω ∪ {z : ℂ | z.im = 0} := by
    rcases hp with hp | hp
    · have hpball : p ∈ activeCompl (j.target i d).event (j.target i d).curve
          (j.target i d).baseChart q ω ∩ ball p r := ⟨hp, mem_ball_self hr⟩
      exact Or.inl ((heq ▸ hpball : p ∈ referenceSet (j.target i d).domain Fold a ω ∩
        ball p r).1)
    · exact Or.inr hp
  obtain ⟨hBA, hAB⟩ := local_agreement_of_inter_ball_eq hr heq
  exact (hω a v vB hv hvr hvB hvBr p hp hpB hBA hAB).comp
    (tendsto_common_compl hland
      (fun z hz => relChart_inv_mem_active hωA hq (hγ ω hωA) (hchart.1 ω hωA).1 hz) hr heq)

end InteractingSLE.Wire.Current.SideTest
