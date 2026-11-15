/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurvive

/-!
# Consistent versions for the countable pocket comparisons

PROVE-POCKET-SIDEIN. Pairing uniqueness and harmonicity give one event on
which two local means agree against every test supported in their common
complement. This permits versions chosen per candidate before comparing
pairs. No uncountable intersection over test functions is taken.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- Any two local mean versions agree simultaneously on all tests in the
active complement. The existing harmonic bump theorem supplies uniformity. -/
theorem ae_mean_apply_eq_on_compl {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Ω → Set ℂ}
    {h g g' : Ω → DistOn upperHalfPlaneOpens}
    (hA : Measurable[mΩ, hittingSigma] A) (hh : Measurable h)
    (hOpen : ∀ ω, IsOpen (H \ A ω))
    (hg : IsLocalSetMean A h P g) (hg' : IsLocalSetMean A h P g') :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ H \ A ω → g ω φ = g' ω φ := by
  refine ae_forall_apply_eq_of_bump
    (Eventually.of_forall fun ω => ⟨hOpen ω, sdiff_subset⟩) hg.2.1 hg'.2.1 ?_
  intro x δ hδ hB
  exact (IsLocalSetMean.ae_apply_eq hA hh hg hg' (GFF.bumpTest x hδ hB)).mono
    fun _ hEq _ => hEq

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWallsFin Sec7.PocketTraversal Sec7.PocketWordPerQ
  LocalSets WangWu

/-- The normalized filling at a deterministic original time is hitting
measurable directly from Ready, the wall versions and the killed driver. -/
theorem measurable_original_filling {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) (q : ℝ≥0) :
    Measurable[mΩ, hittingSigma]
      (eventFilled j.event (j.target i d).domain (fun ω => regHull d.driver d.lifetime q ω)) := by
  have hWalls : (j.target i d).walls ≤ mΩ := by
    rw [target_walls]
    exact wallsSigma_le hRm hLm
  have hEvent : MeasurableSet j.event := by
    apply hWalls
    rw [target_walls]
    obtain ⟨-, -, -, -, -, -, -, hEvent, -⟩ := hj
    exact hEvent
  exact measurable_eventFilled_of_ready hj hRc hLc hWalls hEvent
    (by rw [target_event]) (measurable_regHull hKilled measurable_const)

/-- The same normalized fillings have open active complements at every
outcome, including outside their own candidate event. -/
theorem original_filling_regular {Ω : Type} [MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d) (q : ℝ≥0) :
    ∀ ω, eventFilled j.event (j.target i d).domain
      (fun ω => regHull d.driver d.lifetime q ω) ω ⊆ H ∧
      IsOpen (H \ eventFilled j.event (j.target i d).domain
        (fun ω => regHull d.driver d.lifetime q ω) ω) := by
  exact eventFilled_regular (fun ω hω => isOpen_domain hj ω (by rwa [target_event]))
    (fun ω _ => QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      ((continuous_regDrv d.driver d.lifetime ω).comp continuous_real_toNNReal) q.coe_nonneg)

/-- The time-zero filling is the initial exterior, independently of the
original driver's values after its lifetime. -/
theorem original_filling_zero {Ω : Type} [MeasurableSpace Ω]
    (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) :
    eventFilled j.event (j.target i d).domain (fun ω => regHull d.driver d.lifetime 0 ω) =
      eventFilled j.event (j.target i d).domain (fun _ => ∅) := by
  have hZero : (fun ω => regHull d.driver d.lifetime 0 ω) = (fun _ => ∅) := by
    funext ω
    exact QuantumZipper.RS.fwdHull_zero_eq_empty
      ((continuous_regDrv d.driver d.lifetime ω).comp continuous_real_toNNReal)
  rw [hZero]

end InteractingSLE.Wire.Current.SideTest
