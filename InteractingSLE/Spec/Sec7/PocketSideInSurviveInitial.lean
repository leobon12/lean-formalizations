/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveLoewner

/-!
# The initial coordinate of a surviving current physical landing

PROVE-POCKET-SIDEIN. Ready already supplies the finite initial Jordan
coordinate at the canonical current landing, including exclusion of the
outgoing pole. Its boundary value is the surviving original real coordinate.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

/-- A continuous forward extension at an inverse landing has the original
real boundary coordinate as its value. -/
theorem forward_extension_value_of_inverse_landing {B : Chart} (hB : B.IsConformal)
    {E : ℂ → ℂ} (hEq : EqOn E B.1 B.dom) {p : ℂ}
    (hCont : ContinuousWithinAt E (B.dom : Set ℂ) p) {x : ℝ}
    (hInverse : Tendsto B.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : E p = x := by
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  have hWithin : Tendsto B.2.1 (𝓝[H] (x : ℂ)) (𝓝[(B.dom : Set ℂ)] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hInverse,
      eventually_nhdsWithin_of_forall fun z hz => hB.inv_mem_dom hz⟩
  have hComp := hCont.tendsto.comp hWithin
  have hId : Tendsto (fun z : ℂ => z) (𝓝[H] (x : ℂ)) (𝓝 (E p)) := by
    refine hComp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    dsimp only [Function.comp_def]
    rw [hEq (hB.inv_mem_dom hz), hB.2.2 z hz]
  exact tendsto_nhds_unique hId (tendsto_id'.2 nhdsWithin_le_nhds)

/-- The initial chart tends to that original real coordinate from its
entire initial physical domain, with its image constrained to H. -/
theorem initial_forward_approach_of_inverse_landing {B : Chart} (hB : B.IsConformal)
    {E : ℂ → ℂ} (hEq : EqOn E B.1 B.dom) {p : ℂ}
    (hCont : ContinuousWithinAt E (B.dom : Set ℂ) p) {x : ℝ}
    (hInverse : Tendsto B.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    Tendsto B.1 (𝓝[(B.dom : Set ℂ)] p) (𝓝[H] (x : ℂ)) := by
  have hValue := forward_extension_value_of_inverse_landing hB hEq hCont hInverse
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · rw [← hValue]
    exact hCont.tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => hEq hz)
  · exact eventually_nhdsWithin_of_forall fun z hz => hB.fwd_mem hz

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal

variable {Ω : Type} [MeasurableSpace Ω]

/-- At a surviving real own image, the actual canonical current physical
landing is also the initial inverse landing at the original coordinate. -/
theorem initial_inverse_landing_at_surviving_visit {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hCurrent : relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω =
        ((j.target i d).baseChart ω).loewner W (j.visitCapacity d ω t).toNNReal)
    {x : ℝ} {a : ℝ → ℂ}
    (hSurvives : QuantumZipper.IsForwardSol W x (j.visitCapacity d ω t).toNNReal a) :
    Tendsto ((j.target i d).baseChart ω).2.1 (𝓝[H] (x : ℂ))
      (𝓝 (j.currentVisitLanding i d ω t (a (j.visitCapacity d ω t).toNNReal).re)) := by
  have hLanding := tendsto_currentVisitLanding hj hRc hLc hω ht hvisit
    (a (j.visitCapacity d ω t).toNNReal).re
  rw [hCurrent] at hLanding
  exact initial_inverse_landing_of_surviving_current hW hW0
    (j.visitCapacity d ω t).toNNReal.coe_nonneg hSurvives hLanding

/-- Ready derives the full initial physical forward approach from the
actual current landing and its surviving original real own coordinate. -/
theorem initial_forward_approach_at_surviving_visit {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hCurrent : relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω =
        ((j.target i d).baseChart ω).loewner W (j.visitCapacity d ω t).toNNReal)
    {x : ℝ} {a : ℝ → ℂ}
    (hSurvives : QuantumZipper.IsForwardSol W x (j.visitCapacity d ω t).toNNReal a) :
    Tendsto ((j.target i d).baseChart ω).1
      (𝓝[(((j.target i d).baseChart ω).dom : Set ℂ)]
        (j.currentVisitLanding i d ω t (a (j.visitCapacity d ω t).toNNReal).re))
      (𝓝[H] (x : ℂ)) := by
  let ξ := (a (j.visitCapacity d ω t).toNNReal).re
  have hBase := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hp := (currentVisitLanding_spec hj hRc hLc hω ht hvisit).2.2
    (mem_Hbar_of_im_eq_zero (z := (ξ : ℂ)) (by simp))
  obtain ⟨E, hE, hEc⟩ := exists_initial_finite_extension_of_ready hj hRc hLc hω hp
    (fun hBounded => currentVisitLanding_ne_outgoingSeed hj hBounded hRc hLc hω ht hvisit ξ)
  exact initial_forward_approach_of_inverse_landing hBase.1 hE hEc
    (initial_inverse_landing_at_surviving_visit hj hRc hLc hω ht hvisit hW hW0 hCurrent hSurvives)

end InteractingSLE.Wire.Current.SideTest
