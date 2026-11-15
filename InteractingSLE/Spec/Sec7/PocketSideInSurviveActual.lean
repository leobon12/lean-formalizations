/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveInitial

/-!
# Actual shared initial neighborhoods from surviving incoming coordinates

PROVE-POCKET-SIDEIN. At a common original visit, a shared current collar
and a surviving original real coordinate of the outer own flow imply
the initial physical neighborhood used by the R.5 comparison.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal

variable {Ω : Type} [MeasurableSpace Ω]

/-- Survival makes the initial outer domain active near its canonical
current physical landing, and identifies the full current forward limit. -/
theorem active_near_surviving_visit {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hCurrent : relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω =
        ((j.target i d).baseChart ω).loewner W (j.visitCapacity d ω t).toNNReal)
    {x : ℝ} {a : ℝ → ℂ}
    (hSurvives : QuantumZipper.IsForwardSol W x (j.visitCapacity d ω t).toNNReal a) :
    let O := relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω
    let ξ := (a (j.visitCapacity d ω t).toNNReal).re
    let p := j.currentVisitLanding i d ω t ξ
    (∀ᶠ z in 𝓝[(j.target i d).domain ω] p, z ∈ (O.dom : Set ℂ)) ∧
      Tendsto O.1 (𝓝[(j.target i d).domain ω] p) (𝓝 (ξ : ℂ)) := by
  have hB := isDomainChart_baseChart hj hRc hLc hω
  have hInitial := initial_forward_approach_at_surviving_visit hj hRc hLc hω ht hvisit
    hW hW0 hCurrent hSurvives
  have hActive := eventually_mem_own_stage_of_surviving_approach hB.1 hW hW0
    (j.visitCapacity d ω t).toNNReal.coe_nonneg hSurvives hInitial
  have hForward := tendsto_own_stage_of_surviving_approach hW
    (j.visitCapacity d ω t).toNNReal.coe_nonneg hSurvives hInitial
  rw [← hCurrent, hB.coe_dom] at hActive hForward
  exact ⟨hActive, hForward⟩

/-- At the proper surviving incoming access, the shared current half-disc
already supplies the shared initial physical neighborhood. -/
theorem initial_neighborhood_at_surviving_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hCurrent : relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω =
        ((outer.target i d).baseChart ω).loewner W (outer.visitCapacity d ω t).toNNReal)
    {x : ℝ} {a : ℝ → ℂ}
    (hSurvives : QuantumZipper.IsForwardSol W x (outer.visitCapacity d ω t).toNNReal a)
    {r : ℝ} (hr : 0 < r)
    (hCollar :
      let O := relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω
      let I := relChart (inner.target i d).baseChart (inner.target i d).curve
        (inner.visitCapacity d ω t).toNNReal ω
      H ∩ ball ((a (outer.visitCapacity d ω t).toNNReal).re : ℂ) r ⊆
        ((pocketTransitionChart O I).dom : Set ℂ)) :
    let p := outer.currentVisitLanding i d ω t (a (outer.visitCapacity d ω t).toNNReal).re
    ∃ ε > 0, (outer.target i d).domain ω ∩ ball p ε =
      (inner.target i d).domain ω ∩ ball p ε := by
  have hOC := (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
  have hIC := (isDomainChart_relChart_visitCapacity hI hRc hLcI hωI ht hvisit).1
  have hIncl := current_domain_inclusion_at_visit hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit
  have hIU : ((relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω).dom : Set ℂ) ⊆ (inner.target i d).domain ω := by
    rw [relChart_dom_visitCapacity hI hRc hLcI hωI ht hvisit]
    exact inter_subset_left
  obtain ⟨hActive, hForward⟩ := active_near_surviving_visit hO hRc hLcO hωO ht (hUC hvisit)
    hW hW0 hCurrent hSurvives
  exact initial_neighborhood_of_active_collar hOC hIC hIncl hUC hIU hr hCollar hActive hForward

end InteractingSLE.Wire.Current.SideTest
