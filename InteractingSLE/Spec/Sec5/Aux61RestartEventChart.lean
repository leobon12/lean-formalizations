import InteractingSLE.Spec.Sec5.Aux61RestartEventHistory

/-!
# The measurable chart restricted to the source's component event

Packet PROVE-AUX61-R1. The retained records define a measurable event, and
on that event the chart is constructed without a separate incidence input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49

/-- The restart chart is measurable on exactly the original right-target
component event. The inherited phase and both prime-end limits are included
in the output. No component-incidence hypothesis is added to the constructor. -/
theorem has_original_target_restart_chart_on_event
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    (hrq : (r : ℝ) = q) (hq : 0 < (q : ℝ)) {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hi : ∀ ω, InjOn (η ω) (Icc (0 : ℝ) q))
    (hH : ∀ ω, MapsTo (η ω) (Ioc (0 : ℝ) q) H)
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    (hclear : ∀ ω, 0 < infDist (η ω q) (historyHull s Y ω))
    (hprotected : ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω))
    {e : ℕ → ℂ} (he : DenseRange e) :
    let E := originalTargetAccessEvent s r q Y η U
    MeasurableSet E ∧ HasOriginalTargetRestartChart s r q
      (fun ω : E => Y ω.1) (fun ω : E => η ω.1) (fun t (ω : E) => U t ω.1) e := by
  refine ⟨measurableSet_originalTargetAccessEvent hrq hq hY hUc hU0 hUm hη hi hH hm
    hprotected, ?_⟩
  exact has_original_target_restart_chart_of_protection hrq hq
    (hY.comp measurable_subtype_coe) (fun ω => hUc ω.1) (fun ω => hU0 ω.1)
    (fun t ht => (hUm t ht).comp measurable_subtype_coe)
    (fun ω => hη ω.1) (fun ω => hi ω.1) (fun ω => hH ω.1)
    (fun t ht => (hm t ht).comp measurable_subtype_coe)
    (fun ω => hclear ω.1) (fun ω => hprotected ω.1) (fun ω => ω.2) he

end InteractingSLE.Sec5.Aux61Restart
