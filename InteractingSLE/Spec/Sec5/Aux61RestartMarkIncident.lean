import InteractingSLE.Spec.Sec5.Aux61RestartMarkChart

/-!
# The current access supplied by the source's fresh segment

Packet PROVE-AUX61-R1. Astra follow-up 4, Part (1), §1.1: the fresh segment
before its next retained-boundary contact stays in the original right-target
component. It supplies current-access incidence. The component selector and
the chart are nevertheless functions of the retained histories alone.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49

/-- A fresh segment in the original right-target component gives precisely
the current-access incidence needed by the measurable chart constructor.
Its positive horizon may depend on the sample and need not be measurable. -/
theorem history_current_incidence_of_fresh_segment
    {Ω : Type*} {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q)
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hi : ∀ ω, InjOn (η ω) (Icc (0 : ℝ) q))
    (hH : ∀ ω, MapsTo (η ω) (Ioc (0 : ℝ) q) H)
    (hnew : ∀ ω, ∃ b : ℂ, ∃ T : ℝ,
      (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
      (r : ℝ) < T ∧ MapsTo (η ω) (Ioc (r : ℝ) T)
        (restartComponent (historyHull s Y ω) (η ω) q b)) :
    ∀ ω, ∃ b : ℂ,
      (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
      ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈
        restartComponent (historyHull s Y ω) (η ω) q b := by
  intro ω
  obtain ⟨b, T, hmark, hrT, hseg⟩ := hnew ω
  have hown := historyComponent_subset_own_dom (s := s) (Y := Y)
    hrq hUc hU0 hη hi hH (fun _ => b) ω
  have hsub : restartComponent (historyHull s Y ω) (η ω) q b ⊆
      H \ fwdHull (Ito.rpath (U · ω)) r := by
    simpa only [historyComponent, coe_dom_ownHistoryChart hUc hU0] using hown
  refine ⟨b, hmark, ?_⟩
  exact frequent_current_access_of_fresh_continuation
    (Chart.continuous_rpath_of_continuous (hUc ω)) (Chart.rpath_zero_of (hU0 ω))
    (hη ω) r.coe_nonneg hrT hsub hseg

/-- The chart for the source's fresh-segment configuration, on actual good
hitting histories. All collar, prime-end, record and branch data are outputs. -/
theorem has_original_target_restart_chart_of_fresh_segment
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
    (hgood : ∀ ω, Y ω ∈ GlueCond.goodHitSet)
    (hnew : ∀ ω, ∃ b : ℂ, ∃ T : ℝ,
      (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
      (r : ℝ) < T ∧ MapsTo (η ω) (Ioc (r : ℝ) T)
        (restartComponent (historyHull s Y ω) (η ω) q b))
    {e : ℕ → ℂ} (he : DenseRange e) :
    HasOriginalTargetRestartChart s r q Y η U e :=
  has_original_target_restart_chart_of_goodHit hrq hq hY hUc hU0 hUm hη hi hH hm
    hclear hgood (history_current_incidence_of_fresh_segment hrq hUc hU0 hη hi hH hnew) he

end InteractingSLE.Sec5.Aux61Restart
