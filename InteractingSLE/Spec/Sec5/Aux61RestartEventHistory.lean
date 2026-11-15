import InteractingSLE.Spec.Sec5.Aux61RestartEventAccess

/-!
# The original right-target component event is measurable in the histories

Packet PROVE-AUX61-R1. This is the event specified in Astra follow-up 4,
Part (1), §1.1. A target-collar selector identifies its component, while
countable forward-chart tests detect incidence of the current access.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 Sec7.Lemma71E

/-- The source's event that the current access lies in the component
containing the original right target, at the physical target 1 in Q. -/
def originalTargetAccessEvent {Ω : Type*} (s r : ℝ≥0) (q : ℚ)
    (Y : Ω → HistorySpace 0 0) (η : Ω → ℝ → ℂ) (U : ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | ∃ b : ℂ,
    (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
    ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈
      restartComponent (historyHull s Y ω) (η ω) q b}

/-- Once original-target collars identify a component, incidence in any
target-marked component is exactly incidence in that selected component. -/
theorem original_target_access_iff_selected_component
    {A : Set ℂ} {F : ℂ → ℂ} {b : ℂ}
    (hcollars : ∀ c : ℂ, (1 : ℂ) ∈ closure (connectedComponentIn A c) →
      ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ connectedComponentIn A c)
    (hmark : (1 : ℂ) ∈ closure (connectedComponentIn A b)) :
    (∃ c : ℂ, (1 : ℂ) ∈ closure (connectedComponentIn A c) ∧
      ∃ᶠ w in 𝓝[H] 0, F w ∈ connectedComponentIn A c) ↔
      ∃ᶠ w in 𝓝[H] 0, F w ∈ connectedComponentIn A b := by
  constructor
  · rintro ⟨c, hc, hfreq⟩
    have heq := connectedComponentIn_eq_of_original_target_collars
      (hcollars c hc) (hcollars b hmark)
    rwa [heq] at hfreq
  · exact fun hfreq => ⟨b, hmark, hfreq⟩

/-- The component restriction of the source is measurable from the two
retained histories. All driver observations are through the original own
time r and the retained counterflow stop s. -/
theorem measurableSet_originalTargetAccessEvent
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
    (hprotected : ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω)) :
    MeasurableSet (originalTargetAccessEvent s r q Y η U) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hUobs := measurableSet_closedBall_subset_historyDomain hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) hm
  have htarget := fun ω => exists_original_right_target_collar
    ((hη ω).2.1.mono Icc_subset_Ici_self) (hη ω).1 (hH ω) (hprotected ω)
  obtain ⟨N, hNm, hb, _, hmark⟩ :=
    exists_measurable_original_target_component hUobs htarget he
  let D := historyComponent s q Y η (fun ω => e (N ω))
  have hprops := historyComponent_properties hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) (fun ω => (hη ω).1) hm hNm hb
  have hDm := measurableSet_mem_of_closedBall (fun ω => (hprops.1 ω).1) hprops.2
  have hown := historyComponent_subset_own_dom (s := s) (Y := Y)
    hrq hUc hU0 hη hi hH (fun ω => e (N ω))
  have heq : originalTargetAccessEvent s r q Y η U =
      currentAccessEvent (ownHistoryChart U r) D := by
    ext ω
    exact original_target_access_iff_selected_component (fun b hbmark =>
      exists_original_right_target_component_collar
        ((hη ω).2.1.mono Icc_subset_Ici_self) (hη ω).1 (hH ω)
        (hprotected ω) hbmark) (hmark ω)
  rw [heq]
  exact measurableSet_currentAccessEvent
    (fun ω => Chart.isConformal_loewnerChartAtTime (τ := fun _ => r) hUc hU0 ω)
    (fun ω => (hprops.1 ω).1) hown hDm
    (measurable_indicator_ownHistoryChart hUc hU0 hUm) he

end InteractingSLE.Sec5.Aux61Restart
