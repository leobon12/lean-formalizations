import InteractingSLE.Spec.Sec5.Aux61RestartEventSegment

/-!
# The protected original-target event without a global protection premise

Packet PROVE-AUX61-R1. Protection is itself measurable from the stopped
counterflow. Intersecting it with the current-component event gives a
measurable retained event and its chart, with no global incidence or
protection assumption. Actual glued histories satisfy protection almost surely.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open InteractingSLE.Restart WangWu LawUnique GlueCond CrossCond.Word49

/-- Original-target protection is measurable from the retained counterflow
record, including the boundary point 1. -/
theorem measurableSet_history_original_target_protected
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω)) :
    MeasurableSet {ω | (1 : ℂ) ∉ closure (historyHull s Y ω)} := by
  have hDom : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ H \ historyHull s Y ω} := by
    intro c ρ
    have h := measurableSet_comp_of_stopSigma
      (measurableSet_closedBall_subset_dom_cfChart (s := s) c ρ) hY
    simpa only [preimage_ofPred_eq, coe_dom_cfChart, historyHull] using h
  have hsub : ∀ ω, historyHull s Y ω ⊆ H := by
    rintro ω _ ⟨z, hz, rfl⟩
    exact negInv_mem_H hz.1
  have heq : ∀ ω, H \ (H \ historyHull s Y ω) = historyHull s Y ω := by
    intro ω
    ext z
    constructor
    · intro hz
      by_contra hzK
      exact hz.2 ⟨hz.1, hzK⟩
    · intro hz
      exact ⟨hsub ω hz, fun h => h.2 hz⟩
  have hm := measurable_complementH_of_closedBall hDom
  simp only [heq] at hm
  have h := hm (FlowStopIdentCMI.measurableSet_disjoint_closure_interH
    (isCompact_singleton (x := (1 : ℂ))))
  have hinter : ∀ ω, historyHull s Y ω ∩ H = historyHull s Y ω :=
    fun ω => inter_eq_left.mpr (hsub ω)
  simpa only [preimage_ofPred_eq, hinter, disjoint_singleton_left] using h

/-- The current right-target component event, restricted to protected original
targets. Protection holds almost surely for the actual glued histories. -/
def protectedOriginalTargetEvent {Ω : Type*} (s r : ℝ≥0) (q : ℚ)
    (Y : Ω → HistorySpace 0 0) (η : Ω → ℝ → ℂ) (U : ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | (1 : ℂ) ∉ closure (historyHull s Y ω)} ∩ originalTargetAccessEvent s r q Y η U

/-- The chart on the measurable protected target-component event. Both
incidence and protection are supplied by event membership, rather than
assumed globally on the sample space. -/
theorem has_original_target_restart_chart_on_protected_event
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
    {e : ℕ → ℂ} (he : DenseRange e) :
    let E := protectedOriginalTargetEvent s r q Y η U
    MeasurableSet E ∧ HasOriginalTargetRestartChart s r q
      (fun ω : E => Y ω.1) (fun ω : E => η ω.1) (fun t (ω : E) => U t ω.1) e := by
  let G := {ω | (1 : ℂ) ∉ closure (historyHull s Y ω)}
  have hG : MeasurableSet G := measurableSet_history_original_target_protected hY
  have hsub : MeasurableSet ((Subtype.val : G → Ω) ⁻¹'
      originalTargetAccessEvent s r q Y η U) :=
    measurableSet_originalTargetAccessEvent hrq hq (hY.comp measurable_subtype_coe)
      (fun ω => hUc ω.1) (fun ω => hU0 ω.1)
      (fun t ht => (hUm t ht).comp measurable_subtype_coe)
      (fun ω => hη ω.1) (fun ω => hi ω.1) (fun ω => hH ω.1)
      (fun t ht => (hm t ht).comp measurable_subtype_coe) (fun ω => ω.2)
  have hE : MeasurableSet (protectedOriginalTargetEvent s r q Y η U) := by
    have h := (MeasurableEmbedding.subtype_coe hG).measurableSet_preimage.1 hsub
    simpa only [Subtype.range_coe, inter_comm, protectedOriginalTargetEvent, G] using h
  refine ⟨hE, ?_⟩
  exact has_original_target_restart_chart_of_protection hrq hq
    (hY.comp measurable_subtype_coe) (fun ω => hUc ω.1) (fun ω => hU0 ω.1)
    (fun t ht => (hUm t ht).comp measurable_subtype_coe)
    (fun ω => hη ω.1) (fun ω => hi ω.1) (fun ω => hH ω.1)
    (fun t ht => (hm t ht).comp measurable_subtype_coe)
    (fun ω => hclear ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2) he

end InteractingSLE.Sec5.Aux61Restart
