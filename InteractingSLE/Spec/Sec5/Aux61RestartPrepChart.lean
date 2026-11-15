import InteractingSLE.Spec.Sec5.Aux61RestartPrepDist

/-!
# The restart chart on the complete measurable geometric configuration

Packet PROVE-AUX61-R1. Simplicity, interiority and positive tip clearance
are measured from the retained histories and then used on their event.
The ambient histories need not satisfy these geometric conditions everywhere.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49

/-- The retained own prefix is simple and interior, with its current tip at
positive distance from the retained counterflow hull. -/
def restartPrefixEvent {Ω : Type*} (s : ℝ≥0) (q : ℚ)
    (Y : Ω → HistorySpace 0 0) (η : Ω → ℝ → ℂ) : Set Ω :=
  {ω | InjOn (η ω) (Icc (0 : ℝ) q) ∧ MapsTo (η ω) (Ioc (0 : ℝ) q) H ∧
    0 < infDist (η ω q) (historyHull s Y ω)}

/-- The separated simple interior prefix event is measurable from its
retained observations and the stopped counterflow. -/
theorem measurableSet_restartPrefixEvent
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {q : ℚ} (hq : 0 ≤ (q : ℝ))
    {Y : Ω → HistorySpace 0 0} (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 q))
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t) :
    MeasurableSet (restartPrefixEvent s q Y η) :=
  (measurableSet_injOn_prefix hc hm).inter
    ((measurableSet_interior_prefix hc hm).inter
      (measurableSet_lt measurable_const
        (measurable_infDist_historyHull hY (hm q ⟨hq, le_rfl⟩))))

/-- The full retained geometric configuration, including the physical
original right-target component and current access. -/
def restartConfigurationEvent {Ω : Type*} (s r : ℝ≥0) (q : ℚ)
    (Y : Ω → HistorySpace 0 0) (η : Ω → ℝ → ℂ) (U : ℝ≥0 → Ω → ℝ) : Set Ω :=
  restartPrefixEvent s q Y η ∩ protectedOriginalTargetEvent s r q Y η U

/-- The measurable chart on the full source configuration. Simplicity,
interiority, positive tip clearance, target protection and component
incidence are event properties, with no global geometric premise. -/
theorem has_original_target_restart_chart_on_configuration
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    (hrq : (r : ℝ) = q) (hq : 0 < (q : ℝ)) {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} (he : DenseRange e) :
    let E := restartConfigurationEvent s r q Y η U
    MeasurableSet E ∧ HasOriginalTargetRestartChart s r q
      (fun ω : E => Y ω.1) (fun ω : E => η ω.1) (fun t (ω : E) => U t ω.1) e := by
  let G := restartPrefixEvent s q Y η
  have hG : MeasurableSet G := measurableSet_restartPrefixEvent hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) hm
  have hsub : MeasurableSet ((Subtype.val : G → Ω) ⁻¹'
      protectedOriginalTargetEvent s r q Y η U) :=
    (has_original_target_restart_chart_on_protected_event hrq hq
      (hY.comp measurable_subtype_coe) (fun ω => hUc ω.1) (fun ω => hU0 ω.1)
      (fun t ht => (hUm t ht).comp measurable_subtype_coe)
      (fun ω => hη ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2.1)
      (fun t ht => (hm t ht).comp measurable_subtype_coe) (fun ω => ω.2.2.2) he).1
  have hE : MeasurableSet (restartConfigurationEvent s r q Y η U) := by
    have h := (MeasurableEmbedding.subtype_coe hG).measurableSet_preimage.1 hsub
    simpa only [Subtype.range_coe, inter_comm, restartConfigurationEvent, G] using h
  refine ⟨hE, ?_⟩
  exact has_original_target_restart_chart_of_protection hrq hq
    (hY.comp measurable_subtype_coe) (fun ω => hUc ω.1) (fun ω => hU0 ω.1)
    (fun t ht => (hUm t ht).comp measurable_subtype_coe)
    (fun ω => hη ω.1) (fun ω => ω.2.1.1) (fun ω => ω.2.1.2.1)
    (fun t ht => (hm t ht).comp measurable_subtype_coe)
    (fun ω => ω.2.1.2.2) (fun ω => ω.2.2.1) (fun ω => ω.2.2.2) he

end InteractingSLE.Sec5.Aux61Restart
