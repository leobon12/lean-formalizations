import InteractingSLE.Spec.Sec5.Aux61RestartInstApproach
import InteractingSLE.Spec.Sec5.Aux61RestartCollar
import InteractingSLE.Spec.Sec5.CrossCondMartAsm

/-!
# The restart domain of the actual counterflow and own histories

Packet PROVE-AUX61-R1; Astra follow-up 4, section 1.1. The counterflow set
is the reflected Loewner hull read from `cfDrv0 s (Y ω)`, and the removed own
history is the entire original-time prefix, including its earlier excursions.
All measurability assertions hold in any sigma algebra recording the stopped
counterflow, the own prefix and the additional retained local-set germs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu WangWu.ImgWord LawUnique Cond44Ref Prop411Q
open GlueCond
open CrossCond.Word49
open LocalSets Sec7.Lemma71E

/-- The actual counterflow hull in the chart Q, read from its stopped record. -/
def historyHull {Ω : Type*} (s : ℝ≥0) (Y : Ω → LawUnique.HistorySpace 0 0) (ω : Ω) : Set ℂ :=
  WangWu.negInv '' fwdHull (cfDrv0 s (Y ω)) s

/-- The retained component, with the base point recorded in the past. -/
def historyComponent {Ω : Type*} (s : ℝ≥0) (r : ℚ) (Y : Ω → LawUnique.HistorySpace 0 0)
    (η : Ω → ℝ → ℂ) (b : Ω → ℂ) (ω : Ω) : Set ℂ :=
  restartComponent (historyHull s Y ω) (η ω) r (b ω)

/-- The actual reflected counterflow hull satisfies the topological hypothesis
needed by the retained-component construction, even though it is unbounded. -/
theorem historyHull_properties {Ω : Type*} (s : ℝ≥0) (Y : Ω → LawUnique.HistorySpace 0 0)
    (ω : Ω) : IsOpen (H \ historyHull s Y ω) ∧
      ∀ z ∈ lowerUnion (historyHull s Y ω),
        ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (historyHull s Y ω)) z) := by
  refine ⟨?_, not_isBounded_lowerUnion_image_negInv
    (isHPHull_fwdHull (continuous_cfDrv0 s (Y ω)) s.coe_nonneg)⟩
  have h := (cfChart s (Y ω)).dom.isOpen
  rwa [coe_dom_cfChart] at h

/-- Closed-ball tests for the actual retained domain are measurable from the
stopped counterflow and own prefix; no future own values occur in the premises. -/
theorem measurableSet_closedBall_subset_historyDomain
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {r : ℚ} (hr : 0 ≤ (r : ℝ))
    {Y : Ω → LawUnique.HistorySpace 0 0} (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 r))
    (hm : ∀ t ∈ Icc (0 : ℝ) r, Measurable fun ω => η ω t) (z : ℂ) (ρ : ℝ) :
    MeasurableSet {ω | closedBall z ρ ⊆ retainedDomain (historyHull s Y ω) (η ω) r} := by
  apply measurableSet_closedBall_subset_retainedDomain hr _ hc hm
  intro c a
  have h := measurableSet_comp_of_stopSigma
    (measurableSet_closedBall_subset_dom_cfChart (s := s) c a) hY
  simpa only [preimage_ofPred_eq, coe_dom_cfChart, historyHull] using h

/-- The actual history-selected component is open, connected and simply
connected, and its closed-ball tests are measurable in the retained sigma algebra. -/
theorem historyComponent_properties
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {r : ℚ} (hr : 0 ≤ (r : ℝ))
    {Y : Ω → LawUnique.HistorySpace 0 0} (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 r))
    (h0 : ∀ ω, η ω 0 = 0)
    (hm : ∀ t ∈ Icc (0 : ℝ) r, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N)
    (hb : ∀ ω, e (N ω) ∈ retainedDomain (historyHull s Y ω) (η ω) r) :
    (∀ ω, IsOpen (historyComponent s r Y η (fun ω => e (N ω)) ω) ∧
      IsConnected (historyComponent s r Y η (fun ω => e (N ω)) ω) ∧
      IsSimplyConnected (historyComponent s r Y η (fun ω => e (N ω)) ω) ∧
      historyComponent s r Y η (fun ω => e (N ω)) ω ⊆ H) ∧
    ∀ z ρ, MeasurableSet {ω |
      closedBall z ρ ⊆ historyComponent s r Y η (fun ω => e (N ω)) ω} := by
  refine ⟨fun ω => restartComponent_properties hr (historyHull_properties s Y ω).1
    (historyHull_properties s Y ω).2 (hc ω) (h0 ω) (hb ω), ?_⟩
  exact measurableSet_closedBall_subset_component
    (fun ω => isOpen_retainedDomain (historyHull_properties s Y ω).1 (hc ω))
    (measurableSet_closedBall_subset_historyDomain hr hY hc hm) hN hb

/-- The own inverse chart supplies the current-access collar for the actual
counterflow history at every separated original own time. -/
theorem exists_history_current_collar {Ω : Type*} {s : ℝ≥0} {r : ℚ}
    {Y : Ω → LawUnique.HistorySpace 0 0} {η : Ω → ℝ → ℂ} {W : Ω → ℝ → ℝ}
    (hW : ∀ ω, Continuous (W ω)) (hW0 : ∀ ω, W ω 0 = 0)
    (hη : ∀ ω, IsLoewnerTrace (W ω) (η ω)) (hr : 0 ≤ (r : ℝ))
    (htip : ∀ ω, η ω r ∈ H)
    (hclear : ∀ ω, 0 < infDist (η ω r) (historyHull s Y ω)) :
    ∀ ω, ∃ δ > 0,
      QuantumZipper.fwdMapInv (W ω) r ((δ / 2 : ℝ) * I) ∈
        retainedDomain (historyHull s Y ω) (η ω) r ∧
      QuantumZipper.fwdMapInv (W ω) r '' (ball 0 δ ∩ H) ⊆
        restartComponent (historyHull s Y ω) (η ω) r
          (QuantumZipper.fwdMapInv (W ω) r ((δ / 2 : ℝ) * I)) := by
  intro ω
  exact exists_restart_halfDisk_collar_of_pos_infDist (hW ω) (hW0 ω) hr (hη ω)
    (historyHull_properties s Y ω).1 (htip ω) (hclear ω)

end InteractingSLE.Sec5.Aux61Restart
