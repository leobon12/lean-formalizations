/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverPrefix

/-!
# Measurable driver events from an observed trace prefix

Packet PROVE-RETPLUMB. Clip the observable proxy at the requested capacity and
set it to zero off the live event. The landed inverse-Loewner reader then gives
the driver coordinate on that event, without reading any post-lifetime choice.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A measurable trace proxy agreeing through `q` on a measurable live event
makes every driver event there measurable. Only continuity through `q` is used. -/
theorem measurableSet_driver_of_observed_prefix {E : Set Ω} (hE : MeasurableSet E)
    {Γ Δ : Ω → ℝ≥0 → ℂ} {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {q : ℝ≥0}
    (hΔ : ∀ s, Measurable fun ω => Δ ω s)
    (he : ∀ ω ∈ E, ∀ s ≤ q, Δ ω s = Γ ω s)
    (hc : ∀ ω ∈ E, Continuous fun s => W s ω) (h0 : ∀ ω ∈ E, W 0 ω = 0)
    (hg : ∀ ω ∈ E, IsGeneratingTrace (fun s => W s ω) (V ω) (Γ ω))
    (hq : ∀ ω ∈ E, (q : ℝ≥0∞) < V ω) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (E ∩ {ω | W q ω ∈ A}) := by
  classical
  let ΓE : Ω → ℝ≥0 → ℂ := fun ω s => E.indicator (fun ω => Δ ω (min s q)) ω
  have hΓE : ∀ ω ∈ E, ΓE ω = fun s => Γ ω (min s q) := by
    intro ω hω
    funext s
    rw [show ΓE ω s = E.indicator (fun ω => Δ ω (min s q)) ω from rfl, indicator_of_mem hω]
    exact he ω hω _ (min_le_right _ _)
  have hcE : ∀ ω, Continuous (ΓE ω) := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [hΓE ω hω]
      exact (hg ω hω).2.1.comp_continuous (continuous_id.min continuous_const) fun s =>
        (ENNReal.coe_le_coe.2 (min_le_right s q)).trans (hq ω hω).le
    · have hz : ΓE ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [hz]
      exact continuous_const
  have h0E : ∀ ω, ΓE ω 0 = 0 := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa only [hΓE ω hω, min_eq_left (zero_le : (0 : ℝ≥0) ≤ q)] using (hg ω hω).1
    · exact indicator_of_notMem hω _
  have hm := FCPlumb.measurable_fcReadDriver hcE (fun s => (hΔ (min s q)).indicator hE) h0E q
  have hr : ∀ ω ∈ E, FCPlumb.fcReadDriver ΓE q ω = W q ω := by
    intro ω hω
    rw [fcReadDriver_congr_prefix (Δ := Γ) (fun s hs => by
      rw [hΓE ω hω]
      exact congrArg (Γ ω) (min_eq_left hs))]
    exact FCPlumb.fcReadDriver_eq (hc ω hω) (h0 ω hω) (hg ω hω) (hq ω hω)
  convert hE.inter (hm hA) using 1
  ext ω
  by_cases hω : ω ∈ E
  · simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hω, true_and, hr ω hω]
  · simp only [mem_inter_iff, hω, false_and]

/-- Physical prefix events supply ambient measurability as well: every live
capacity is reached by an integer physical line. -/
theorem adaptedBefore_timeChange_of_reaches {𝓖 : Filtration ℝ≥0 mΩ}
    {Q : ℝ≥0 → Ω → ℝ≥0} (hQ : ∀ t, Measurable[𝓖 t] (Q t))
    (hm : ∀ ω, Monotone fun t => Q t ω) {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    (hr : ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V ω → ∃ t, q ≤ Q t ω)
    (hp : ∀ (q t : ℝ≥0) (A : Set ℝ), MeasurableSet A →
      MeasurableSet[𝓖 t] ({ω | (q : ℝ≥0∞) < V ω ∧ W q ω ∈ A} ∩ {ω | q ≤ Q t ω})) :
    AdaptedBefore (DomainMarkov.Aux79.timeChange 𝓖 Q hQ) V W := by
  apply DomainMarkov.Aux79.adaptedBefore_timeChange
  intro q A hA
  refine ⟨?_, fun t => hp q t A hA⟩
  have he : {ω | (q : ℝ≥0∞) < V ω ∧ W q ω ∈ A} =
      ⋃ n : ℕ, ({ω | (q : ℝ≥0∞) < V ω ∧ W q ω ∈ A} ∩ {ω | q ≤ Q n ω}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hω
      obtain ⟨t, ht⟩ := hr ω q hω.1
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, hω, ht.trans (hm ω hn)⟩
    · rintro ⟨_, hω, -⟩
      exact hω
  rw [he]
  exact MeasurableSet.iUnion fun n => 𝓖.le n _ (hp q n A hA)

end InteractingSLE.Restart.RetAux79
