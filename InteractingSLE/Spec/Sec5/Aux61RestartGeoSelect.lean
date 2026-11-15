import InteractingSLE.Spec.Sec5.Aux61RestartGeoMeas

/-!
# A measurable selector for the actual original-target component

Packet PROVE-AUX61-R1. A free physical half-disc at the original target gives
a canonical history-measurable component selector. Its whole half-disc and
its closure mark at 1 are proved, so neither is an extra marking hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

open InteractingSLE.Restart LocalSets Sec7.Lemma71E

/-- The original real target belongs to the closure of each of its half-discs. -/
theorem original_target_mem_closure_halfDisc {δ : ℝ} (hδ : 0 < δ) :
    (1 : ℂ) ∈ closure (ball (1 : ℂ) δ ∩ H) := by
  have hH : (1 : ℂ) ∈ closure H := mem_closure_iff_nhdsWithin_neBot.2
    (PrimeEnd.approachH_neBot (1 : ℝ))
  exact isOpen_ball.inter_closure ⟨mem_ball_self hδ, hH⟩

/-- A measurable dense point in an original-target collar selects that target's
component. The radius and dense-point index are chosen from countable records. -/
theorem exists_measurable_original_target_component
    {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Set ℂ}
    (hUm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ U ω})
    (htarget : ∀ ω, ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ U ω)
    {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ N : Ω → ℕ, Measurable N ∧ (∀ ω, e (N ω) ∈ U ω) ∧
      (∀ ω, ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ connectedComponentIn (U ω) (e (N ω))) ∧
      (∀ ω, (1 : ℂ) ∈ closure (connectedComponentIn (U ω) (e (N ω)))) := by
  classical
  let V : ℕ → Set ℂ := fun n => ball (1 : ℂ) (1 / ((n : ℝ) + 1)) ∩ H
  have hVo : ∀ n, IsOpen (V n) := fun _ => isOpen_ball.inter QuantumZipper.isOpen_H
  have hVne : ∀ n, (V n).Nonempty := by
    intro n
    exact closure_nonempty_iff.1 ⟨1, original_target_mem_closure_halfDisc (by positivity)⟩
  have hVm : ∀ n, MeasurableSet {ω | V n ⊆ U ω} := by
    intro n
    have hm := measurable_complementH_of_closedBall hUm
      (measurableSet_hitting (hVo n) inter_subset_right).compl
    convert hm using 1
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff]
    constructor
    · intro h ⟨z, hzC, hzV⟩
      exact hzC.2 (h hzV)
    · intro h z hzV
      by_contra hzU
      exact h ⟨z, ⟨hzV.2, hzU⟩, hzV⟩
  have hex : ∀ ω, ∃ n, V n ⊆ U ω := by
    intro ω
    obtain ⟨δ, hδ, hf⟩ := htarget ω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact ⟨n, (inter_subset_inter_left H (ball_subset_ball hn.le)).trans hf⟩
  let n : Ω → ℕ := fun ω => Nat.find (hex ω)
  have hnm : Measurable n := measurable_find hex hVm
  have hnf : ∀ ω, V (n ω) ⊆ U ω := fun ω => Nat.find_spec (hex ω)
  have hj : ∀ n, ∃ j, e j ∈ V n := fun n => he.exists_mem_open (hVo n) (hVne n)
  choose j hj using hj
  let N : Ω → ℕ := j ∘ n
  have hNm : Measurable N := (measurable_from_top (f := j)).comp hnm
  have hb : ∀ ω, e (N ω) ∈ U ω := fun ω => hnf ω (hj (n ω))
  have hVc : ∀ ω, V (n ω) ⊆ connectedComponentIn (U ω) (e (N ω)) := fun ω =>
    (convex_ball_inter_H (1 : ℂ) _).isPreconnected.subset_connectedComponentIn
      (hj (n ω)) (hnf ω)
  refine ⟨N, hNm, hb, fun ω => ⟨1 / ((n ω : ℝ) + 1), by positivity, hVc ω⟩, ?_⟩
  intro ω
  exact closure_mono (hVc ω) (original_target_mem_closure_halfDisc (by positivity))

/-- Any two components with physical collars at 1 are the same component. -/
theorem connectedComponentIn_eq_of_original_target_collars
    {U : Set ℂ} {b c : ℂ}
    (hb : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ connectedComponentIn U b)
    (hc : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ connectedComponentIn U c) :
    connectedComponentIn U b = connectedComponentIn U c := by
  obtain ⟨δ, hδ, hb⟩ := hb
  obtain ⟨ε, hε, hc⟩ := hc
  have hne : (ball (1 : ℂ) (min δ ε) ∩ H).Nonempty :=
    closure_nonempty_iff.1 ⟨1, original_target_mem_closure_halfDisc (lt_min hδ hε)⟩
  obtain ⟨z, hz⟩ := hne
  have hzb := hb ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
  have hzc := hc ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩
  exact (connectedComponentIn_eq hzb).trans (connectedComponentIn_eq hzc).symm

end InteractingSLE.Sec5.Aux61Restart
