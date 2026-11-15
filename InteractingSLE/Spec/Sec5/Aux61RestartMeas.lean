import InteractingSLE.Spec.Sec5.Aux61RestartComponent
import InteractingSLE.Spec.Sec7.Lemma71EChart

/-!
# Measurable charts of the retained restart component

Packet PROVE-AUX61-R1; ruling R71. The measurable space on the parameter may be
the sigma algebra of the full retained records and germs. A component is selected
by a measurable index in a fixed dense sequence, entirely from those records.
Both the old hull and the entire finite flow prefix remain in the complement.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

open LocalSets
open Sec7.Lemma71E

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Closed-ball avoidance of a continuous random finite prefix is measurable.
This adapts the existing infinite-path result by clamping the time parameter. -/
theorem measurableSet_closedBall_inter_prefix_eq_empty {η : Ω → ℝ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 r))
    (hm : ∀ t ∈ Icc 0 r, Measurable fun ω => η ω t) (c : ℂ) (ρ : ℝ) :
    MeasurableSet {ω | closedBall c ρ ∩ η ω '' Icc 0 r = ∅} := by
  let clip : ℝ → ℝ := fun u => min (max u 0) r
  have hclip : ∀ u, clip u ∈ Icc 0 r := fun u =>
    ⟨le_min (le_max_right u 0) hr, min_le_right _ _⟩
  have hclipc : Continuous clip := (continuous_id.max continuous_const).min continuous_const
  have heq : ∀ ω, (fun u => η ω (clip u)) '' Ici 0 = η ω '' Icc 0 r := by
    intro ω
    apply subset_antisymm
    · rintro _ ⟨u, _, rfl⟩
      exact ⟨clip u, hclip u, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, by simp only [clip, max_eq_left hu.1, min_eq_left hu.2]⟩
  have h := measurableSet_closedBall_inter_image_eq_empty
    (η := fun ω u => η ω (clip u))
    (fun ω => (hc ω).comp hclipc.continuousOn fun u _ => hclip u)
    (fun u _ => hm _ (hclip u)) c ρ
  simpa only [heq] using h

/-- The retained domain is a measurable random open set when the old hull and
the finite own prefix are known from the retained records. -/
theorem measurableSet_closedBall_subset_retainedDomain {K : Ω → Set ℂ}
    {η : Ω → ℝ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hKm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ H \ K ω})
    (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 r))
    (hm : ∀ t ∈ Icc 0 r, Measurable fun ω => η ω t) (c : ℂ) (ρ : ℝ) :
    MeasurableSet {ω | closedBall c ρ ⊆ retainedDomain (K ω) (η ω) r} := by
  have heq : {ω | closedBall c ρ ⊆ retainedDomain (K ω) (η ω) r} =
      {ω | closedBall c ρ ⊆ H \ K ω} ∩
        {ω | closedBall c ρ ∩ η ω '' Icc 0 r = ∅} := by
    ext ω
    simp only [retainedDomain, mem_ofPred_eq, mem_inter_iff, subset_sdiff,
      disjoint_union_right, ← disjoint_iff_inter_eq_empty]
    tauto
  rw [heq]
  exact (hKm c ρ).inter (measurableSet_closedBall_inter_prefix_eq_empty hr hc hm c ρ)

/-- Measurable Riemann maps of the history-selected restart component, with a
measurable interior normalization and measurable inverses. No future point is
used to select the component or the chart. -/
theorem exists_measurable_restart_discPair {K : Ω → Set ℂ} {η : Ω → ℝ → ℂ}
    {r : ℝ} (hr : 0 ≤ r) (hKo : ∀ ω, IsOpen (H \ K ω))
    (hKu : ∀ ω z, z ∈ lowerUnion (K ω) →
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z))
    (hKm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ H \ K ω})
    (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 r)) (h0 : ∀ ω, η ω 0 = 0)
    (hm : ∀ t ∈ Icc 0 r, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} (he : DenseRange e) {N : Ω → ℕ} (hN : Measurable N)
    (hb : ∀ ω, e (N ω) ∈ retainedDomain (K ω) (η ω) r) :
    ∃ (Φ F : Ω → ℂ → ℂ) (a : Ω → ℂ),
      (∀ ω, a ω ∈ restartComponent (K ω) (η ω) r (e (N ω))) ∧
      (∀ ω, IsConformalBijection (Φ ω)
        (restartComponent (K ω) (η ω) r (e (N ω))) (ball 0 1) ∧ Φ ω (a ω) = 0) ∧
      (∀ ω z, z ∉ restartComponent (K ω) (η ω) r (e (N ω)) → Φ ω z = 0) ∧
      (∀ z, Measurable fun ω => Φ ω z) ∧
      (∀ ω, IsConformalBijection (F ω) (ball 0 1)
        (restartComponent (K ω) (η ω) r (e (N ω))) ∧ F ω 0 = a ω ∧
          0 < (deriv (F ω) 0).re ∧ (deriv (F ω) 0).im = 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, Measurable fun ω => F ω z) ∧
      (∀ ω, EqOn (Φ ω) (Function.invFunOn (F ω) (ball 0 1))
        (restartComponent (K ω) (η ω) r (e (N ω)))) := by
  have hprops := fun ω => restartComponent_properties hr (hKo ω) (hKu ω) (hc ω) (h0 ω) (hb ω)
  have hUm := measurableSet_closedBall_subset_retainedDomain hr hKm hc hm
  have hCm := measurableSet_closedBall_subset_component
    (fun ω => isOpen_retainedDomain (hKo ω) (hc ω)) hUm hN hb
  obtain ⟨Φ, F, a, ha, hΦ, hΦ0, hΦm, hF, hFm, hinv⟩ :=
    exists_measurable_discPair (fun ω => (hprops ω).1) (fun ω => (hprops ω).2.1)
      (fun ω => (hprops ω).2.2.1) (fun ω => (hprops ω).2.2.2) hCm he
  refine ⟨Φ, F, a, ha, hΦ, hΦ0, hΦm, fun ω => ?_, hFm, hinv⟩
  exact ⟨(hF ω).1, (hF ω).2.1, (Complex.pos_iff.1 (hF ω).2.2).1,
    (Complex.pos_iff.1 (hF ω).2.2).2.symm⟩

end InteractingSLE.Sec5.Aux61Restart
