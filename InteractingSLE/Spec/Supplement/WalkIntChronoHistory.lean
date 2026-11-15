/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoTopology
import InteractingSLE.Spec.Supplement.GW1WalkChain

/-!
# Chronological histories supply compact seeded prefix supports

Finite ordinary arcs and real connectors are the existing ArcHistory.
Its elementary compactness and connectedness facts identify its carrier
with an initial segment of the full proper walk parametrization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntChrono

open GW1WalkChain WalkIntFill

/-- The finite chronological history is compact, preconnected and contains
its original seed, including when some instructions add no arc. -/
theorem arcHistory_compact_preconnected_seed {x q : ℂ} {A : Set ℂ}
    (h : ArcHistory x A q) : IsCompact A ∧ IsPreconnected A ∧ x ∈ A := by
  induction h with
  | root => exact ⟨isCompact_singleton, isPreconnected_singleton, mem_singleton _⟩
  | @append A q past γ hγ _ hstart _ ih =>
    have hc : IsCompact (Iic (1 : ℝ≥0)) := by
      convert (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) 1)) using 1
      ext t
      simp only [mem_Iic, mem_Icc, zero_le, true_and]
    refine ⟨ih.1.union (hc.image_of_continuousOn hγ.1), ?_, Or.inl ih.2.2⟩
    exact ih.2.1.union q past.endpoint_mem ⟨0, mem_Iic.2 zero_le, hstart⟩
      (isPreconnected_Iic.image _ hγ.1)

/-- Physical history data for an actual recorded prefix. The equality
retains its whole ordinary set in H and permits all real connectors. -/
structure PrefixHistory {s : ExplState} (R : WalkPrefix s) (α : ℝ≥0 → ℂ) where
  carrier : Set ℂ
  endpoint : ℂ
  history : ArcHistory (α 0) carrier endpoint
  raw_eq : carrier ∩ H = R.raw
  range_subset : carrier ⊆ range α

/-- Chronological history data determine the exact prefix set in the
given full-walk parameter; no parameter correspondence is assumed. -/
theorem PrefixHistory.exists_initial_segment {s : ExplState} {R : WalkPrefix s}
    {α : ℝ≥0 → ℂ} (P : PrefixHistory R α) (hα : Supp9B.IsProperCurve α) :
    ∃ a : ℝ≥0, P.carrier = α '' Icc 0 a ∧ R.raw = (α '' Icc 0 a) ∩ H := by
  obtain ⟨hc, hp, h0⟩ := arcHistory_compact_preconnected_seed P.history
  obtain ⟨a, ha⟩ := WalkIntChrono.exists_initial_segment hα hc hp P.range_subset h0
  exact ⟨a, ha, P.raw_eq.symm.trans (congrArg (fun A => A ∩ H) ha)⟩

/-- Missing a physical exit makes the derived initial-segment parameter
strictly earlier than that exit. -/
theorem PrefixHistory.exists_before {s : ExplState} {R : WalkPrefix s}
    {α : ℝ≥0 → ℂ} (P : PrefixHistory R α) (hα : Supp9B.IsProperCurve α)
    {t : ℝ≥0} (ht : α t ∉ P.carrier) :
    ∃ a : ℝ≥0, a < t ∧ R.raw ⊆ α '' Icc 0 a := by
  obtain ⟨hc, hp, h0⟩ := arcHistory_compact_preconnected_seed P.history
  obtain ⟨a, hat, ha⟩ := exists_initial_segment_before hα hc hp P.range_subset h0 ht
  refine ⟨a, hat, fun z hz => ?_⟩
  have hzc : z ∈ P.carrier := ((Set.ext_iff.1 P.raw_eq z).2 hz).1
  rwa [ha] at hzc

/-- Nesting physical histories supplies the raw nesting required by the
reference-family theorem; real connectors are removed only by intersecting H. -/
theorem raw_subset_of_history_subset {s s' : ExplState} {R : WalkPrefix s}
    {R' : WalkPrefix s'} {α β : ℝ≥0 → ℂ} (P : PrefixHistory R α)
    (P' : PrefixHistory R' β) (h : P.carrier ⊆ P'.carrier) : R.raw ⊆ R'.raw := by
  rw [← P.raw_eq, ← P'.raw_eq]
  exact inter_subset_inter_left H h

end InteractingSLE.Theorem14.WalkIntChrono
