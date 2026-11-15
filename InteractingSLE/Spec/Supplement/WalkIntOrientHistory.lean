/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientClock

/-!
# A chronological history ends at its last full-walk parameter

Compactness and connectedness already identify the carrier with an initial
segment. The appended arc's increasing inverse parameter identifies its
endpoint as the last point of that segment, retaining orientation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

open GW1WalkChain WalkIntChrono

/-- A seeded chronological history contained in a proper walk is its
initial segment, with the chronological endpoint at the last parameter. -/
theorem arcHistory_endpoint_initial_segment {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) {A : Set ℂ} {q : ℂ}
    (h : ArcHistory (α 0) A q) (hrange : A ⊆ range α) :
    ∃ a : ℝ≥0, A = α '' Icc 0 a ∧ q = α a := by
  revert hrange
  induction h with
  | root =>
    intro _
    exact ⟨0, by simp only [Icc_self, image_singleton], rfl⟩
  | @append A q past γ hγ hupper hstart hmeet ih =>
    intro hrange
    obtain ⟨a, hA, hq⟩ := ih (subset_union_left.trans hrange)
    have hγrange : γ '' Icc 0 1 ⊆ range α :=
      (image_mono Icc_subset_Iic_self).trans (subset_union_right.trans hrange)
    have hmono := strictMonoOn_curveTime_of_initial_segment hα (show (0 : ℝ≥0) ≤ 1 by norm_num)
      (hγ.1.mono Icc_subset_Iic_self) (hγ.2.mono Icc_subset_Iic_self)
      hγrange (hstart.trans hq) (fun t ht hz => hmeet t ht.2 (hA ▸ hz))
    obtain ⟨hc, hp, h0⟩ := arcHistory_compact_preconnected_seed
      (past.append γ hγ hupper hstart hmeet)
    obtain ⟨b, hB⟩ := exists_initial_segment hα hc hp hrange h0
    have hγ1 : γ 1 ∈ range α := hγrange ⟨1, by norm_num, rfl⟩
    have hlast : b ≤ curveTime α (γ 1) := by
      have hb : α b ∈ A ∪ γ '' Iic 1 := by
        rw [hB]
        exact ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩
      rcases hb with hb | ⟨t, ht, htb⟩
      · obtain ⟨u, hu, hub⟩ := hA ▸ hb
        have hba : b ≤ a := hα.2.1 hub ▸ hu.2
        have htime : curveTime α (γ 0) = a := by
          rw [hstart, hq, curveTime_apply hα.2.1]
        exact hba.trans (htime ▸ hmono.monotoneOn (by norm_num) (by norm_num) (by norm_num))
      · have htb' : curveTime α (γ t) = b := by rw [htb, curveTime_apply hα.2.1]
        exact htb' ▸ hmono.monotoneOn ⟨zero_le, ht⟩ (by norm_num) ht
    have hγend : γ 1 ∈ α '' Icc 0 b := by
      rw [← hB]
      exact Or.inr ⟨1, mem_Iic.2 le_rfl, rfl⟩
    obtain ⟨u, hu, hue⟩ := hγend
    have htime : curveTime α (γ 1) = u := by rw [← hue, curveTime_apply hα.2.1]
    have hub : u = b := le_antisymm hu.2 (htime ▸ hlast)
    exact ⟨b, hB, hue.symm.trans (congrArg α hub)⟩

/-- The original prefix-history certificate now also determines the
endpoint, with no separately assumed orientation or parameter map. -/
theorem prefixHistory_endpoint_initial_segment {s : ExplState}
    {R : WalkIntFill.WalkPrefix s} {α : ℝ≥0 → ℂ}
    (P : PrefixHistory R α) (hα : Supp9B.IsProperCurve α) :
    ∃ a : ℝ≥0, P.carrier = α '' Icc 0 a ∧ P.endpoint = α a ∧
      R.raw = (α '' Icc 0 a) ∩ QuantumZipper.H := by
  obtain ⟨a, ha, hq⟩ := arcHistory_endpoint_initial_segment hα P.history P.range_subset
  exact ⟨a, ha, hq, P.raw_eq.symm.trans (congrArg (fun B => B ∩ QuantumZipper.H) ha)⟩

end InteractingSLE.Theorem14.WalkIntOrient
