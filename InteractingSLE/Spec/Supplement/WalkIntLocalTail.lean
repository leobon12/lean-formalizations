/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoHistory
import InteractingSLE.Foundations.OrientationWinding

/-!
# Chronological prefix coverage supplies a physical collar

A later tail of a proper physical curve is closed. If every occurrence of
the landing precedes the cutoff, a physical ball misses that tail. Within
the ball the full ordinary walk is therefore its retained initial segment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntLocal

open WalkBdry WalkMean WalkIntFill

/-- Properness turns chronological precedence into a positive ball
avoiding the entire later tail, including all of its real contacts. -/
theorem exists_ball_disjoint_tail {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {p : ℂ} {a : ℝ≥0} (hbefore : ∀ u, α u = p → u < a) :
    ∃ ρ : ℝ, 0 < ρ ∧ Disjoint (ball p ρ) (α '' Ici a) := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hα
  have hc : IsClosed (α '' Ici a) := he.isClosedMap _ isClosed_Ici
  have hp : p ∉ α '' Ici a := by
    rintro ⟨u, hu, hup⟩
    exact (not_lt_of_ge hu) (hbefore u hup)
  obtain ⟨ρ, hρ, hsep⟩ := Orientation.exists_ball_disjoint hc hp
  refine ⟨ρ, hρ, Set.disjoint_left.2 fun z hz ht => ?_⟩
  exact (not_lt_of_ge (hsep z ht)) (by simpa only [mem_ball, dist_eq_norm] using hz)

/-- An exact chronological raw prefix contains the full ordinary walk
near any physical landing strictly before its cutoff. -/
theorem exists_ordinary_collar_of_initial_segment {s : ExplState} (R : WalkPrefix s)
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) {w : ExplSpec}
    (hRange : range α = physOf w s) {a : ℝ≥0}
    (hraw : R.raw = (α '' Icc 0 a) ∩ H) {p : ℂ}
    (hbefore : ∀ u, α u = p → u < a) :
    ∃ ρ : ℝ, 0 < ρ ∧ wsetOf s ∩ ball p ρ ⊆ R.raw := by
  obtain ⟨ρ, hρ, hdis⟩ := exists_ball_disjoint_tail hα hbefore
  refine ⟨ρ, hρ, ?_⟩
  rintro z ⟨hw, hz⟩
  have hzphys : z ∈ physOf w s :=
    ((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H w s) z).2 hw).1
  obtain ⟨u, rfl⟩ := hRange.symm ▸ hzphys
  have hua : u ≤ a := le_of_not_gt fun hau =>
    Set.disjoint_left.1 hdis hz ⟨u, hau.le, rfl⟩
  rw [hraw]
  exact ⟨⟨u, ⟨zero_le, hua⟩, rfl⟩, hw.2⟩

end InteractingSLE.Theorem14.WalkIntLocal
