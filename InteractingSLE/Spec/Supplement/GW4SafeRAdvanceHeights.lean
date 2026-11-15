/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceBounds

/-!
# GW4: incoming height bounds from the actual connector heights

The existing component boundary-data predicate gives the ordinary flank
heights. Generic boundary points transfer the original connector inequalities
to the whole piecewise constant component word. The named connector-height
property is still to be proved for the actual walks; no bound is assigned to
an incident original-real contact of an ordinary flow piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open GW3Word

/-- The source's low/high inequality on the recorded original-real connectors,
off the original height marks and the original root. This is a named geometric
input, not a theorem about every arbitrary staged driver. -/
def WalkConnectorHeightBounds (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) : Prop :=
  ∀ a ∈ (ExplState.run κ b J spec D spec.2.2.length).2.1,
    ∀ x ∈ a, x ≠ spec.1 → x ∉ J →
      if right then b x ≤ -sleLambda (16 / κ) else sleLambda (16 / κ) ≤ b x

/-- The exact component boundary word satisfies GW3.1's height inequalities
once its actual recorded connectors satisfy the original low/high inequalities.
No finiteness of the fibers over an original contact is assumed. -/
theorem incomingHeightBounds_of_connectorHeights {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} {wR wL : ExplSpec}
    {DR DL : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR0 : wR.1 = 0) (hL0 : wL.1 = 0)
    (hR : WalkConnectorHeightBounds κ b J wR DR true)
    (hL : WalkConnectorHeightBounds κ b J wL DL false)
    {C : Set ℂ} {c : Chart}
    (hch : IsComponentChart (ExplState.physSet κ b J wR DR)
      (ExplState.physSet κ b J wL DL) C c) (hCo : IsOpen C)
    {bC : ℝ → ℝ} {JC : Finset ℝ} (hpc : IsPiecewiseConstantBoundaryData bC JC)
    (hbd : IsComponentBoundaryData κ b (ExplState.ordinarySet κ b J wR DR)
      (ExplState.ordinarySet κ b J wL DL) c.2.1 bC JC) :
    IncomingHeightBounds κ bC JC := by
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have key : ∀ y, y ≠ 0 → y ∉ JC →
      ∃ x : ℝ, bC x = bC y ∧ x ∉ JC ∧ (0 < y → 0 < x) ∧ (y < 0 → x < 0) ∧
        ∃ p : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) ∧
          (0 < x → p ∈ ExplState.physSet κ b J wR DR) ∧
          (x < 0 → p ∈ ExplState.physSet κ b J wL DL) ∧
          ∀ t ∈ insert 0 J, p ≠ (t : ℂ) := by
    intro y hy0 hyJ
    obtain ⟨ε, hε, hloc⟩ := Metric.eventually_nhds_iff.1 (hpc y hyJ)
    let δ := min ε |y| / 2
    have hδ : 0 < δ := half_pos (lt_min hε (abs_pos.2 hy0))
    have hδε : δ < ε := by dsimp only [δ]; linarith only [min_le_left ε |y|, hε]
    have hδy : δ < |y| := by
      dsimp only [δ]
      linarith only [min_le_right ε |y|, abs_pos.2 hy0]
    obtain ⟨x, hx, hxJ, p, hp, hpR, hpL, hpE⟩ :=
      exists_generic hch hCo (by linarith only [hδ] : y - δ < y + δ) JC (insert 0 J)
    have hdist : dist x y < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith only [hx.1, hx.2, hδε]
    refine ⟨x, hloc hdist, hxJ, ?_, ?_, p, hp, hpR, hpL, hpE⟩
    · intro hy
      rw [abs_of_pos hy] at hδy
      linarith only [hx.1, hδy]
    · intro hy
      rw [abs_of_neg hy] at hδy
      linarith only [hx.2, hδy]
  constructor
  · intro y hy hyJ
    obtain ⟨x, he, hxJ, -, hxneg, p, hp, -, hpL, hpE⟩ := key y hy.ne hyJ
    have hx := hxneg hy
    rw [← he, (hbd x hxJ p hp).2 hx]
    split_ifs with hpo
    · exact hΛ.le
    · rcases mem_physSet_cases (hpL hx) hpo with h0 | ⟨a, ha, t, ht, rfl⟩
      · exact False.elim (hpE 0 (Finset.mem_insert_self _ _) (by simpa only [hL0] using h0))
      · have ht0 : t ≠ wL.1 := fun he => hpE 0 (Finset.mem_insert_self _ _)
          (by rw [he, hL0])
        have htJ : t ∉ J := fun htJ => hpE t (Finset.mem_insert_of_mem htJ) rfl
        exact hL a ha t ht ht0 htJ
  · intro y hy hyJ
    obtain ⟨x, he, hxJ, hxpos, -, p, hp, hpR, -, hpE⟩ := key y hy.ne' hyJ
    have hx := hxpos hy
    rw [← he, (hbd x hxJ p hp).1 hx]
    split_ifs with hpo
    · exact neg_le_neg hΛ.le
    · rcases mem_physSet_cases (hpR hx) hpo with h0 | ⟨a, ha, t, ht, rfl⟩
      · exact False.elim (hpE 0 (Finset.mem_insert_self _ _) (by simpa only [hR0] using h0))
      · have ht0 : t ≠ wR.1 := fun he => hpE 0 (Finset.mem_insert_self _ _)
          (by rw [he, hR0])
        have htJ : t ∉ J := fun htJ => hpE t (Finset.mem_insert_of_mem htJ) rfl
        exact hR a ha t ht ht0 htJ

end InteractingSLE.Theorem14.GW4Fix
