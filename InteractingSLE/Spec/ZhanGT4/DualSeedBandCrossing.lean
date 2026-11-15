/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandRemainder

/-!
# The boundary cell in logarithmic band pasting

Packet PROVE-ZHAN-GT4-A22. A continuous compensated process has a vanishing
Taylor defect on short boundary cells. Monotonicity permits only one such
cell per boundary, also for the clamped dyadic partitions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {X c₁ c₂ B : ℝ≥0 → Ω → ℝ}

/-- A direct bound for a boundary-cell defect, with no field regularity
required across the boundary itself. -/
theorem abs_seed_itoDefect_le {a b : ℝ≥0} (hab : a ≤ b) {ω : Ω} {C η : ℝ}
    (_hC : 0 ≤ C) (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hX : |X b ω - X a ω| ≤ η) (hB : |B b ω - B a ω| ≤ η)
    (hdt : (b : ℝ) - a ≤ η) (h₁ : |c₁ a ω| ≤ C) (h₂ : |c₂ a ω| ≤ C) :
    |Ito.itoDefect X c₁ c₂ B a b ω| ≤ (1 + 2 * C) * η := by
  have hq : (B b ω - B a ω) ^ 2 ≤ η := by
    rw [← sq_abs]
    nlinarith only [hB, abs_nonneg (B b ω - B a ω), _hη, hη1]
  have hlen : 0 ≤ (b : ℝ) - a := sub_nonneg.2 hab
  have hquad : |(B b ω - B a ω) ^ 2 - ((b : ℝ) - a)| ≤ 2 * η := by
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hlen]
      linarith only [hq, hdt])
  have hlin := abs_mul_le_of_le h₁ hB
  have hsecond := abs_mul_le_of_le h₂ hquad
  have hh := (abs_sub (X b ω - X a ω - c₁ a ω * (B b ω - B a ω))
    (1 / 2 * c₂ a ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a)))).trans
      (add_le_add (abs_sub _ _) le_rfl)
  have he : |1 / 2 * c₂ a ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))| ≤ C * η := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith only [hsecond]
  change |Ito.itoDefect X c₁ c₂ B a b ω| ≤ _ at hh
  exact hh.trans (by nlinarith only [hX, hlin, he])

/-- The error confined to the cell crossing a fixed pathwise boundary. -/
def seedCrossingRemainder (X c₁ c₂ B : ℝ≥0 → Ω → ℝ) (σ t : ℝ≥0) (ω : Ω) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (cells n),
    if min (grid n k) t < σ ∧ σ < min (grid n (k + 1)) t then
      |Ito.itoDefect X c₁ c₂ B (min (grid n k) t) (min (grid n (k + 1)) t) ω| else 0

/-- Boundary-cell errors vanish pathwise; no moment bound or measurable
choice of a random Taylor constant is needed. -/
theorem tendsto_seedCrossingRemainder (σ t : ℝ≥0) (ω : Ω)
    (hX : Continuous (X · ω)) (hB : Continuous (B · ω)) {C : ℝ} (hC : 0 ≤ C)
    (h₁ : ∀ u ≤ t, |c₁ u ω| ≤ C) (h₂ : ∀ u ≤ t, |c₂ u ω| ≤ C) :
    Tendsto (seedCrossingRemainder X c₁ c₂ B σ t ω) atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := min 1 (ε / (3 * C + 2))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hXr : Continuous (fun u : ℝ => X u.toNNReal ω) := hX.comp continuous_real_toNNReal
  have hBr : Continuous (fun u : ℝ => B u.toNNReal ω) := hB.comp continuous_real_toNNReal
  obtain ⟨δX, hδX, hXu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (hXr.continuousOn (s := Icc 0 (t : ℝ)))) η hη
  obtain ⟨δB, hδB, hBu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (hBr.continuousOn (s := Icc 0 (t : ℝ)))) η hη
  let δ := min (min δX δB) η
  have hδ : 0 < δ := lt_min (lt_min hδX hδB) hη
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
  have hm (k : ℕ) : (p k : ℝ) ∈ Icc (0 : ℝ) t := ⟨(p k).coe_nonneg, min_le_right _ _⟩
  have hs (k : ℕ) : (p (k + 1) : ℝ) - p k < δ := (seed_grid_sub_le n k t).trans_lt hn
  have hd (k : ℕ) : dist (p (k + 1) : ℝ) (p k : ℝ) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (show (p k : ℝ) ≤ p (k + 1) from hp (Nat.le_succ k)))]
    exact hs k
  have hb (k : ℕ) : |Ito.itoDefect X c₁ c₂ B (p k) (p (k + 1)) ω| ≤ (1 + 2 * C) * η := by
    apply abs_seed_itoDefect_le (hp (Nat.le_succ k)) hC hη.le hη1
    · simpa only [Real.toNNReal_coe, Real.dist_eq] using
        (hXu _ (hm (k + 1)) _ (hm k) ((hd k).trans_le ((min_le_left _ _).trans (min_le_left _ _)))).le
    · simpa only [Real.toNNReal_coe, Real.dist_eq] using
        (hBu _ (hm (k + 1)) _ (hm k) ((hd k).trans_le ((min_le_left _ _).trans (min_le_right _ _)))).le
    · exact (hs k).le.trans (min_le_right _ _)
    · exact h₁ _ (min_le_right _ _)
    · exact h₂ _ (min_le_right _ _)
  have hnon : 0 ≤ seedCrossingRemainder X c₁ c₂ B σ t ω n := Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hsum : seedCrossingRemainder X c₁ c₂ B σ t ω n ≤ (1 + 2 * C) * η :=
    Ito.sum_ite_le_of_unique (by positivity) (fun k _ _ => hb k)
      (fun _ _ hk hj => seed_unique_crossing_cell (fun i j hij => by exact_mod_cast hp hij) hk hj)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
  apply hsum.trans_lt
  have he := mul_le_mul_of_nonneg_left (min_le_right 1 (ε / (3 * C + 2)))
    (by positivity : (0 : ℝ) ≤ 3 * C + 2)
  rw [mul_div_cancel₀ _ (by positivity : (3 * C + 2 : ℝ) ≠ 0)] at he
  nlinarith only [he, hη, mul_nonneg hC hη.le]

end InteractingSLE.ZhanGT4
