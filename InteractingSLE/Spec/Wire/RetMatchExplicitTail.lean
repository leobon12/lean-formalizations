/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchExplicitMin

/-!
# Tail minima announce an eventually approached-from-below limit

If a sequence converges and is eventually below its limit, every tail has an
attained minimum below the limit. These minima converge to the same limit.
The corresponding random times are raw stopping times by the attained-minimum
lemma, with no right-continuity assumption.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchExplicit

/-- The attained minimum of the tail starting at `n`, or infinity off attainment. -/
def tailMinimum (r : ℕ → WithTop ℝ≥0) (n : ℕ) : WithTop ℝ≥0 :=
  attainedMin (fun k => r (n + k))

theorem isStoppingTime_tailMinimum {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {R : ℕ → Ω → WithTop ℝ≥0}
    (hR : ∀ n, IsStoppingTime 𝓕 (R n)) (n : ℕ) :
    IsStoppingTime 𝓕 (fun ω => tailMinimum (fun k => R k ω) n) :=
  isStoppingTime_attainedMin (fun k => hR (n + k))

/-- Every tail minimum is strictly below the limit, and the minima converge
to it, when the original sequence converges and is eventually below it. -/
theorem tailMinimum_lt_and_tendsto {r : ℕ → WithTop ℝ≥0} {v : ℝ≥0∞}
    (hlim : Tendsto (fun n => (r n : ℝ≥0∞)) atTop (𝓝 v))
    (hlt : ∀ᶠ n in atTop, (r n : ℝ≥0∞) < v) :
    (∀ n, (tailMinimum r n : ℝ≥0∞) < v) ∧
      Tendsto (fun n => (tailMinimum r n : ℝ≥0∞)) atTop (𝓝 v) := by
  have hmin : ∀ n, ∃ k, ∀ j, r (n + k) ≤ r (n + j) := by
    intro n
    have hshift : Tendsto (fun k => (r (n + k) : ℝ≥0∞)) atTop (𝓝 v) :=
      hlim.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat n)
    obtain ⟨k, hk, hkv⟩ := ((eventually_ge_atTop n).and hlt).exists
    obtain ⟨j, hj⟩ := exists_min_of_tendsto hshift
      ⟨k - n, by simpa only [Nat.add_sub_of_le hk] using hkv⟩
    exact ⟨j, hj⟩
  have heq : ∀ n, ∃ k, tailMinimum r n = r (n + k) ∧
      ∀ j, r (n + k) ≤ r (n + j) := by
    intro n
    obtain ⟨k, hk⟩ := hmin n
    exact ⟨k, attainedMin_eq_of_min hk, hk⟩
  have hbound : ∀ n, (tailMinimum r n : ℝ≥0∞) < v := by
    intro n
    obtain ⟨k, hk, hkv⟩ := ((eventually_ge_atTop n).and hlt).exists
    obtain ⟨j, he, hminj⟩ := heq n
    have hle : tailMinimum r n ≤ r k := by
      exact he.trans_le (by simpa only [Nat.add_sub_of_le hk] using hminj (k - n))
    exact lt_of_le_of_lt hle hkv
  refine ⟨hbound, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Ioi_mem_nhds ha))
    filter_upwards [eventually_ge_atTop N] with n hn
    obtain ⟨k, he, _⟩ := heq n
    exact (hN (n + k) (hn.trans (Nat.le_add_right _ _))).trans_eq
      (congrArg (fun x : WithTop ℝ≥0 => (x : ℝ≥0∞)) he).symm
  · intro a ha
    exact Eventually.of_forall fun n => (hbound n).trans ha

end InteractingSLE.Wire.RetMatchExplicit
