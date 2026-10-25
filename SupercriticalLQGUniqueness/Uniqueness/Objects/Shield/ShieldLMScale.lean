import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldLMBridge
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.OffCentre
import NV1Evidence




 






set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

def shieldScale (a : ℝ) (K k : ℕ) : ℝ :=
  3 * (8 : ℝ) ^ K * a / 8 ^ k

theorem shieldScale_pos {a : ℝ} (ha : 0 < a) (K k : ℕ) :
    0 < shieldScale a K k := by
  unfold shieldScale
  positivity

theorem shieldScale_succ (a : ℝ) (K k : ℕ) :
    shieldScale a K (k + 1) = shieldScale a K k / 8 := by
  unfold shieldScale
  rw [pow_succ]
  ring

theorem shieldScale_eq_block (a : ℝ) (K k : ℕ) (hk : k ≤ K) :
    shieldScale a K k = 3 * 8 ^ (K - k) * a := by
  unfold shieldScale
  have hpow : (8 : ℝ) ^ (K - k) = 8 ^ K / 8 ^ k := by
    rw [pow_sub₀ (8 : ℝ) (by norm_num) hk]
    rfl
  rw [hpow]
  ring

theorem shieldScale_antitone {a : ℝ} (ha : 0 < a) (K : ℕ) :
    Antitone (shieldScale a K) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [shieldScale_succ]
  have ht := shieldScale_pos ha K k
  linarith

theorem shieldScale_ratio {a : ℝ} (ha : 0 < a) (K k : ℕ) :
    ((22 / 5) * shieldScale a K (k + 1)) /
      ((22 / 5) * shieldScale a K k) ≤ (1 / 5 : ℝ) := by
  rw [shieldScale_succ]
  have ht := shieldScale_pos ha K k
  have hneq : (22 / 5 : ℝ) * shieldScale a K k ≠ 0 := by positivity
  field_simp
  nlinarith only [ht]

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
