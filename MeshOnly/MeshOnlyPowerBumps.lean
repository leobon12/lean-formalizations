import BouRabeeGwynne.PaperObjects
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! An explicit sequence of positive-radius smooth bump functions, all fitting
inside one prescribed margin and with outer radius tending to zero. -/

open scoped Topology
open Filter

namespace BouRabeeGwynne

noncomputable def meshOnlyShrinkingBump {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) : ContDiffBump (0 : Euc d) where
  rOut := δ * (1 / 2 : ℝ) ^ n
  rIn := δ * (1 / 2 : ℝ) ^ n / 2
  rIn_pos := half_pos (mul_pos hδ (pow_pos (by norm_num) n))
  rIn_lt_rOut := half_lt_self (mul_pos hδ (pow_pos (by norm_num) n))

lemma meshOnlyShrinkingBump_rOut_le {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (meshOnlyShrinkingBump (d := d) δ hδ n).rOut ≤ δ := by
  change δ * (1 / 2 : ℝ) ^ n ≤ δ
  exact mul_le_of_le_one_right hδ.le (pow_le_one₀ (by norm_num) (by norm_num))

lemma meshOnlyShrinkingBump_rOut_tendsto {d : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (meshOnlyShrinkingBump (d := d) δ hδ n).rOut)
      atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul δ
  simpa only [meshOnlyShrinkingBump, mul_zero] using h

end BouRabeeGwynne
