import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# The time scale in the mesh-only spike argument

These are the scalar estimates in (5.14)--(5.16) of the volume-notation draft.
The probabilistic survival and crossing estimates are separate inputs to the
argument, not asserted here.
-/

open scoped Topology

namespace BouRabeeGwynne

/-- For small positive mesh, the draft's time is above the mesh-square scale. -/
theorem mesh_only_time_ge_square {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ 2 ≤ ε ^ (2 / (d : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd1
  have hexp : 2 / (d : ℝ) ≤ 2 := (div_le_iff₀ hdpos).mpr (by linarith)
  simpa only [Real.rpow_two] using
    Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp

/-- Multiplying the heat survival time factor by one mesh gives its square
root, uniformly in the dimension. -/
theorem mesh_only_survival_scale {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) :
    ε * (ε ^ (2 / (d : ℝ))) ^ (-(d : ℝ) / 4) = ε ^ (1 / 2 : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [← Real.rpow_mul hε.le]
  have hexp : (2 / (d : ℝ)) * (-(d : ℝ) / 4) = -(1 / 2 : ℝ) := by
    field_simp
    <;> ring
  rw [hexp]
  calc
    ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 : ℝ) * ε ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_one]
    _ = ε ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := (Real.rpow_add hε _ _).symm
    _ = ε ^ (1 / 2 : ℝ) := by norm_num

/-- Both upper bounds used to exclude a persistent spike vanish at the chosen
time scale. The constants and radius are fixed before the mesh index. -/
theorem mesh_only_spike_bound_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (𝓝 0)) (C r : ℝ) :
    Filter.Tendsto
      (fun n => C * (ε n) ^ (1 / 2 : ℝ) +
        (2 * (d : ℝ) * (ε n) ^ (2 / (d : ℝ)) +
          2 * ε n * (r + 2 * ε n)) / r ^ 2)
      Filter.atTop (𝓝 0) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsqrt := hε.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 2)
  have htime := hε.rpow_const_nhds_zero (div_pos zero_lt_two hdpos)
  simpa only [mul_zero, zero_mul, add_zero, zero_add, zero_div] using
    (hsqrt.const_mul C).add
      (((htime.const_mul (2 * (d : ℝ))).add
        ((hε.const_mul 2).mul (Filter.Tendsto.const_add r (hε.const_mul 2)))).div_const
          (r ^ 2))

end BouRabeeGwynne
