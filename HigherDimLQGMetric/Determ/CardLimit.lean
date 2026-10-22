import HigherDimLQGMetric.Determ.FBound

/-! The near-path slack beats the number of translated cubes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- A mesh-independent polynomial bound for the volume-scaled cube count. -/
theorem determ_eps_card_le {d : ℕ} {ε R : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) :
    ε ^ (d + 1) * ((determFixedBox (d := d) ε R).card : ℝ) ≤
      ε * (2 * R + 2 * Real.sqrt d + 2) ^ d := by
  let K : ℝ := 2 * R + 2 * Real.sqrt d + 2
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hbase : 2 * (R + Real.sqrt d * ε) / ε + 2 ≤ K / ε := by
    apply (le_div_iff₀ hε).2
    rw [add_mul, div_mul_cancel₀ _ hε.ne']
    dsimp [K]
    have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    nlinarith
  have hbase0 : 0 ≤ 2 * (R + Real.sqrt d * ε) / ε + 2 := by
    positivity
  have hcard := determ_card_fixedBox_le (d := d) hε hR
  have hpow : (2 * (R + Real.sqrt d * ε) / ε + 2) ^ d ≤ (K / ε) ^ d :=
    pow_le_pow_left₀ hbase0 hbase d
  calc
    ε ^ (d + 1) * ((determFixedBox (d := d) ε R).card : ℝ)
        ≤ ε ^ (d + 1) * (2 * (R + Real.sqrt d * ε) / ε + 2) ^ d :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ ε ^ (d + 1) * (K / ε) ^ d :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ε * K ^ d := by
      rw [pow_succ, div_pow]
      field_simp

end HigherDimLQGMetric
