import SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePSmallAll
import SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePRoundAll
import SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceIdx
import Mathlib.Analysis.Complex.ExponentialBounds

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_fine_start_gt_three {K : ℕ} (hK : 64 ≤ K)
    {T : ℝ} (hT : (2 : ℝ)^(Real.sqrt K) < T) : 3 < T := by
  have hKr : (64 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : (8 : ℝ) ≤ Real.sqrt K := by
    have hh := Real.sqrt_le_sqrt hKr
    norm_num at hh
    exact hh
  have hp : (2 : ℝ)^8 ≤ (2 : ℝ)^(Real.sqrt K) := by
    convert Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hs using 1 <;> norm_num
  norm_num at hp
  linarith

theorem j1_fine_loglog_pos {T : ℝ} (hT : 3 < T) :
    0 < Real.log (Real.log T) := by
  have hlog : 1 < Real.log T := by
    have he : Real.exp 1 < T := Real.exp_one_lt_three.trans hT
    have hh := Real.log_lt_log (Real.exp_pos 1) he
    simpa only [Real.log_exp] using hh
  exact Real.log_pos hlog

theorem j1_source_union_le_near_union
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ) (δ : ℝ) (E : ℤ × ℤ → Set Ω) :
    P {ω | ∃ b ∈ j1SourceIdx K δ, ω ∈ E b} ≤
      P {ω | ∃ b ∈ LQGMetric.DDDF.T20B.nearIdx K, ω ∈ E b} :=
  (j1_source_union_le_nearby_union P K δ E).trans
    (j1_nearby_union_le_near_union P K E)

end SupercriticalLQGUniqueness.B2.DG20Conc
