import HigherDimLQGContinuity.Improve.PinWindow
import HigherDimLQGContinuity.SiteEvents.Cap

/-!
# Parameter ratio bound at every successful seed trial
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The cap already present in the whole-site event controls all seed scale
ratios; the trial radii form one fixed finite list. -/
theorem q11_trial_ratio_bound {d : ℕ} (hd : 2 ≤ d)
    {ξ η L Kpin v τ : ℝ} (hξ : 0 ≤ ξ) (hη : 0 ≤ η)
    (hL : 0 < L) (hKpin : 0 ≤ Kpin)
    (Ntr : ℕ)
    (hτ : |η - ξ| ≤ τ)
    (hτsmall :
      τ ≤ v / (20 * (Real.sqrt (2 * d) + Kpin) *
        (1 + ∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)| + 3)))
    (j : Fin Ntr) (c : Rd d) (g : DistRd d)
    (hcap : |sphereAvg g (seedTrialRadius L j) c| ≤ Kpin) :
    |Real.log (scaleS d η 1 (seedTrialRadius L j) c g /
      scaleS d ξ 1 (seedTrialRadius L j) c g)| ≤ v / 20 := by
  let Rlog : ℝ := ∑ i ∈ Finset.range Ntr,
    |Real.log (seedTrialRadius L i)|
  let n : ℝ := 1 + Rlog
  have hR : 0 ≤ Rlog := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hn : 1 ≤ n := by dsimp [n]; linarith
  have hcap' : |sphereAvg g (seedTrialRadius L j) c| ≤ Kpin * n := by
    exact hcap.trans (le_mul_of_one_le_right hKpin hn)
  have hlog : |Real.log (seedTrialRadius L j)| ≤ n + 3 := by
    have := q11_trial_log_bound L Ntr j
    dsimp [n]
    linarith
  have hratio := cap_scale_ratio hd g c (seedTrialRadius_pos hL j)
    hξ hη (by linarith : 0 ≤ n) hKpin hlog hcap'
  have hfac : 0 ≤ (Real.sqrt (2 * d) + Kpin) * (n + 3) := by positivity
  have hsmall : (Real.sqrt (2 * d) + Kpin) * τ * (n + 3) ≤ v / 20 := by
    have hden : 0 < 20 * (Real.sqrt (2 * d) + Kpin) * (n + 3) := by
      have hroot : 0 < Real.sqrt (2 * d : ℝ) := by
        apply Real.sqrt_pos.mpr
        have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      positivity
    have hh := (le_div_iff₀ hden).mp (by simpa only [Rlog, n] using hτsmall)
    nlinarith only [hh]
  exact hratio.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hτ (by positivity)) (by positivity)).trans hsmall)

end HigherDimLQGContinuity
