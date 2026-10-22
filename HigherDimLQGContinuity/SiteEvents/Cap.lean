import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Caps.Gaussian
import HigherDimLQGContinuity.Caps.Scale
import HigherDimLQGContinuity.Norm.PinGauss

/-! The finite family sphere average cap of equation (4.22). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory ProbabilityTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem q10_maxlog_spatial {d : ℕ} {z : Rd d} {a : ℝ}
    (ha : 1 ≤ a) (hz : ‖z‖ ≤ 4) :
    max 0 (Real.log (‖z‖ / a)) ≤ Real.log 5 := by
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  apply max_le hlog5
  by_cases hz0 : ‖z‖ = 0
  · rw [hz0, zero_div, Real.log_zero]
    exact hlog5
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
    have ha0 : 0 < a := by linarith
    have hdiv : ‖z‖ / a ≤ 5 := by
      calc
        ‖z‖ / a ≤ ‖z‖ := div_le_self (norm_nonneg z) ha
        _ ≤ 4 := hz
        _ ≤ 5 := by norm_num
    exact Real.log_le_log (div_pos hzpos ha0) hdiv

/-- The variance on a finite family of radii between `e⁻ⁿ` and `10` is `O(n)`. -/
private theorem q10_variance_family {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cvar : ℝ, 0 < Cvar ∧ ∀ {s₀ : ℝ}, 1 ≤ s₀ → s₀ ≤ 10 →
      ∀ {n : ℕ}, 1 ≤ n → ∀ {r : ℝ}, Real.exp (-(n : ℝ)) ≤ r → r ≤ 10 →
      ∀ z : Rd d, ‖z‖ ≤ 4 →
        Var[fun g : DistRd d => sphereAvg g r z; pinLaw d s₀] ≤ Cvar * n := by
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_pinLaw_le hd
  let Cvar : ℝ := 1 + max 0 (Real.log 10 + 2 * Real.log 5 + K)
  have hCvar : 0 < Cvar := by dsimp [Cvar]; linarith [le_max_left 0 (Real.log 10 + 2 * Real.log 5 + K)]
  refine ⟨Cvar, hCvar, ?_⟩
  intro s₀ hs₀ hs₀10 n hn r hrlo hr10 z hz
  have hr : 0 < r := (Real.exp_pos _).trans_le hrlo
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogrlo : -(n : ℝ) ≤ Real.log r := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hrlo
  have hlogrhi : Real.log r ≤ Real.log 10 := Real.log_le_log hr hr10
  have hlogs₀hi : Real.log s₀ ≤ Real.log 10 :=
    Real.log_le_log (by linarith) hs₀10
  have hlogs₀lo : 0 ≤ Real.log s₀ := Real.log_nonneg hs₀
  have hconst : Real.log 10 + 2 * Real.log 5 + K ≤
      max 0 (Real.log 10 + 2 * Real.log 5 + K) := le_max_right _ _
  have hmax0 : 0 ≤ max 0 (Real.log 10 + 2 * Real.log 5 + K) := le_max_left _ _
  have hmaxn : max 0 (Real.log 10 + 2 * Real.log 5 + K) ≤
      max 0 (Real.log 10 + 2 * Real.log 5 + K) * n := by
    nlinarith only [mul_nonneg hmax0 (sub_nonneg.mpr hnR)]
  rcases le_total r s₀ with hle | hle
  · have hv := (hK (by linarith) hr z).1 hle
    rw [Real.log_div (by linarith : s₀ ≠ 0) hr.ne'] at hv
    have hsp := q10_maxlog_spatial hs₀ hz
    dsimp [Cvar]
    nlinarith only [hv, hlogs₀hi, hlogrlo, hsp, hconst, hmaxn, hnR]
  · have hv := (hK (by linarith) hr z).2 hle
    rw [Real.log_div hr.ne' (by linarith : s₀ ≠ 0)] at hv
    have hsp := q10_maxlog_spatial (hs₀.trans hle) hz
    dsimp [Cvar]
    nlinarith only [hv, hlogrhi, hlogs₀lo, hsp, hconst, hmaxn, hnR]

/-- The deterministic part of (4.22), including radii larger than one. -/
theorem cap_scale_ratio {d : ℕ} (hd : 2 ≤ d) (g : DistRd d) (z : Rd d)
    {r n C ξ η : ℝ} (hr : 0 < r) (hξ : 0 ≤ ξ) (hη : 0 ≤ η)
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlog : |Real.log r| ≤ n + 3)
    (hcap : |sphereAvg g r z| ≤ C * n) :
    |Real.log (scaleS d η 1 r z g / scaleS d ξ 1 r z g)| ≤
      (Real.sqrt (2 * d) + C) * |η - ξ| * (n + 3) := by
  rw [scaleS_ratio d ξ η 1 hr, Real.log_exp]
  simp only [one_mul]
  have hφ := phiXi_lipschitz_nonneg hd hη hξ
  have hsq : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have hdiff : 0 ≤ |η - ξ| := abs_nonneg _
  have hn3 : 0 ≤ n + 3 := by linarith
  calc
    |(phiXi d η - phiXi d ξ) * Real.log r + (η - ξ) * sphereAvg g r z| ≤
      |phiXi d η - phiXi d ξ| * |Real.log r| +
        |η - ξ| * |sphereAvg g r z| := by
          simpa only [abs_mul] using abs_add_le
            ((phiXi d η - phiXi d ξ) * Real.log r) ((η - ξ) * sphereAvg g r z)
    _ ≤ (Real.sqrt (2 * d) + C) * |η - ξ| * (n + 3) := by
      calc
        _ ≤ (Real.sqrt (2 * d) * |η - ξ|) * (n + 3) +
              |η - ξ| * (C * (n + 3)) := by
                gcongr
                nlinarith only [hcap, hC]
        _ = _ := by ring

private theorem q10_log_ten_le_three : Real.log 10 ≤ 3 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).2
  have h : (2.5 : ℝ) ≤ Real.exp 1 :=
    (by norm_num : (2.5 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have he : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by
    exact (Real.exp_one_pow 3).symm
  rw [he]
  nlinarith [sq_nonneg (Real.exp 1 - 2.5)]

/-- A finite family of pin radii has a Gaussian cap and a parameter scale ratio cap. -/
theorem cap_finite_family {d : ℕ} (hd : 2 ≤ d) {s₀ CF ξbar : ℝ}
    (hs₀ : 1 ≤ s₀) (hs₀10 : s₀ ≤ 10) (hCF : 1 ≤ CF) :
    ∃ Ccap : ℝ, 0 < Ccap ∧
      ∀ {n : ℕ}, 1 ≤ n → ∀ F : Finset (ℝ × Rd d),
        (∀ p ∈ F, Real.exp (-(n : ℝ)) ≤ p.1 ∧ p.1 ≤ 10 ∧ ‖p.2‖ ≤ 4) →
        ((F.card : ℝ) ≤ CF * Real.exp (CF * n)) →
        pinLaw d s₀ {g | ∃ p ∈ F, Ccap * n < |sphereAvg g p.1 p.2|} ≤
          ENNReal.ofReal (2 * Real.exp (-(n : ℝ))) ∧
        (∀ g : DistRd d, (∀ p ∈ F, |sphereAvg g p.1 p.2| ≤ Ccap * n) →
          ∀ ξ ∈ Set.Icc (0 : ℝ) ξbar, ∀ η ∈ Set.Icc (0 : ℝ) ξbar,
            ∀ p ∈ F,
              |Real.log (scaleS d η 1 p.1 p.2 g / scaleS d ξ 1 p.1 p.2 g)| ≤
                (Real.sqrt (2 * d) + Ccap) * |η - ξ| * (n + 3)) := by
  obtain ⟨Cvar, hCvar, hvar⟩ := q10_variance_family hd
  let Ccap : ℝ := Cvar + CF + 2
  have hCcap : 0 < Ccap := by dsimp [Ccap]; linarith
  refine ⟨Ccap, hCcap, ?_⟩
  intro n hn F hF hcard
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs₀pos : 0 < s₀ := by linarith
  have hV : ∀ p ∈ F,
      Var[fun g : DistRd d => sphereAvg g (1 * p.1) p.2; pinLaw d s₀] ≤ Cvar * n := by
    intro p hp
    simpa only [one_mul] using hvar hs₀ hs₀10 hn (hF p hp).1 (hF p hp).2.1 p.2 (hF p hp).2.2
  have hpos : ∀ p ∈ F, 0 < (1 : ℝ) * p.1 := by
    intro p hp
    simp only [one_mul]
    exact (Real.exp_pos _).trans_le (hF p hp).1
  have hcap := p4_cap_finite hd hs₀pos F hpos hV (T := Ccap * n) (t := 2) (by norm_num)
  have hcount_exp : CF ≤ Real.exp (CF * n) := by
    calc
      CF ≤ CF * n + 1 := by nlinarith only [hCF, hnR]
      _ ≤ Real.exp (CF * n) := Real.add_one_le_exp _
  have hbound : (F.card : ℝ) *
      (2 * Real.exp (-(2 : ℝ) * (Ccap * n) + 2 ^ 2 * (Cvar * n) / 2)) ≤
      2 * Real.exp (-(n : ℝ)) := by
    have hfactor : 0 ≤ 2 * Real.exp (-(2 : ℝ) * (Ccap * n) + 2 ^ 2 * (Cvar * n) / 2) := by
      positivity
    have hstep := mul_le_mul_of_nonneg_right hcard hfactor
    have heq : CF * Real.exp (CF * n) *
        (2 * Real.exp (-(2 : ℝ) * (Ccap * n) + 2 ^ 2 * (Cvar * n) / 2)) =
        2 * CF * Real.exp (-(CF + 4) * n) := by
      calc
        _ = 2 * CF * (Real.exp (CF * n) *
            Real.exp (-(2 : ℝ) * (Ccap * n) + 2 ^ 2 * (Cvar * n) / 2)) := by ring
        _ = 2 * CF * Real.exp (CF * n +
            (-(2 : ℝ) * (Ccap * n) + 2 ^ 2 * (Cvar * n) / 2)) := by
              conv_rhs => rw [Real.exp_add]
        _ = _ := by congr 1; dsimp [Ccap]; ring
    rw [heq] at hstep
    have hmul : CF * Real.exp (-(CF + 4) * n) ≤ Real.exp (-4 * n) := by
      have h := mul_le_mul_of_nonneg_right hcount_exp
        (Real.exp_pos (-(CF + 4) * n)).le
      have he : Real.exp (CF * n) * Real.exp (-(CF + 4) * n) = Real.exp (-4 * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he] at h
      exact h
    have hexp : Real.exp (-4 * n) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hnR]
    nlinarith only [hstep, hmul, hexp]
  constructor
  · calc
      pinLaw d s₀ _ ≤ ENNReal.ofReal ((F.card : ℝ) *
        (2 * Real.exp (-(2 : ℝ) * (Ccap * n) + 2 ^ 2 * (Cvar * n) / 2))) := by
          simpa only [one_mul] using hcap
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ))) := ENNReal.ofReal_le_ofReal hbound
  · intro g hg ξ hξ η hη p hp
    have hrlo := (hF p hp).1
    have hrhi := (hF p hp).2.1
    have hr : 0 < p.1 := (Real.exp_pos _).trans_le hrlo
    have hlogrlo : -(n : ℝ) ≤ Real.log p.1 := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hrlo
    have hlogrhi : Real.log p.1 ≤ 3 :=
      (Real.log_le_log hr hrhi).trans q10_log_ten_le_three
    have hlog : |Real.log p.1| ≤ (n : ℝ) + 3 := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact cap_scale_ratio hd g p.2 hr hξ.1 hη.1 (by linarith) hCcap.le hlog (hg p hp)

end HigherDimLQGContinuity
