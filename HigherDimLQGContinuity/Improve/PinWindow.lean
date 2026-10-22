import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGContinuity.Param.Lipschitz
import HigherDimLQGContinuity.SiteEvents.Trials

/-!
# Uniform scale-factor windows from a finite sphere-average cap
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The scale exponent is uniformly bounded throughout a compact parameter
window, including its zero endpoint. -/
theorem q11_phi_abs_bound {d : ℕ} (hd : 2 ≤ d)
    {ξ ξbar : ℝ} (hξ : 0 ≤ ξ) (hξbar : ξ ≤ ξbar) :
    |phiXi d ξ| ≤ 1 + Real.sqrt (2 * d) * ξbar := by
  have hdiff := phiXi_lipschitz hd ξ 0
  rw [phiXi_zero, sub_zero, abs_of_nonneg hξ] at hdiff
  have hroot : 0 ≤ Real.sqrt (2 * d : ℝ) := Real.sqrt_nonneg _
  have hfac : Real.sqrt (2 * d) * ξ ≤ Real.sqrt (2 * d) * ξbar :=
    mul_le_mul_of_nonneg_left hξbar hroot
  have habs : |phiXi d ξ| ≤ |phiXi d ξ - 1| + 1 := by
    calc
      |phiXi d ξ| = |(phiXi d ξ - 1) + 1| := by ring_nf
      _ ≤ |phiXi d ξ - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |phiXi d ξ - 1| + 1 := by norm_num
  linarith only [hdiff, hfac, habs]

/-- A cap on the sphere average and a fixed radius give a common window for
all `ξ` in the parameter interval. -/
theorem q11_scaleS_pin_window {d : ℕ} (hd : 2 ≤ d)
    {ξ ξbar r Kpin L : ℝ} (hξ : 0 ≤ ξ) (hξbar : ξ ≤ ξbar)
    (hr : 0 < r)
    (hlog : |Real.log r| ≤ L)
    (z : Rd d) (g : DistRd d)
    (hcap : |sphereAvg g r z| ≤ Kpin) :
    let C := (1 + Real.sqrt (2 * d) * ξbar) * L + ξbar * Kpin
    Real.exp (-C) ≤ scaleS d ξ 1 r z g ∧
      scaleS d ξ 1 r z g ≤ Real.exp C := by
  let B : ℝ := 1 + Real.sqrt (2 * d) * ξbar
  let C : ℝ := B * L + ξbar * Kpin
  have hB : 0 ≤ B := by
    have hbar : 0 ≤ ξbar := hξ.trans hξbar
    dsimp [B]
    positivity
  have hbar : 0 ≤ ξbar := hξ.trans hξbar
  have hφ : |phiXi d ξ| ≤ B := q11_phi_abs_bound hd hξ hξbar
  have hterm1 : |phiXi d ξ * Real.log r| ≤ B * L := by
    rw [abs_mul]
    exact mul_le_mul hφ hlog (abs_nonneg _) hB
  have hterm2 : |ξ * sphereAvg g r z| ≤ ξbar * Kpin := by
    rw [abs_mul, abs_of_nonneg hξ]
    exact mul_le_mul hξbar hcap (abs_nonneg _) hbar
  have harg : |phiXi d ξ * Real.log r + ξ * sphereAvg g r z| ≤ C :=
    (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
  have hlow : -C ≤ phiXi d ξ * Real.log r + ξ * sphereAvg g r z :=
    (neg_le_of_abs_le harg)
  have hhi : phiXi d ξ * Real.log r + ξ * sphereAvg g r z ≤ C :=
    (le_of_abs_le harg)
  change Real.exp (-C) ≤ scaleS d ξ 1 r z g ∧
    scaleS d ξ 1 r z g ≤ Real.exp C
  rw [scaleS_eq_exp d ξ 1 hr]
  simpa only [one_mul] using
    (show Real.exp (-C) ≤ Real.exp (phiXi d ξ * Real.log r + ξ * sphereAvg g r z) ∧
      Real.exp (phiXi d ξ * Real.log r + ξ * sphereAvg g r z) ≤ Real.exp C from
      ⟨Real.exp_le_exp.mpr hlow, Real.exp_le_exp.mpr hhi⟩)

/-- A finite list of trial radii has one deterministic log-radius bound. -/
theorem q11_trial_log_bound (L : ℝ) (Ntr : ℕ)
    (j : Fin Ntr) :
    |Real.log (seedTrialRadius L j)| ≤
      ∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)| := by
  exact Finset.single_le_sum
    (fun i _ => abs_nonneg (Real.log (seedTrialRadius L i)))
    (Finset.mem_range.mpr j.isLt)

def q11TrialLambda (d : ℕ) (ξbar L Kpin : ℝ) (Ntr : ℕ) : ℝ :=
  Real.exp ((1 + Real.sqrt (2 * d) * ξbar) *
    (∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)|) + ξbar * Kpin)

theorem q11_trialLambda_one_le {d : ℕ} {ξbar Kpin : ℝ}
    (hξbar : 0 ≤ ξbar) (hKpin : 0 ≤ Kpin) (L : ℝ) (Ntr : ℕ) :
    1 ≤ q11TrialLambda d ξbar L Kpin Ntr := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range Ntr, |Real.log (seedTrialRadius L i)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB : 0 ≤ 1 + Real.sqrt (2 * d) * ξbar := by positivity
  unfold q11TrialLambda
  exact Real.one_le_exp (add_nonneg (mul_nonneg hB hsum) (mul_nonneg hξbar hKpin))

theorem q11_trial_scale_window {d : ℕ} (hd : 2 ≤ d)
    {ξ ξbar L Kpin : ℝ} (hξ : 0 ≤ ξ) (hξbar : ξ ≤ ξbar)
    (hL : 0 < L) (Ntr : ℕ) (j : Fin Ntr)
    (c : Rd d) (g : DistRd d)
    (hcap : |sphereAvg g (seedTrialRadius L j) c| ≤ Kpin) :
    (q11TrialLambda d ξbar L Kpin Ntr)⁻¹ ≤
      scaleS d ξ 1 (seedTrialRadius L j) c g ∧
      scaleS d ξ 1 (seedTrialRadius L j) c g ≤
        q11TrialLambda d ξbar L Kpin Ntr := by
  let Rlog : ℝ := ∑ i ∈ Finset.range Ntr,
    |Real.log (seedTrialRadius L i)|
  have h := q11_scaleS_pin_window hd hξ hξbar
    (seedTrialRadius_pos hL j) (q11_trial_log_bound L Ntr j) c g hcap
  dsimp only at h
  simpa only [q11TrialLambda, Real.exp_neg, Rlog] using h

end HigherDimLQGContinuity
