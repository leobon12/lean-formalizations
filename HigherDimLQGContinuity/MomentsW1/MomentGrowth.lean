import HigherDimLQGContinuity.MomentsW1.Envelope

/-! Absorbing the deterministic radius factor into one exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem wnMoment_growth {d : ℕ} {b p CZ D C₁ C₂ R : ℝ}
    (_hb : 0 < b) (_hp : 0 < p) (hCZ : 0 < CZ) (hR : 1 ≤ R)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbudget : 8*p*b ≤ Real.sqrt (2*d)) :
    let A₀ : ℝ := Real.sqrt (2*d)*CZ
    let A : ℝ := A₀+d
    let C : ℝ := Real.exp (p*Real.log D+A₀*Real.log 2)*(C₁+C₂)
    Real.exp (p*(Real.log D+b*CZ*Real.log (2+R)))*
      (C₁+C₂*(1+R)^d) ≤ C*(1+R)^A := by
  dsimp only
  let A₀ : ℝ := Real.sqrt (2*d)*CZ
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hpbc : p*b*CZ ≤ A₀ := by
    dsimp [A₀]
    have h := mul_le_mul_of_nonneg_right hbudget hCZ.le
    nlinarith
  have hlogR : 0 ≤ Real.log (2+R) := Real.log_nonneg (by linarith)
  have hlog1R : 0 ≤ Real.log (1+R) := Real.log_nonneg (by linarith)
  have hlogbound : Real.log (2+R) ≤ Real.log 2+Real.log (1+R) := by
    have hmain : Real.log (2+R) ≤ Real.log (2*(1+R)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : 1+R ≠ 0)] at hmain
    exact hmain
  have hdet : Real.exp (p*(Real.log D+b*CZ*Real.log (2+R))) ≤
      Real.exp (p*Real.log D+A₀*Real.log 2)*(1+R)^A₀ := by
    have harg : p*(Real.log D+b*CZ*Real.log (2+R)) ≤
        p*Real.log D+A₀*Real.log 2+A₀*Real.log (1+R) := by
      have h1 := mul_le_mul_of_nonneg_right hpbc hlogR
      have h2 := mul_le_mul_of_nonneg_left hlogbound hA₀
      nlinarith
    calc
      Real.exp (p*(Real.log D+b*CZ*Real.log (2+R))) ≤
          Real.exp (p*Real.log D+A₀*Real.log 2+A₀*Real.log (1+R)) :=
            Real.exp_le_exp.mpr harg
      _ = Real.exp (p*Real.log D+A₀*Real.log 2)*(1+R)^A₀ := by
        rw [Real.exp_add, Real.rpow_def_of_pos (by linarith : 0 < 1+R)]
        congr 1
        ring_nf
  have hbase : 1 ≤ (1+R)^d := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+R)
  have hsum : C₁+C₂*(1+R)^d ≤ (C₁+C₂)*(1+R)^d := by
    nlinarith [mul_nonneg hC₁ (sub_nonneg.mpr hbase)]
  have hsum0 : 0 ≤ C₁+C₂*(1+R)^d := by positivity
  have hdet0 : 0 ≤ Real.exp (p*Real.log D+A₀*Real.log 2) := (Real.exp_pos _).le
  calc
    Real.exp (p*(Real.log D+b*CZ*Real.log (2+R)))*(C₁+C₂*(1+R)^d)
        ≤ (Real.exp (p*Real.log D+A₀*Real.log 2)*(1+R)^A₀)*
            (C₁+C₂*(1+R)^d) := mul_le_mul_of_nonneg_right hdet hsum0
    _ ≤ (Real.exp (p*Real.log D+A₀*Real.log 2)*(1+R)^A₀)*
            ((C₁+C₂)*(1+R)^d) := by
          gcongr
    _ = (Real.exp (p*Real.log D+A₀*Real.log 2)*(C₁+C₂))*
          (1+R)^(A₀+d) := by
        rw [Real.rpow_add (by linarith : 0 < 1+R), Real.rpow_natCast]
        ring_nf

end HigherDimLQGContinuity
