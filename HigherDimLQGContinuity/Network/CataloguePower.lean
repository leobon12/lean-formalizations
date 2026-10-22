import HigherDimLQGContinuity.Network.Catalogue
import HigherDimLQGContinuity.Network.CountPower
import HigherDimLQGContinuity.SiteCert.Count

/-! # The logarithmic site catalogue bound -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

namespace HigherDimLQGContinuity

/-- A constant depending only on the fixed site data. -/
def siteCatalogueCoeff {d : ℕ} (S : SiteData d) : ℝ :=
  (Nat.card S.Edge : ℝ) *
    (S.Ntr + 3 * (2 * (S.boxHalfSide / siteMuCoeff d + 3) + 1) ^ d +
      2 * (siteCN d + 1) + 2 * (siteCN d + 1) * 12 ^ d)

/-- The corrected display (4.9): the logarithm of the finite catalogue is
bounded by a fixed multiple of `ν^(-8d)`. -/
theorem labelCatalogue_log_card_power {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) :
    let C := siteConsts S Cnet v
    Real.log ((labelCatalogue S (labelCellCutoff S C.μ)
      (labelLeadCutoff C.ν) C.N C.μ C.ν C.r (Routing.gpC1 4)).card : ℝ) ≤
      siteCatalogueCoeff S * C.ν ^ (-(8 * d : ℝ)) := by
  let C := siteConsts S Cnet v
  let x := C.ν⁻¹
  let Kc := labelCellCutoff S C.μ
  let Kl := labelLeadCutoff C.ν
  let A := 2 * (S.boxHalfSide / siteMuCoeff d + 3) + 1
  let E := Nat.card S.Edge
  let J := (labelCatalogue S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)).card
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hx : 1 ≤ x := (one_le_inv₀ hν).2 hν1
  have hx0 : 0 ≤ x := by linarith
  have hμc : 0 < siteMuCoeff d := siteMuCoeff_pos hd
  have hL : 0 ≤ S.boxHalfSide := (S.boxHalfSide_pos hd).le
  have hKc := q4_cutoff_le_invpow hL hμc hν hν1
    (show siteMuCoeff d * C.ν ^ 8 ≤ C.μ from
      le_of_eq (siteConsts_mu_eq S Cnet v).symm)
  change (Kc : ℝ) ≤ (S.boxHalfSide / siteMuCoeff d + 3) * x ^ 8 at hKc
  have hKl := q4_cutoff_le_invpow
    (B := 5 / 2) (a := C.ν) (c := 1) (ν := C.ν) (k := 1)
    (by norm_num) (by norm_num) hν hν1 (by simp)
  have hKl' : (Kl : ℝ) ≤ (5 / 2 + 3) * x := by
    simpa only [Kl, labelLeadCutoff, x, div_one, pow_one] using hKl
  have hN := siteConsts_N_le_invpow S hd Cnet v hv
  change (C.N : ℝ) ≤ siteCN d * x ^ d at hN
  have hx8 : 1 ≤ x ^ 8 := one_le_pow₀ hx
  have hxd : 1 ≤ x ^ d := one_le_pow₀ hx
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCN : 0 ≤ siteCN d := (siteCN_pos d).le
  have hPbase : ((2 * Kc + 1 : ℕ) : ℝ) ≤ A * x ^ 8 := by
    have hcast : ((2 * Kc + 1 : ℕ) : ℝ) = 2 * (Kc : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    dsimp [A]
    nlinarith
  have hQbase : ((2 * Kl + 1 : ℕ) : ℝ) ≤ 12 * x := by
    have hcast : ((2 * Kl + 1 : ℕ) : ℝ) = 2 * (Kl : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [hKl']
  have hP : (((2 * Kc + 1 : ℕ) : ℝ) ^ d) ≤ A ^ d * x ^ (8 * d) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hPbase d
    rw [mul_pow, ← pow_mul] at h
    exact h
  have hQ : (((2 * Kl + 1 : ℕ) : ℝ) ^ d) ≤ 12 ^ d * x ^ d := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hQbase d
    rw [mul_pow] at h
    exact h
  have hN1 : (C.N : ℝ) + 1 ≤ (siteCN d + 1) * x ^ d := by
    nlinarith
  have hlog : Real.log (J : ℝ) ≤
      (E : ℝ) * (S.Ntr + 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d +
        2 * ((C.N : ℝ) + 1) +
        2 * ((C.N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d) := by
    apply q7b_log_card_le
    simpa only [J, Kc, Kl, E, labelIndex_card] using
      labelCatalogue_card_le S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)
  have hpowd : x ^ d ≤ x ^ (8 * d) := pow_le_pow_right₀ hx (by omega)
  have hpow2d : x ^ (2 * d) ≤ x ^ (8 * d) := pow_le_pow_right₀ hx (by omega)
  have hpow1 : 1 ≤ x ^ (8 * d) := one_le_pow₀ hx
  have hT0 : (S.Ntr : ℝ) ≤ S.Ntr * x ^ (8 * d) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hpow1
  have hT1 : 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d ≤
      3 * A ^ d * x ^ (8 * d) := by nlinarith
  have hT2 : 2 * ((C.N : ℝ) + 1) ≤
      2 * (siteCN d + 1) * x ^ (8 * d) := by
    have h := mul_le_mul_of_nonneg_left hpowd (by positivity : 0 ≤ 2 * (siteCN d + 1))
    nlinarith
  have hT3 : 2 * ((C.N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d ≤
      2 * (siteCN d + 1) * 12 ^ d * x ^ (8 * d) := by
    have hprod := mul_le_mul hN1 hQ (by positivity) (by positivity)
    have h2 : x ^ d * x ^ d = x ^ (2 * d) := by rw [← pow_add]; congr 1; omega
    have hcoef : 0 ≤ 2 * (siteCN d + 1) * 12 ^ d := by positivity
    have hsm := mul_le_mul_of_nonneg_left hpow2d hcoef
    nlinarith [hprod]
  have hE : 0 ≤ (E : ℝ) := Nat.cast_nonneg _
  have hsum : (S.Ntr : ℝ) + 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d +
      2 * ((C.N : ℝ) + 1) + 2 * ((C.N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d ≤
      (S.Ntr + 3 * A ^ d + 2 * (siteCN d + 1) +
        2 * (siteCN d + 1) * 12 ^ d) * x ^ (8 * d) := by
    nlinarith
  have hpow : x ^ (8 * d) = C.ν ^ (-(8 * d : ℝ)) := by
    dsimp [x]
    have hexp : (8 * d : ℝ) = ((8 * d : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_neg hν.le, hexp, Real.rpow_natCast, ← inv_pow]
  calc
    Real.log (J : ℝ) ≤ (E : ℝ) *
      (S.Ntr + 3 * ((2 * Kc + 1 : ℕ) : ℝ) ^ d +
        2 * ((C.N : ℝ) + 1) +
        2 * ((C.N : ℝ) + 1) * ((2 * Kl + 1 : ℕ) : ℝ) ^ d) := hlog
    _ ≤ siteCatalogueCoeff S * C.ν ^ (-(8 * d : ℝ)) := by
      rw [← hpow]
      change (E : ℝ) * _ ≤ (E : ℝ) *
        (S.Ntr + 3 * A ^ d + 2 * (siteCN d + 1) +
          2 * (siteCN d + 1) * 12 ^ d) * x ^ (8 * d)
      nlinarith [mul_le_mul_of_nonneg_left hsum hE]

end HigherDimLQGContinuity
