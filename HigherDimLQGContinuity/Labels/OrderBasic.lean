import HigherDimLQGContinuity.Labels.Order

/-!
# Elementary bounds for the explicit site constants
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem sitePortDenom_pos {d : ℕ} (S : SiteData d) (hd : 1 ≤ d) :
    0 < sitePortDenom S := by
  unfold sitePortDenom
  positivity

theorem siteTExponent_pos {d : ℕ} (S : SiteData d) : 0 < siteTExponent S := by
  unfold siteTExponent
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem siteTCoeff_pos {d : ℕ} (S : SiteData d) : 0 < siteTCoeff S := by
  unfold siteTCoeff
  have hA : 0 < S.seed.A := by linarith [S.seed.A_ge]
  have hα : 0 < S.seed.α := S.seed.α_pos
  have hs : 0 < S.s := S.s_pos
  have hd0 : 0 < S.seed.d₀ := S.seed.d₀_pos
  have hH : 0 < S.Hup := by linarith [S.Hup_ge]
  have hℓ : 0 < S.seed.ℓ₁ := lt_of_lt_of_le S.seed.ℓ₀_pos S.seed.ℓ₀_le_ℓ₁
  positivity

theorem siteCS_pos {s : ℝ} (hs : 0 < s) : 0 < siteCS s := by
  unfold siteCS
  have h2 : 1 < (2 : ℝ) ^ s := Real.one_lt_rpow (by norm_num) hs
  positivity

theorem siteCN_pos (d : ℕ) : 0 < siteCN d := by
  unfold siteCN
  positivity

theorem siteNuCoeff_pos {d : ℕ} (S : SiteData d) (hd : 1 ≤ d) :
    0 < siteNuCoeff S := by
  unfold siteNuCoeff
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < √(d : ℝ) := Real.sqrt_pos.2 hdR
  have hC := siteCN_pos d
  have hCsE := siteCS_pos S.seed.sE_pos
  have hc0 := Routing.gpC0_pos hd
  positivity

theorem siteOmegaCoeff_pos (d : ℕ) (hd : 1 ≤ d) : 0 < siteOmegaCoeff d := by
  unfold siteOmegaCoeff
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < √(d : ℝ) := Real.sqrt_pos.2 hdR
  have hc1 := Routing.gpC1_pos (show (0 : ℝ) ≤ 4 by norm_num)
  positivity

theorem siteData_eps0_pos {d : ℕ} (S : SiteData d) :
    0 < siteEps0 S.mc S.Hlo := by
  have hH : 0 < S.Hlo := by linarith [S.Hlo_ge]
  have hmc := S.mc_pos
  have hinv : 0 < S.Hlo⁻¹ := inv_pos.mpr hH
  unfold siteEps0 siteBtrig siteAout
  positivity

theorem siteConsts_t₀_pos {d : ℕ} (S : SiteData d) (Cnet v : ℝ) (hv : 0 < v) :
    0 < (siteConsts S Cnet v).t₀ := by
  change 0 < siteTCoeff S * v ^ siteTExponent S
  exact mul_pos (siteTCoeff_pos S) (Real.rpow_pos_of_pos hv _)

theorem siteConsts_r_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    0 < (siteConsts S Cnet v).r := by
  change 0 < Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide
    (siteTCoeff S * v ^ siteTExponent S)
  exact Routing.leadR_pos S.seed.A_ge (siteConsts_t₀_pos S Cnet v hv)
    (S.boxHalfSide_pos hd)

theorem siteConsts_barν_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    0 < (siteConsts S Cnet v).barν := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hd1 : 1 ≤ d := by omega
  have hcν : 0 < siteNuCoeff S := siteNuCoeff_pos S hd1
  have hbaseD : 0 < v * S.seed.d₀ / (1000 * S.Hup) := by
    have hH : 0 < S.Hup := by linarith [S.Hup_ge]
    have hd0 := S.seed.d₀_pos
    positivity
  have hbaseE : 0 < v * S.seed.d₀ / (1000 * S.seed.HE) := by
    have hHE : 0 < S.seed.HE := by linarith [S.seed.HE_ge]
    have hd0 := S.seed.d₀_pos
    positivity
  have hmin : 0 < min (C.r ^ (3 * d + 2))
      (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
        ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE))) := by
    exact lt_min (pow_pos hr _) (lt_min (Real.rpow_pos_of_pos hbaseD _)
      (Real.rpow_pos_of_pos hbaseE _))
  change 0 < siteNuCoeff S * min (C.r ^ (3 * d + 2))
    (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
      ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE)))
  exact mul_pos hcν hmin

theorem siteConsts_Mν_pos {d : ℕ} (S : SiteData d) (Cnet v : ℝ) :
    0 < (siteConsts S Cnet v).Mν := by
  change 0 < max 1 ⌈((sitePortDenom S : ℝ) *
    (siteConsts S Cnet v).barν)⁻¹⌉₊
  exact lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)

theorem siteConsts_ν_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) : 0 < (siteConsts S Cnet v).ν := by
  change 0 < 1 / ((sitePortDenom S : ℝ) * (siteConsts S Cnet v).Mν)
  have hq : 0 < (sitePortDenom S : ℝ) := by exact_mod_cast sitePortDenom_pos S (by omega)
  have hM : 0 < ((siteConsts S Cnet v).Mν : ℝ) := by
    exact_mod_cast siteConsts_Mν_pos S Cnet v
  positivity

theorem siteConsts_ν_le_one {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) : (siteConsts S Cnet v).ν ≤ 1 := by
  have hqN : 1 ≤ sitePortDenom S := sitePortDenom_pos S (by omega)
  have hMN : 1 ≤ (siteConsts S Cnet v).Mν := siteConsts_Mν_pos S Cnet v
  have hq : (1 : ℝ) ≤ sitePortDenom S := by exact_mod_cast hqN
  have hM : (1 : ℝ) ≤ (siteConsts S Cnet v).Mν := by exact_mod_cast hMN
  change 1 / ((sitePortDenom S : ℝ) * (siteConsts S Cnet v).Mν) ≤ 1
  apply (div_le_iff₀ (by positivity : 0 < (sitePortDenom S : ℝ) *
    (siteConsts S Cnet v).Mν)).2
  nlinarith [mul_le_mul hq hM (by norm_num : (0 : ℝ) ≤ 1)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hq)]

theorem siteConsts_ν_le_barν {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).ν ≤ (siteConsts S Cnet v).barν := by
  let C := siteConsts S Cnet v
  have hbar : 0 < C.barν := siteConsts_barν_pos S hd Cnet v hv
  have hq : 0 < (sitePortDenom S : ℝ) := by
    exact_mod_cast sitePortDenom_pos S (by omega)
  have hM : 0 < (C.Mν : ℝ) := by exact_mod_cast siteConsts_Mν_pos S Cnet v
  have hceil : (((sitePortDenom S : ℝ) * C.barν)⁻¹) ≤ (C.Mν : ℝ) := by
    change (((sitePortDenom S : ℝ) * C.barν)⁻¹) ≤
      (max 1 ⌈((sitePortDenom S : ℝ) * C.barν)⁻¹⌉₊ : ℕ)
    calc
      _ ≤ ((⌈((sitePortDenom S : ℝ) * C.barν)⁻¹⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast le_max_right 1 _
  have hmul : 1 ≤ ((sitePortDenom S : ℝ) * C.barν) * (C.Mν : ℝ) := by
    have hqbar : 0 < (sitePortDenom S : ℝ) * C.barν := mul_pos hq hbar
    nlinarith [mul_le_mul_of_nonneg_left hceil hqbar.le,
      mul_inv_cancel₀ hqbar.ne']
  change 1 / ((sitePortDenom S : ℝ) * (C.Mν : ℝ)) ≤ C.barν
  apply (div_le_iff₀ (mul_pos hq hM)).2
  nlinarith

/-- The denominator selected in (O3) is the least positive integer giving a
grid spacing at most `barν`. -/
theorem siteConsts_Mν_least {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) (M : ℕ) (hM : 0 < M)
    (hsmall : 1 / ((sitePortDenom S : ℝ) * M) ≤
      (siteConsts S Cnet v).barν) :
    (siteConsts S Cnet v).Mν ≤ M := by
  let C := siteConsts S Cnet v
  have hbar : 0 < C.barν := siteConsts_barν_pos S hd Cnet v hv
  have hq : 0 < (sitePortDenom S : ℝ) := by
    exact_mod_cast sitePortDenom_pos S (by omega)
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hqbar : 0 < (sitePortDenom S : ℝ) * C.barν := mul_pos hq hbar
  have hqM : 0 < (sitePortDenom S : ℝ) * M := mul_pos hq hMR
  have hprod : 1 ≤ ((sitePortDenom S : ℝ) * C.barν) * M := by
    have hs := (div_le_iff₀ hqM).1 hsmall
    nlinarith
  have hinv : (((sitePortDenom S : ℝ) * C.barν)⁻¹) ≤ (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hqbar.le)
    nlinarith [inv_mul_cancel₀ hqbar.ne']
  change max 1 ⌈((sitePortDenom S : ℝ) * C.barν)⁻¹⌉₊ ≤ M
  apply max_le (by omega)
  exact Nat.ceil_le.mpr hinv

theorem siteConsts_barν_div_le_ν {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).barν /
      (1 + (sitePortDenom S : ℝ) * (siteConsts S Cnet v).barν) ≤
        (siteConsts S Cnet v).ν := by
  let C := siteConsts S Cnet v
  have hbar : 0 < C.barν := siteConsts_barν_pos S hd Cnet v hv
  have hq : 0 < (sitePortDenom S : ℝ) := by
    exact_mod_cast sitePortDenom_pos S (by omega)
  have hqbar : 0 < (sitePortDenom S : ℝ) * C.barν := mul_pos hq hbar
  have hM : 0 < (C.Mν : ℝ) := by exact_mod_cast siteConsts_Mν_pos S Cnet v
  have hMle : (C.Mν : ℝ) ≤ 1 + (((sitePortDenom S : ℝ) * C.barν)⁻¹) := by
    change ((max 1 ⌈((sitePortDenom S : ℝ) * C.barν)⁻¹⌉₊ : ℕ) : ℝ) ≤
      1 + (((sitePortDenom S : ℝ) * C.barν)⁻¹)
    rw [Nat.cast_max]
    apply max_le
    · linarith [inv_pos.mpr hqbar]
    · simpa only [add_comm] using
        (Nat.ceil_lt_add_one (inv_pos.mpr hqbar).le).le
  have hden : 0 < 1 + (sitePortDenom S : ℝ) * C.barν := by positivity
  have hmul : (sitePortDenom S : ℝ) * (C.Mν : ℝ) * C.barν ≤
      1 + (sitePortDenom S : ℝ) * C.barν := by
    have h := mul_le_mul_of_nonneg_left hMle hqbar.le
    nlinarith [mul_inv_cancel₀ hqbar.ne']
  change C.barν / (1 + (sitePortDenom S : ℝ) * C.barν) ≤
    1 / ((sitePortDenom S : ℝ) * (C.Mν : ℝ))
  apply (div_le_div_iff₀ hden (mul_pos hq hM)).2
  nlinarith

end HigherDimLQGContinuity
