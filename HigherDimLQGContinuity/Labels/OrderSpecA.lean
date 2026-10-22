import HigherDimLQGContinuity.Labels.OrderPoly

/-!
# The lead and separation inequalities of the explicit order
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem SiteData.boxHalfSide_le_one {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    S.boxHalfSide ≤ 1 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ √(d : ℝ) := Real.one_le_sqrt.mpr hdR
  have hδ : 0 < S.mesh.δm := S.mesh.δm_pos
  have hδsmall := S.mesh.δm_small
  have hL := S.boxHalfSide_le_half hd
  nlinarith [mul_le_mul_of_nonneg_right hsqrt hδ.le]

theorem siteConsts_r_le_box {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).r ≤ S.boxHalfSide / 160 := by
  change Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide
    (siteTCoeff S * v ^ siteTExponent S) ≤ S.boxHalfSide / 160
  exact Routing.leadR_le_L S.seed.A_ge S.seed.α_pos S.seed.α_le
    S.seed.β_pos S.seed.β_le (siteConsts_t₀_pos S Cnet v hv)
    (S.boxHalfSide_pos hd) (S.boxHalfSide_le_one hd)

theorem siteConsts_r_le_one {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).r ≤ 1 := by
  have hrL := siteConsts_r_le_box S hd Cnet v hv
  have hL := S.boxHalfSide_le_one hd
  linarith

theorem siteConsts_N_bound {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v)
    (hr1 : (siteConsts S Cnet v).r ≤ 1) :
    2 * ((siteConsts S Cnet v).N : ℝ) + 5 ≤
      siteCN d * (siteConsts S Cnet v).r⁻¹ ^ d := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hN := Routing.leadN_le (d := d) hr hr1
  change (C.N : ℝ) ≤ ((4 * √(d : ℝ) + 2) ^ d + 5) * C.r⁻¹ ^ d at hN
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ √(d : ℝ) := Real.one_le_sqrt.mpr hdR
  have hbase : 4 * √(d : ℝ) + 2 ≤ 6 * √(d : ℝ) := by nlinarith
  have hpow : (4 * √(d : ℝ) + 2) ^ d ≤ (6 * √(d : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have hri : 1 ≤ C.r⁻¹ := (one_le_inv₀ hr).2 hr1
  have hripow : 1 ≤ C.r⁻¹ ^ d := one_le_pow₀ hri
  have hcoeff : (4 * √(d : ℝ) + 2) ^ d + 5 ≤
      (6 * √(d : ℝ)) ^ d + 5 := by linarith
  have hcoeffmul := mul_le_mul_of_nonneg_right hcoeff
    (pow_nonneg (inv_nonneg.mpr hr.le) d)
  change 2 * (C.N : ℝ) + 5 ≤ siteCN d * C.r⁻¹ ^ d
  unfold siteCN
  nlinarith [mul_le_mul_of_nonneg_left hripow (by norm_num : (0 : ℝ) ≤ 5)]

theorem siteConsts_ν_le_rpower {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).ν ≤ siteNuCoeff S *
      (siteConsts S Cnet v).r ^ (3 * d + 2) := by
  have hν := siteConsts_ν_le_barν S hd Cnet v hv
  have hc : 0 ≤ siteNuCoeff S := (siteNuCoeff_pos S (by omega)).le
  calc
    (siteConsts S Cnet v).ν ≤ (siteConsts S Cnet v).barν := hν
    _ ≤ siteNuCoeff S * (siteConsts S Cnet v).r ^ (3 * d + 2) := by
      change siteNuCoeff S * min ((siteConsts S Cnet v).r ^ (3 * d + 2))
        (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
          ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE))) ≤ _
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hc

theorem siteConsts_ν_le_vD {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).ν ≤ siteNuCoeff S *
      (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) := by
  have hν := siteConsts_ν_le_barν S hd Cnet v hv
  have hc : 0 ≤ siteNuCoeff S := (siteNuCoeff_pos S (by omega)).le
  calc
    (siteConsts S Cnet v).ν ≤ (siteConsts S Cnet v).barν := hν
    _ ≤ siteNuCoeff S * (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) := by
      change siteNuCoeff S * min ((siteConsts S Cnet v).r ^ (3 * d + 2))
        (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
          ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE))) ≤ _
      exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hc

theorem siteConsts_ν_le_vE {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).ν ≤ siteNuCoeff S *
      (v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE) := by
  have hν := siteConsts_ν_le_barν S hd Cnet v hv
  have hc : 0 ≤ siteNuCoeff S := (siteNuCoeff_pos S (by omega)).le
  calc
    (siteConsts S Cnet v).ν ≤ (siteConsts S Cnet v).barν := hν
    _ ≤ siteNuCoeff S * (v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE) := by
      change siteNuCoeff S * min ((siteConsts S Cnet v).r ^ (3 * d + 2))
        (min ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s))
          ((v * S.seed.d₀ / (1000 * S.seed.HE)) ^ (1 / S.seed.sE))) ≤ _
      exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hc

theorem siteConsts_ν_le_r_div {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v)
    (hr1 : (siteConsts S Cnet v).r ≤ 1) :
    (siteConsts S Cnet v).ν ≤ (siteConsts S Cnet v).r / (800 * d) := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hpow : C.r ^ (3 * d + 2) ≤ C.r :=
    pow_le_of_le_one hr.le hr1 (by omega)
  have hc : siteNuCoeff S ≤ 1 / (800 * d : ℝ) := by
    unfold siteNuCoeff
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hc0 : 0 ≤ siteNuCoeff S := (siteNuCoeff_pos S (by omega)).le
  have hdR : 0 < (800 * d : ℝ) := by
    have : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    positivity
  calc
    C.ν ≤ siteNuCoeff S * C.r ^ (3 * d + 2) :=
      siteConsts_ν_le_rpower S hd Cnet v hv
    _ ≤ (1 / (800 * d : ℝ)) * C.r := by
      exact (mul_le_mul_of_nonneg_left hpow hc0).trans
        (mul_le_mul_of_nonneg_right hc hr.le)
    _ = C.r / (800 * d) := by ring

theorem siteConsts_lead_short {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v)
    (hr1 : (siteConsts S Cnet v).r ≤ 1) :
    √(d : ℝ) * (siteConsts S Cnet v).ν ≤ (siteConsts S Cnet v).r ∧
      (siteConsts S Cnet v).g ≤ (siteConsts S Cnet v).r / 8 := by
  let C := siteConsts S Cnet v
  have hν := siteConsts_ν_le_r_div S hd Cnet v hv hr1
  have hνpos : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : √(d : ℝ) ≤ d := (Real.sqrt_le_self_iff).2 (Or.inr hdR)
  have hrootmul := mul_le_mul_of_nonneg_right hsqrt hνpos.le
  have hden : 0 < (800 * d : ℝ) := by positivity
  have hνmul : C.ν * (800 * d : ℝ) ≤ C.r := (le_div_iff₀ hden).1 hν
  constructor
  · nlinarith
  · change 100 * d * C.ν ≤ C.r / 8
    nlinarith

theorem siteConsts_lead_grid_constraint {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v)
    (hr1 : (siteConsts S Cnet v).r ≤ 1) :
    (siteConsts S Cnet v).ν ≤ Routing.gpC0 d *
      ((siteConsts S Cnet v).r / (4 * √(d : ℝ))) /
        (2 * ((siteConsts S Cnet v).N : ℝ) + 5) ^ 3 := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hd1 : 1 ≤ d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : 0 < √(d : ℝ) := Real.sqrt_pos.2 hdR
  have hc0 : 0 < Routing.gpC0 d := Routing.gpC0_pos hd1
  have hCN : 0 < siteCN d := siteCN_pos d
  have hU : 0 < 2 * (C.N : ℝ) + 5 := by positivity
  have hN := siteConsts_N_bound S hd Cnet v hv hr1
  have hCoeff : siteNuCoeff S ≤ Routing.gpC0 d /
      (4 * √(d : ℝ) * (siteCN d) ^ 3) := by
    unfold siteNuCoeff
    exact min_le_left _ _
  have hpower : C.r ^ (3 * d + 2) * (C.r⁻¹ ^ d) ^ 3 = C.r ^ 2 := by
    have hpow : C.r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
    have hexp : 3 * d + 2 = d * 3 + 2 := by omega
    rw [hexp, pow_add, pow_mul, inv_pow]
    field_simp
  have hνbound : C.ν ≤
      (Routing.gpC0 d / (4 * √(d : ℝ) * (siteCN d) ^ 3)) *
        C.r ^ (3 * d + 2) := by
    exact (siteConsts_ν_le_rpower S hd Cnet v hv).trans
      (mul_le_mul_of_nonneg_right hCoeff (pow_nonneg hr.le _))
  have hUcube : (2 * (C.N : ℝ) + 5) ^ 3 ≤
      (siteCN d * C.r⁻¹ ^ d) ^ 3 :=
    pow_le_pow_left₀ hU.le hN 3
  have hright : 0 ≤ (siteCN d * C.r⁻¹ ^ d) ^ 3 := by positivity
  have hmain : C.ν * (2 * (C.N : ℝ) + 5) ^ 3 ≤
      Routing.gpC0 d * C.r / (4 * √(d : ℝ)) := by
    calc
      C.ν * (2 * (C.N : ℝ) + 5) ^ 3 ≤
          C.ν * (siteCN d * C.r⁻¹ ^ d) ^ 3 :=
        mul_le_mul_of_nonneg_left hUcube hν.le
      _ ≤ ((Routing.gpC0 d / (4 * √(d : ℝ) * (siteCN d) ^ 3)) *
          C.r ^ (3 * d + 2)) * (siteCN d * C.r⁻¹ ^ d) ^ 3 :=
        mul_le_mul_of_nonneg_right hνbound hright
      _ = Routing.gpC0 d * C.r ^ 2 / (4 * √(d : ℝ)) := by
        rw [mul_pow]
        calc
          _ = (Routing.gpC0 d / (4 * √(d : ℝ) * (siteCN d) ^ 3) *
                (siteCN d) ^ 3) *
                (C.r ^ (3 * d + 2) * (C.r⁻¹ ^ d) ^ 3) := by ring
          _ = Routing.gpC0 d * C.r ^ 2 / (4 * √(d : ℝ)) := by
            rw [hpower]
            field_simp
      _ ≤ Routing.gpC0 d * C.r / (4 * √(d : ℝ)) := by
        have hr2 : C.r ^ 2 ≤ C.r := sq_le hr.le hr1
        apply (div_le_div_iff₀ (by positivity : 0 < 4 * √(d : ℝ))
          (by positivity : 0 < 4 * √(d : ℝ))).2
        nlinarith [mul_le_mul_of_nonneg_left hr2 hc0.le]
  change C.ν ≤ Routing.gpC0 d * (C.r / (4 * √(d : ℝ))) /
    (2 * (C.N : ℝ) + 5) ^ 3
  apply (le_div_iff₀ (pow_pos hU 3)).2
  calc
    C.ν * (2 * (C.N : ℝ) + 5) ^ 3 ≤
        Routing.gpC0 d * C.r / (4 * √(d : ℝ)) := hmain
    _ = Routing.gpC0 d * (C.r / (4 * √(d : ℝ))) := by ring

theorem siteConsts_omega_bounds {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).ω ≤
      (siteConsts S Cnet v).r / (8 * √(d : ℝ)) ∧
    (siteConsts S Cnet v).ω ≤ Routing.gpC1 4 *
      (siteConsts S Cnet v).ν ^ 3 / 8 := by
  let C := siteConsts S Cnet v
  have hr1 := siteConsts_r_le_one S hd Cnet v hv
  have hνr := siteConsts_ν_le_r_div S hd Cnet v hv hr1
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hcω : 0 < siteOmegaCoeff d := siteOmegaCoeff_pos d (by omega)
  have hc1 : 0 < Routing.gpC1 4 :=
    Routing.gpC1_pos (show (0 : ℝ) ≤ 4 by norm_num)
  have hνr' : C.ν ≤ C.r := by
    have hden : 0 < (800 * d : ℝ) := by positivity
    have hmul := (le_div_iff₀ hden).1 hνr
    nlinarith
  have hν4ν : C.ν ^ 4 ≤ C.ν := pow_le_of_le_one hν.le hν1 (by norm_num)
  have hν4ν3 : C.ν ^ 4 ≤ C.ν ^ 3 :=
    pow_le_pow_of_le_one hν.le hν1 (by norm_num)
  have hcoeffR : siteOmegaCoeff d ≤ 1 / (8 * √(d : ℝ)) := by
    unfold siteOmegaCoeff
    exact min_le_right _ _
  have hcoeffC : siteOmegaCoeff d ≤ Routing.gpC1 4 / 8 := by
    unfold siteOmegaCoeff
    exact min_le_left _ _
  constructor
  · change siteOmegaCoeff d * C.ν ^ 4 ≤ C.r / (8 * √(d : ℝ))
    calc
      siteOmegaCoeff d * C.ν ^ 4 ≤ (1 / (8 * √(d : ℝ))) * C.r :=
        (mul_le_mul_of_nonneg_left (hν4ν.trans hνr') hcω.le).trans
          (mul_le_mul_of_nonneg_right hcoeffR hr.le)
      _ = C.r / (8 * √(d : ℝ)) := by ring
  · change siteOmegaCoeff d * C.ν ^ 4 ≤ Routing.gpC1 4 * C.ν ^ 3 / 8
    calc
      siteOmegaCoeff d * C.ν ^ 4 ≤ (Routing.gpC1 4 / 8) * C.ν ^ 3 :=
        (mul_le_mul_of_nonneg_left hν4ν3 hcω.le).trans
          (mul_le_mul_of_nonneg_right hcoeffC (pow_nonneg hν.le 3))
      _ = Routing.gpC1 4 * C.ν ^ 3 / 8 := by ring

theorem siteConsts_cell_radius_bound {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) :
    (√(d : ℝ) / 2) * (siteConsts S Cnet v).μ ≤
      (siteConsts S Cnet v).ω / 4 := by
  let C := siteConsts S Cnet v
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ √(d : ℝ) := Real.one_le_sqrt.mpr hdR
  have hsqrtpos : 0 < √(d : ℝ) := by linarith
  have hcω : 0 < siteOmegaCoeff d := siteOmegaCoeff_pos d (by omega)
  have hcω1 : siteOmegaCoeff d ≤ 1 := by
    have h := min_le_right (Routing.gpC1 4 / 8) (1 / (8 * √(d : ℝ)))
    unfold siteOmegaCoeff
    apply h.trans
    have hden : (1 : ℝ) ≤ 8 * √(d : ℝ) := by nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 8 * √(d : ℝ))).2
    simpa only [one_mul] using hden
  have hωpos : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    positivity
  have hω1 : C.ω ≤ 1 := by
    change siteOmegaCoeff d * C.ν ^ 4 ≤ 1
    have hν4 : C.ν ^ 4 ≤ 1 := pow_le_one₀ hν.le hν1
    nlinarith [mul_le_mul hcω1 hν4 (pow_nonneg hν.le 4)
      (by norm_num : (0 : ℝ) ≤ 1)]
  have hω2 : C.ω ^ 2 ≤ C.ω := sq_le hωpos.le hω1
  have heq : (√(d : ℝ) / 2) * C.μ = C.ω ^ 2 / 4 := by
    change (√(d : ℝ) / 2) * (C.ω ^ 2 / (2 * √(d : ℝ))) = C.ω ^ 2 / 4
    field_simp
    norm_num
  rw [heq]
  linarith

theorem siteConsts_delta_bounds {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).δsep ≤
      min ((siteConsts S Cnet v).r / 2)
        (min ((siteConsts S Cnet v).g / 2)
          (min (Routing.gpC1 4 * (siteConsts S Cnet v).ν ^ 3 / 2)
            (S.boxHalfSide / 2))) := by
  let C := siteConsts S Cnet v
  have hr1 := siteConsts_r_le_one S hd Cnet v hv
  have hνr := siteConsts_ν_le_r_div S hd Cnet v hv hr1
  have hrL := siteConsts_r_le_box S hd Cnet v hv
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hν3ν : C.ν ^ 3 ≤ C.ν := pow_le_of_le_one hν.le hν1 (by norm_num)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hden : 0 < (800 * d : ℝ) := by positivity
  have hνmul : C.ν * (800 * d : ℝ) ≤ C.r := (le_div_iff₀ hden).1 hνr
  have hν3r : C.ν ^ 3 ≤ C.r := by nlinarith
  have hc1 : Routing.gpC1 4 = 1 / 100 := by norm_num [Routing.gpC1]
  have hδ : C.δsep = C.ν ^ 3 / 400 := by
    change Routing.gpC1 4 * C.ν ^ 3 / 4 = C.ν ^ 3 / 400
    rw [hc1]
    ring
  have hg : C.g = 100 * d * C.ν := rfl
  rw [hδ, hg, hc1]
  apply le_min
  · linarith
  apply le_min
  · nlinarith [pow_nonneg hν.le 3]
  apply le_min
  · nlinarith [pow_nonneg hν.le 3]
  · nlinarith [S.boxHalfSide_pos hd]

/-- Clause (a) of the corrected order lemma, with one fixed tolerance threshold. -/
theorem siteConsts_spec_a {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    ∃ vsite : ℝ, 0 < vsite ∧ vsite ≤ 1 / 100 ∧
      ∀ v, 0 < v → v ≤ vsite →
        let C := siteConsts S Cnet v
        C.ν ≤ Routing.gpC0 d * (C.r / (4 * √(d : ℝ))) /
          (2 * (C.N : ℝ) + 5) ^ 3 ∧
        √(d : ℝ) * C.ν ≤ C.r ∧ C.g ≤ C.r / 8 ∧
        C.ω ≤ min (C.r / (8 * √(d : ℝ)))
          (Routing.gpC1 4 * C.ν ^ 3 / 8) ∧
        (√(d : ℝ) / 2) * C.μ ≤ C.ω / 4 ∧
        C.δsep ≤ min (C.r / 2)
          (min (C.g / 2)
            (min (Routing.gpC1 4 * C.ν ^ 3 / 2) (S.boxHalfSide / 2))) ∧
        2 * C.g + 8 * C.ς < S.seedMin / 4 := by
  have hsmin : 0 < S.seedMin := by
    unfold SiteData.seedMin
    have hL := S.boxHalfSide_pos hd
    positivity
  obtain ⟨εg, hεg, hεg1, hgsmall⟩ :=
    sitePowerBounds_small (siteConsts_g_power S hd Cnet)
      (siteNuExponent_pos S) (by positivity : 0 < S.seedMin / 32)
  obtain ⟨ες, hες, hες1, hςsmall⟩ :=
    sitePowerBounds_small (siteConsts_ς_power S hd Cnet hCnet)
      (siteVarsigmaExponent_pos S) (by positivity : 0 < S.seedMin / 128)
  let vsite := min (1 / 100 : ℝ) (min εg ες)
  have hvsite : 0 < vsite := by
    dsimp [vsite]
    exact lt_min (by norm_num) (lt_min hεg hες)
  refine ⟨vsite, hvsite, ?_, ?_⟩
  · exact min_le_left _ _
  intro v hv hvsite'
  have hvεg : v ≤ εg := hvsite'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hvες : v ≤ ες := hvsite'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgs : (siteConsts S Cnet v).g ≤ S.seedMin / 32 := hgsmall v hv hvεg
  have hςs : (siteConsts S Cnet v).ς ≤ S.seedMin / 128 := hςsmall v hv hvες
  let C := siteConsts S Cnet v
  have hr1 := siteConsts_r_le_one S hd Cnet v hv
  have hshort := siteConsts_lead_short S hd Cnet v hv hr1
  have hω := siteConsts_omega_bounds S hd Cnet v hv
  have hδ := siteConsts_delta_bounds S hd Cnet v hv
  change C.ν ≤ Routing.gpC0 d * (C.r / (4 * √(d : ℝ))) /
      (2 * (C.N : ℝ) + 5) ^ 3 ∧
    √(d : ℝ) * C.ν ≤ C.r ∧ C.g ≤ C.r / 8 ∧
    C.ω ≤ min (C.r / (8 * √(d : ℝ)))
      (Routing.gpC1 4 * C.ν ^ 3 / 8) ∧
    (√(d : ℝ) / 2) * C.μ ≤ C.ω / 4 ∧
    C.δsep ≤ min (C.r / 2)
      (min (C.g / 2)
        (min (Routing.gpC1 4 * C.ν ^ 3 / 2) (S.boxHalfSide / 2))) ∧
    2 * C.g + 8 * C.ς < S.seedMin / 4
  refine ⟨siteConsts_lead_grid_constraint S hd Cnet v hv hr1,
    hshort.1, hshort.2, le_min hω.1 hω.2,
    siteConsts_cell_radius_bound S hd Cnet v,
    hδ, ?_⟩
  linarith

end HigherDimLQGContinuity
