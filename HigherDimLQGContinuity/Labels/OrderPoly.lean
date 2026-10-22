import HigherDimLQGContinuity.Labels.OrderVarsigma

/-!
# Shared polynomial bounds for the ten small site scales
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem siteConsts_g_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).g) (siteNuExponent S) := by
  have hc : 0 < (100 * d : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    positivity
  have h := sitePowerBounds_scale (siteConsts_ν_power S hd Cnet) hc
  convert h using 1
  ext v
  change (100 * d : ℝ) * (siteConsts S Cnet v).ν =
    (100 * d : ℝ) * (siteConsts S Cnet v).ν
  rfl

theorem siteConsts_ω_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).ω) (siteNuExponent S * 4) := by
  have hc := siteOmegaCoeff_pos d (by omega : 1 ≤ d)
  have h := sitePowerBounds_scale
    (sitePowerBounds_rpow (siteConsts_ν_power S hd Cnet) (by norm_num : (0 : ℝ) < 4)) hc
  convert h using 1
  ext v
  change siteOmegaCoeff d * (siteConsts S Cnet v).ν ^ (4 : ℕ) =
    siteOmegaCoeff d * (siteConsts S Cnet v).ν ^ (4 : ℝ)
  exact congrArg (fun z : ℝ => siteOmegaCoeff d * z)
    (Real.rpow_natCast (siteConsts S Cnet v).ν 4).symm

theorem siteConsts_μ_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).μ) (siteNuExponent S * 8) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hden : 0 < 2 * √(d : ℝ) := by positivity
  have h := sitePowerBounds_div_const
    (sitePowerBounds_rpow (siteConsts_ω_power S hd Cnet) (by norm_num : (0 : ℝ) < 2)) hden
  have hq : (siteNuExponent S * 4) * 2 = siteNuExponent S * 8 := by ring
  rw [hq] at h
  convert h using 1
  ext v
  change (siteConsts S Cnet v).ω ^ (2 : ℕ) / (2 * √(d : ℝ)) =
    (siteConsts S Cnet v).ω ^ (2 : ℝ) / (2 * √(d : ℝ))
  exact congrArg (fun z : ℝ => z / (2 * √(d : ℝ)))
    (Real.rpow_natCast (siteConsts S Cnet v).ω 2).symm

theorem siteConsts_δsep_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).δsep)
      (siteNuExponent S * 3) := by
  have h := sitePowerBounds_comp siteDeltaFromNu_power
    (siteConsts_ν_power S hd Cnet) (by norm_num : (0 : ℝ) < 3)
    (fun v _ _ => ⟨siteConsts_ν_pos S hd Cnet v,
      siteConsts_ν_le_one S hd Cnet v⟩)
  change SitePowerBounds (fun v => siteDeltaFromNu (siteConsts S Cnet v).ν)
    (siteNuExponent S * 3)
  exact h

theorem siteConsts_cseed_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).cseed)
      (siteNuExponent S * siteThetaExponent S) := by
  have hc : 0 < S.seed.d₀ / 2 := by positivity [S.seed.d₀_pos]
  have h := sitePowerBounds_scale (siteConsts_θ_power S hd Cnet hCnet) hc
  convert h using 1
  ext v
  change (siteConsts S Cnet v).θ * S.seed.d₀ / 2 =
    S.seed.d₀ / 2 * (siteConsts S Cnet v).θ
  ring

/-- The ten small scales in the generic polynomial clause, in blueprint order. -/
def siteSmallScale {d : ℕ} (S : SiteData d) (Cnet v : ℝ) : Fin 10 → ℝ :=
  let C := siteConsts S Cnet v
  ![C.t₀, C.r, C.ν, C.g, C.ω, C.μ, C.δsep, C.θ, C.ς, C.cseed]

/-- Positive powers of `v` for the ten small scales. -/
def siteSmallExponent {d : ℕ} (S : SiteData d) : Fin 10 → ℝ :=
  ![siteTExponent S, siteRExponent S, siteNuExponent S,
    siteNuExponent S, siteNuExponent S * 4, siteNuExponent S * 8,
    siteNuExponent S * 3, siteNuExponent S * siteThetaExponent S,
    siteVarsigmaExponent S, siteNuExponent S * siteThetaExponent S]

theorem siteRExponent_pos {d : ℕ} (S : SiteData d) :
    0 < siteRExponent S := by
  unfold siteRExponent
  have hα := S.seed.α_pos
  have hβ := S.seed.β_pos
  positivity [siteTExponent_pos S]

theorem siteThetaExponent_pos {d : ℕ} (S : SiteData d) :
    0 < siteThetaExponent S := by
  unfold siteThetaExponent
  have hb := S.b_ge
  positivity

theorem siteVarsigmaExponent_pos {d : ℕ} (S : SiteData d) :
    0 < siteVarsigmaExponent S := by
  unfold siteVarsigmaExponent
  exact lt_of_lt_of_le (mul_pos (by norm_num) (siteNuExponent_pos S))
    (le_max_left _ _)

theorem siteSmallExponent_pos {d : ℕ} (S : SiteData d) :
    ∀ i : Fin 10, 0 < siteSmallExponent S i := by
  intro i
  fin_cases i
  · exact siteTExponent_pos S
  · exact siteRExponent_pos S
  · exact siteNuExponent_pos S
  · exact siteNuExponent_pos S
  · exact mul_pos (siteNuExponent_pos S) (by norm_num)
  · exact mul_pos (siteNuExponent_pos S) (by norm_num)
  · exact mul_pos (siteNuExponent_pos S) (by norm_num)
  · exact mul_pos (siteNuExponent_pos S) (siteThetaExponent_pos S)
  · exact siteVarsigmaExponent_pos S
  · exact mul_pos (siteNuExponent_pos S) (siteThetaExponent_pos S)

theorem siteSmallScale_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    ∀ i : Fin 10, SitePowerBounds (fun v => siteSmallScale S Cnet v i)
      (siteSmallExponent S i) := by
  intro i
  fin_cases i
  · exact siteConsts_t₀_power S Cnet
  · exact siteConsts_r_power_corrected S hd Cnet
  · exact siteConsts_ν_power S hd Cnet
  · exact siteConsts_g_power S hd Cnet
  · exact siteConsts_ω_power S hd Cnet
  · exact siteConsts_μ_power S hd Cnet
  · exact siteConsts_δsep_power S hd Cnet
  · exact siteConsts_θ_power S hd Cnet hCnet
  · exact siteConsts_ς_power S hd Cnet hCnet
  · exact siteConsts_cseed_power S hd Cnet hCnet

theorem siteInversePower_upper {c v K x a : ℝ}
    (hc : 0 < c) (hv : 0 < v) (ha : 0 ≤ a)
    (hlo : c * v ^ K ≤ x) :
    x ^ (-a) ≤ c ^ (-a) * v ^ (-(K * a)) := by
  have hvK : 0 < v ^ K := Real.rpow_pos_of_pos hv _
  have hbase : 0 < c * v ^ K := mul_pos hc hvK
  calc
    x ^ (-a) ≤ (c * v ^ K) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hbase hlo (by linarith)
    _ = c ^ (-a) * (v ^ K) ^ (-a) := Real.mul_rpow hc.le hvK.le
    _ = c ^ (-a) * v ^ (-(K * a)) := by
      rw [← Real.rpow_mul hv.le]
      congr 1
      ring

/-- Ruling N29's generic clause, with the two large scales. The one exponent
`K` and one pair of fixed constants work for every entry simultaneously. -/
theorem siteConsts_polynomial {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet : ℝ) (hCnet : 0 < Cnet) :
    ∃ vsite c C K : ℝ,
      0 < vsite ∧ vsite ≤ 1 ∧ 0 < c ∧ 0 < C ∧ 0 < K ∧
      ∀ v, 0 < v → v ≤ vsite →
        (∀ i : Fin 10, c * v ^ K ≤ siteSmallScale S Cnet v i ∧
          siteSmallScale S Cnet v i ≤ 1) ∧
        (siteConsts S Cnet v).Anet ≤ C * v ^ (-K) ∧
        ((siteConsts S Cnet v).N : ℝ) ≤ C * v ^ (-K) := by
  obtain ⟨vsite, c, K₀, hvsite, hvsite1, hc, hK₀, hsmall⟩ :=
    sitePowerBounds_finite
      (fun i v => siteSmallScale S Cnet v i) (siteSmallExponent S)
      (siteSmallExponent_pos S) (siteSmallScale_power S hd Cnet hCnet)
  let K : ℝ := K₀ * (8 * d + 1)
  let CA : ℝ := Cnet * S.Hup * c ^ (-(8 * d : ℝ))
  let CN : ℝ := ((4 * √(d : ℝ) + 2) ^ d + 5) * c ^ (-(d : ℝ))
  let C : ℝ := max CA CN
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hH : 0 < S.Hup := by linarith [S.Hup_ge]
  have hCA : 0 < CA := by
    dsimp [CA]
    positivity
  have hCN : 0 < CN := by
    dsimp [CN]
    positivity
  have hC : 0 < C := lt_of_lt_of_le hCA (le_max_left _ _)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hK₀K : K₀ ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hK₀.le (by positivity : (0 : ℝ) ≤ 8 * d)]
  have hKdK : K₀ * d ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hK₀.le (by positivity : (0 : ℝ) ≤ 7 * d + 1)]
  have hK8dK : K₀ * (8 * d : ℝ) ≤ K := by
    dsimp [K]
    nlinarith [hK₀.le]
  refine ⟨vsite, c, C, K, hvsite, hvsite1, hc, hC, hK, ?_⟩
  intro v hv hvsite'
  have hv1 : v ≤ 1 := hvsite'.trans hvsite1
  have hsc := hsmall v hv hvsite'
  have hrlow : c * v ^ K₀ ≤ (siteConsts S Cnet v).r := (hsc 1).1
  have hrone : (siteConsts S Cnet v).r ≤ 1 := (hsc 1).2
  have hνlow : c * v ^ K₀ ≤ (siteConsts S Cnet v).ν := (hsc 2).1
  have hr : 0 < (siteConsts S Cnet v).r := siteConsts_r_pos S hd Cnet v hv
  have hν : 0 < (siteConsts S Cnet v).ν := siteConsts_ν_pos S hd Cnet v
  have hpowA := siteInversePower_upper hc hv (by positivity : (0 : ℝ) ≤ 8 * d) hνlow
  have hpowN := siteInversePower_upper hc hv hdR.le hrlow
  have hvpowA : v ^ (-(K₀ * (8 * d : ℝ))) ≤ v ^ (-K) :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith)
  have hvpowN : v ^ (-(K₀ * d : ℝ)) ≤ v ^ (-K) :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith)
  constructor
  · intro i
    obtain ⟨hlo, hhi⟩ := hsc i
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hv hv1 hK₀K) hc.le).trans hlo
    · exact hhi
  constructor
  · change Cnet * S.Hup * (siteConsts S Cnet v).ν ^ (-(8 * d : ℝ)) ≤
      C * v ^ (-K)
    calc
      Cnet * S.Hup * (siteConsts S Cnet v).ν ^ (-(8 * d : ℝ)) ≤
          CA * v ^ (-(K₀ * (8 * d : ℝ))) := by
            dsimp [CA]
            nlinarith [mul_le_mul_of_nonneg_left hpowA
              (mul_nonneg hCnet.le hH.le)]
      _ ≤ CA * v ^ (-K) := mul_le_mul_of_nonneg_left hvpowA hCA.le
      _ ≤ C * v ^ (-K) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hv _).le
  · have hN := Routing.leadN_le (d := d) hr hrone
    change (Routing.leadN d (siteConsts S Cnet v).r : ℝ) ≤ C * v ^ (-K)
    have hNpow : (siteConsts S Cnet v).r⁻¹ ^ d =
        (siteConsts S Cnet v).r ^ (-(d : ℝ)) := by
      rw [inv_pow, Real.rpow_neg hr.le, Real.rpow_natCast]
    rw [hNpow] at hN
    calc
      (Routing.leadN d (siteConsts S Cnet v).r : ℝ) ≤
          ((4 * √(d : ℝ) + 2) ^ d + 5) *
            (siteConsts S Cnet v).r ^ (-(d : ℝ)) := hN
      _ ≤ CN * v ^ (-(K₀ * d : ℝ)) := by
        dsimp [CN]
        have hcoeff : 0 ≤ (4 * √(d : ℝ) + 2) ^ d + 5 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpowN hcoeff]
      _ ≤ CN * v ^ (-K) := mul_le_mul_of_nonneg_left hvpowN hCN.le
      _ ≤ C * v ^ (-K) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hv _).le

/-- Directly usable joint polynomial lower bounds and unit upper bounds for
all ten small scales. -/
theorem siteConsts_smallScale_polynomial {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet : ℝ) (hCnet : 0 < Cnet) :
    ∃ vsite c K : ℝ, 0 < vsite ∧ vsite ≤ 1 ∧ 0 < c ∧ 0 < K ∧
      ∀ v, 0 < v → v ≤ vsite →
        ∀ i : Fin 10, c * v ^ K ≤ siteSmallScale S Cnet v i ∧
          siteSmallScale S Cnet v i ≤ 1 := by
  exact sitePowerBounds_finite
    (fun i v => siteSmallScale S Cnet v i) (siteSmallExponent S)
    (siteSmallExponent_pos S) (siteSmallScale_power S hd Cnet hCnet)

end HigherDimLQGContinuity
