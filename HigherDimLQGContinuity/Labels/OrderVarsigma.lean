import HigherDimLQGContinuity.Labels.OrderPower

/-!
# Corrected power exponent for the attachment radius

Each of the five terms of (O8) has a checked power bound. Their minimum has
the exponent `q_ς` of ruling N29.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

private theorem nu_range {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    ∀ v, 0 < v → v ≤ 1 →
      0 < (siteConsts S Cnet v).ν ∧ (siteConsts S Cnet v).ν ≤ 1 :=
  fun v _ _ => ⟨siteConsts_ν_pos S hd Cnet v,
    siteConsts_ν_le_one S hd Cnet v⟩

theorem siteVarsigmaTerm1_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => siteVarsigmaTerm1 (siteConsts S Cnet v).ν)
      (siteNuExponent S * 3) := by
  have h := sitePowerBounds_comp siteDeltaFromNu_power
    (siteConsts_ν_power S hd Cnet) (by norm_num) (nu_range S hd Cnet)
  exact sitePowerBounds_div_const h (by norm_num)

theorem siteVarsigmaTerm2_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => siteVarsigmaTerm2 d (siteConsts S Cnet v).ν)
      (siteNuExponent S * 4) := by
  have hc : 0 < siteOmegaCoeff d / 4 := by
    have hω := siteOmegaCoeff_pos d (by omega)
    positivity
  have h := sitePowerBounds_scale
    (sitePowerBounds_rpow (siteConsts_ν_power S hd Cnet) (by norm_num : (0 : ℝ) < 4)) hc
  apply sitePowerBounds_congr h
  intro v _ _
  unfold siteVarsigmaTerm2
  rw [← Real.rpow_natCast]
  ring

theorem siteVarsigmaTerm3_power {d : ℕ} (S : SiteData d) :
    SitePowerBounds (siteVarsigmaTerm3 S) (1 / S.s) := by
  have hH : 0 < 1000 * S.Hup := by linarith [S.Hup_ge]
  have hc : 0 < S.seed.d₀ / (1000 * S.Hup) := by positivity [S.seed.d₀_pos]
  have hs : 0 < 1 / S.s := by positivity [S.s_pos]
  have h := sitePowerBounds_div_const
    (sitePowerBounds_rpow
      (sitePowerBounds_scale (sitePowerBounds_monomial 1) hc) hs)
    (by norm_num : (0 : ℝ) < 8)
  apply sitePowerBounds_congr (by simpa only [one_mul] using h)
  intro v _ _
  unfold siteVarsigmaTerm3
  congr 1
  simp only [Real.rpow_one]
  ring

theorem siteVarsigmaTerm4_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    SitePowerBounds (fun v => siteVarsigmaTerm4 S (siteConsts S Cnet v).ν)
      ((3 * S.b / S.s) * siteNuExponent S) := by
  have hδ := sitePowerBounds_comp siteDeltaFromNu_power
    (siteConsts_ν_power S hd Cnet) (by norm_num) (nu_range S hd Cnet)
  have hb : 0 < S.b := by linarith [S.b_ge]
  have hHlo : 0 < S.Hlo⁻¹ := by
    apply inv_pos.mpr
    linarith [S.Hlo_ge]
  have hHup : 0 < 4 * S.Hup := by linarith [S.Hup_ge]
  have hs : 0 < 1 / S.s := by positivity [S.s_pos]
  have h := sitePowerBounds_div_const
    (sitePowerBounds_rpow
      (sitePowerBounds_div_const
        (sitePowerBounds_scale
          (sitePowerBounds_rpow
            (sitePowerBounds_div_const hδ (by norm_num : (0 : ℝ) < 2)) hb)
          hHlo) hHup) hs)
    (by norm_num : (0 : ℝ) < 4)
  have hq : ((siteNuExponent S * 3) * S.b) * (1 / S.s) =
      (3 * S.b / S.s) * siteNuExponent S := by ring
  rw [hq] at h
  apply sitePowerBounds_congr h
  intro v _ _
  unfold siteVarsigmaTerm4
  rfl

theorem siteVarsigmaTerm5_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    SitePowerBounds (fun v => siteVarsigmaTerm5 S v (siteConsts S Cnet v).θ)
      ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE) := by
  have hHE : 0 < 1000 * S.seed.HE := by linarith [S.seed.HE_ge]
  have hc : 0 < S.seed.d₀ / (1000 * S.seed.HE) := by positivity [S.seed.d₀_pos]
  have hsE : 0 < 1 / S.seed.sE := by positivity [S.seed.sE_pos]
  have hθ := siteConsts_θ_power S hd Cnet hCnet
  have hmul := sitePowerBounds_mul (sitePowerBounds_monomial 1) hθ
  have h := sitePowerBounds_div_const
    (sitePowerBounds_rpow (sitePowerBounds_scale hmul hc) hsE)
    (by norm_num : (0 : ℝ) < 4)
  have hq : (1 + siteNuExponent S * siteThetaExponent S) * (1 / S.seed.sE) =
      (1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE := by ring
  rw [hq] at h
  apply sitePowerBounds_congr h
  intro v _ _
  unfold siteVarsigmaTerm5
  simp only [Real.rpow_one]
  congr 1
  ring

theorem siteVarsigmaExponent_full {d : ℕ} (S : SiteData d) :
    max (siteNuExponent S * 3)
      (max (siteNuExponent S * 4)
        (max (1 / S.s)
          (max ((3 * S.b / S.s) * siteNuExponent S)
            ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE)))) =
      siteVarsigmaExponent S := by
  have hq : 0 < siteNuExponent S := siteNuExponent_pos S
  have hq1 : siteNuExponent S * 3 ≤ siteNuExponent S * 4 := by nlinarith
  have hbase : 1 / S.s ≤ siteNuExponent S := by
    unfold siteNuExponent
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hq3 : 1 / S.s ≤ siteNuExponent S * 4 := by nlinarith
  unfold siteVarsigmaExponent
  calc
    max (siteNuExponent S * 3)
        (max (siteNuExponent S * 4)
          (max (1 / S.s)
            (max ((3 * S.b / S.s) * siteNuExponent S)
              ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE))))
      = max (max (siteNuExponent S * 3) (siteNuExponent S * 4))
          (max (1 / S.s)
            (max ((3 * S.b / S.s) * siteNuExponent S)
              ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE))) := by rw [max_assoc]
    _ = max (siteNuExponent S * 4)
          (max (1 / S.s)
            (max ((3 * S.b / S.s) * siteNuExponent S)
              ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE))) := by
          rw [max_eq_right hq1]
    _ = max (max (siteNuExponent S * 4) (1 / S.s))
          (max ((3 * S.b / S.s) * siteNuExponent S)
            ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE)) := by rw [max_assoc]
    _ = max (siteNuExponent S * 4)
          (max ((3 * S.b / S.s) * siteNuExponent S)
            ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE)) := by
          rw [max_eq_left hq3]
    _ = max (4 * siteNuExponent S)
          (max ((3 * S.b / S.s) * siteNuExponent S)
            ((1 + siteThetaExponent S * siteNuExponent S) / S.seed.sE)) := by ring

theorem siteConsts_ς_power {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) (hCnet : 0 < Cnet) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).ς)
      (siteVarsigmaExponent S) := by
  have h1 := siteVarsigmaTerm1_power S hd Cnet
  have h2 := siteVarsigmaTerm2_power S hd Cnet
  have h3 := siteVarsigmaTerm3_power S
  have h4 := siteVarsigmaTerm4_power S hd Cnet
  have h5 := siteVarsigmaTerm5_power S hd Cnet hCnet
  have h := sitePowerBounds_min h1
    (sitePowerBounds_min h2
      (sitePowerBounds_min h3 (sitePowerBounds_min h4 h5)))
  rw [siteVarsigmaExponent_full S] at h
  change SitePowerBounds (fun v => siteVarsigmaFrom S v
    (siteConsts S Cnet v).ν (siteConsts S Cnet v).θ)
    (siteVarsigmaExponent S)
  exact h

end HigherDimLQGContinuity
