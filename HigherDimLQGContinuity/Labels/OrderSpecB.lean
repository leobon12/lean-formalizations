import HigherDimLQGContinuity.Labels.OrderSpecA

/-!
# Gate access and attached-lead cost bounds
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem siteTExponent_ge_one {d : ℕ} (S : SiteData d) :
    1 ≤ siteTExponent S := by
  unfold siteTExponent
  exact le_max_left _ _

theorem siteTExponent_mul_alpha_ge {d : ℕ} (S : SiteData d) :
    1 / S.s ≤ siteTExponent S * S.seed.α := by
  have hα := S.seed.α_pos
  have hs := S.s_pos
  have hp : 1 / (S.seed.α * S.s) ≤ siteTExponent S := by
    unfold siteTExponent
    exact le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_right hp hα.le
  have heq : (1 / (S.seed.α * S.s)) * S.seed.α = 1 / S.s := by
    field_simp
  simpa only [heq] using hmul

theorem siteTCoeff_le_sixth {d : ℕ} (S : SiteData d) :
    siteTCoeff S ≤ 1 / 6 := by
  unfold siteTCoeff
  exact min_le_left _ _

theorem siteTCoeff_le_access {d : ℕ} (S : SiteData d) :
    siteTCoeff S ≤
      (16 * S.seed.A) ^ (-(1 / S.seed.α)) *
        (S.seed.d₀ / (1000 * S.Hup)) ^ (1 / (S.seed.α * S.s)) := by
  unfold siteTCoeff
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem siteTCoeff_le_length {d : ℕ} (S : SiteData d) :
    siteTCoeff S ≤ S.seed.d₀ / (4000 * S.seed.ℓ₁) := by
  unfold siteTCoeff
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem siteConsts_t₀_le_sixth {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    (siteConsts S Cnet v).t₀ ≤ 1 / 6 := by
  change siteTCoeff S * v ^ siteTExponent S ≤ 1 / 6
  have hpow : v ^ siteTExponent S ≤ 1 :=
    Real.rpow_le_one hv.le hv1 (siteTExponent_pos S).le
  have hcoeff := siteTCoeff_le_sixth S
  have hcoeffpos := siteTCoeff_pos S
  nlinarith [mul_le_mul hcoeff hpow
    (Real.rpow_pos_of_pos hv _).le (by norm_num : (0 : ℝ) ≤ 1 / 6)]

theorem siteConsts_length_cost {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    2 * (siteConsts S Cnet v).t₀ * S.seed.ℓ₁ ≤
      v * S.seed.d₀ / 2000 := by
  let C := siteConsts S Cnet v
  have hpow : v ^ siteTExponent S ≤ v := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hv hv1 (siteTExponent_ge_one S)
  have hcoeff := siteTCoeff_le_length S
  have hℓ : 0 < S.seed.ℓ₁ := lt_of_lt_of_le S.seed.ℓ₀_pos S.seed.ℓ₀_le_ℓ₁
  have hδ : 0 < 4000 * S.seed.ℓ₁ := by positivity
  have hcoeffmul : siteTCoeff S * (4000 * S.seed.ℓ₁) ≤ S.seed.d₀ :=
    (le_div_iff₀ hδ).1 hcoeff
  change 2 * (siteTCoeff S * v ^ siteTExponent S) * S.seed.ℓ₁ ≤
    v * S.seed.d₀ / 2000
  nlinarith [mul_le_mul_of_nonneg_left hpow (siteTCoeff_pos S).le,
    mul_le_mul_of_nonneg_right hcoeffmul hv.le]

theorem siteConsts_arc_gate_cost {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    S.seed.A * (2 * (siteConsts S Cnet v).t₀) ^ S.seed.α ≤
      (siteConsts S Cnet v).eD / 4 := by
  let A := S.seed.A
  let α := S.seed.α
  let B := S.seed.d₀ / (1000 * S.Hup)
  let p := siteTExponent S
  let ct := siteTCoeff S
  have hA : 0 < A := by linarith [S.seed.A_ge]
  have hα : 0 < α := S.seed.α_pos
  have hB : 0 < B := by
    have hH : 0 < S.Hup := by linarith [S.Hup_ge]
    dsimp [B]
    positivity [S.seed.d₀_pos]
  have hct : 0 < ct := siteTCoeff_pos S
  have hctle : ct ≤ (16 * A) ^ (-(1 / α)) * B ^ (1 / (α * S.s)) :=
    siteTCoeff_le_access S
  have hpα : 1 / S.s ≤ p * α := siteTExponent_mul_alpha_ge S
  have hA16 : 0 < 16 * A := by positivity
  have hbase : 0 < (16 * A) ^ (-(1 / α)) * B ^ (1 / (α * S.s)) := by positivity
  have hctpow : ct ^ α ≤
      ((16 * A) ^ (-(1 / α)) * B ^ (1 / (α * S.s))) ^ α :=
    Real.rpow_le_rpow hct.le hctle hα.le
  have he1 : (-(1 / α)) * α = -1 := by field_simp [ne_of_gt hα]
  have he2 : (1 / (α * S.s)) * α = 1 / S.s := by
    field_simp [ne_of_gt hα, ne_of_gt S.s_pos]
  have hcoeffpow :
      ((16 * A) ^ (-(1 / α)) * B ^ (1 / (α * S.s))) ^ α =
        (16 * A)⁻¹ * B ^ (1 / S.s) := by
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hA16 _).le
      (Real.rpow_pos_of_pos hB _).le,
      ← Real.rpow_mul hA16.le, ← Real.rpow_mul hB.le, he1, he2,
      Real.rpow_neg_one]
  have h2pow : (2 : ℝ) ^ α ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) S.seed.α_le
  have hvpow : v ^ (p * α) ≤ v ^ (1 / S.s) :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 hpα
  have ht0 : (siteConsts S Cnet v).t₀ = ct * v ^ p := rfl
  have hfactor : A * (2 * (siteConsts S Cnet v).t₀) ^ α =
      A * ((2 : ℝ) ^ α * ct ^ α * v ^ (p * α)) := by
    rw [ht0, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg hct.le (Real.rpow_pos_of_pos hv _).le),
      Real.mul_rpow hct.le (Real.rpow_pos_of_pos hv _).le,
      ← Real.rpow_mul hv.le]
    ring
  have hBv : B ^ (1 / S.s) * v ^ (1 / S.s) =
      (v * B) ^ (1 / S.s) := by
    rw [Real.mul_rpow hv.le hB.le]
    ring
  have heD : (siteConsts S Cnet v).eD = (v * B) ^ (1 / S.s) / 2 := by
    change (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 2 = _
    congr 1
    dsimp [B]
    ring
  rw [hfactor, heD]
  change A * ((2 : ℝ) ^ α * ct ^ α * v ^ (p * α)) ≤
    ((v * B) ^ (1 / S.s) / 2) / 4
  calc
    A * ((2 : ℝ) ^ α * ct ^ α * v ^ (p * α)) ≤
        A * (2 * ((16 * A)⁻¹ * B ^ (1 / S.s)) * v ^ (1 / S.s)) := by
      rw [← hcoeffpow]
      gcongr
    _ = B ^ (1 / S.s) * v ^ (1 / S.s) / 8 := by
      field_simp
      ring
    _ = ((v * B) ^ (1 / S.s) / 2) / 4 := by rw [hBv]; ring

theorem siteConsts_g_le_eD_fourth {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) :
    (siteConsts S Cnet v).g ≤ (siteConsts S Cnet v).eD / 4 := by
  let C := siteConsts S Cnet v
  let B := (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s)
  have hν := siteConsts_ν_le_vD S hd Cnet v hv
  have hcoeff : siteNuCoeff S ≤ 1 / (800 * d : ℝ) := by
    unfold siteNuCoeff
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hB : 0 < B := by
    have hH : 0 < S.Hup := by linarith [S.Hup_ge]
    dsimp [B]
    positivity [S.seed.d₀_pos]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hνB : C.ν ≤ B / (800 * d) := by
    calc
      C.ν ≤ siteNuCoeff S * B := hν
      _ ≤ (1 / (800 * d : ℝ)) * B :=
        mul_le_mul_of_nonneg_right hcoeff hB.le
      _ = B / (800 * d) := by ring
  have hden : 0 < (800 * d : ℝ) := by positivity
  have hmul := (le_div_iff₀ hden).1 hνB
  change 100 * d * C.ν ≤ (B / 2) / 4
  nlinarith

theorem siteConsts_omega_le_nu {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ω ≤ (siteConsts S Cnet v).ν := by
  let C := siteConsts S Cnet v
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ √(d : ℝ) := Real.one_le_sqrt.mpr hdR
  have hcω : 0 < siteOmegaCoeff d := siteOmegaCoeff_pos d (by omega)
  have hcω1 : siteOmegaCoeff d ≤ 1 := by
    have h := min_le_right (Routing.gpC1 4 / 8) (1 / (8 * √(d : ℝ)))
    unfold siteOmegaCoeff
    apply h.trans
    have hden : (1 : ℝ) ≤ 8 * √(d : ℝ) := by nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 8 * √(d : ℝ))).2
    simpa only [one_mul] using hden
  have hν4 : C.ν ^ 4 ≤ C.ν := pow_le_of_le_one hν.le hν1 (by norm_num)
  change siteOmegaCoeff d * C.ν ^ 4 ≤ C.ν
  calc
    siteOmegaCoeff d * C.ν ^ 4 ≤ 1 * C.ν := by
      exact (mul_le_mul_of_nonneg_left hν4 hcω.le).trans
        (mul_le_mul_of_nonneg_right hcω1 hν.le)
    _ = C.ν := one_mul _

theorem siteConsts_ς_le_eD_fourth {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ς ≤ (siteConsts S Cnet v).eD / 4 := by
  let C := siteConsts S Cnet v
  have h : C.ς ≤ siteVarsigmaTerm3 S v := by
    change siteVarsigmaFrom S v C.ν C.θ ≤ siteVarsigmaTerm3 S v
    unfold siteVarsigmaFrom
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  calc
    C.ς ≤ siteVarsigmaTerm3 S v := h
    _ = C.eD / 4 := by
      change (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 8 =
        ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 2) / 4
      ring

theorem siteConsts_gate_width_le_eD {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    S.seed.A * (2 * (siteConsts S Cnet v).t₀) ^ S.seed.α +
      (siteConsts S Cnet v).g + (siteConsts S Cnet v).ω +
        (siteConsts S Cnet v).ς ≤ (siteConsts S Cnet v).eD := by
  let C := siteConsts S Cnet v
  have ht := siteConsts_arc_gate_cost S Cnet v hv hv1
  have hg := siteConsts_g_le_eD_fourth S hd Cnet v hv
  have hων := siteConsts_omega_le_nu S hd Cnet v
  have hνg : C.ν ≤ C.g := by
    have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    change C.ν ≤ 100 * d * C.ν
    nlinarith
  have hω : C.ω ≤ C.eD / 4 := (hων.trans hνg).trans hg
  have hς := siteConsts_ς_le_eD_fourth S Cnet v
  linarith

theorem siteConsts_lead_access_cost {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) :
    2 * siteCS S.seed.sE * S.seed.HE *
      (siteConsts S Cnet v).g ^ S.seed.sE ≤
        v * S.seed.d₀ / 2000 := by
  let C := siteConsts S Cnet v
  let sE := S.seed.sE
  let Cs := siteCS sE
  let B := v * S.seed.d₀ / (1000 * S.seed.HE)
  let c := (4 * Cs) ^ (-(1 / sE))
  have hsE : 0 < sE := S.seed.sE_pos
  have hCs : 0 < Cs := siteCS_pos hsE
  have hHE : 0 < S.seed.HE := by linarith [S.seed.HE_ge]
  have hB : 0 < B := by
    dsimp [B]
    positivity [S.seed.d₀_pos]
  have hc : 0 < c := by dsimp [c]; positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hν := siteConsts_ν_le_vE S hd Cnet v hv
  have hcoeff : siteNuCoeff S ≤ c / (100 * d : ℝ) := by
    unfold siteNuCoeff
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hpowB : 0 < B ^ (1 / sE) := Real.rpow_pos_of_pos hB _
  have hνbound : C.ν ≤ c / (100 * d : ℝ) * B ^ (1 / sE) :=
    hν.trans (mul_le_mul_of_nonneg_right hcoeff hpowB.le)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    positivity [siteConsts_ν_pos S hd Cnet v]
  have hgbound : C.g ≤ c * B ^ (1 / sE) := by
    change 100 * d * C.ν ≤ c * B ^ (1 / sE)
    have hden : 0 < (100 * d : ℝ) := by positivity
    calc
      (100 * d : ℝ) * C.ν ≤
          (100 * d : ℝ) * (c / (100 * d : ℝ) * B ^ (1 / sE)) :=
        mul_le_mul_of_nonneg_left hνbound hden.le
      _ = c * B ^ (1 / sE) := by field_simp
  have hgpow := Real.rpow_le_rpow hg.le hgbound hsE.le
  have he1 : (-(1 / sE)) * sE = -1 := by field_simp [ne_of_gt hsE]
  have he2 : (1 / sE) * sE = 1 := by field_simp [ne_of_gt hsE]
  have hpowEq : (c * B ^ (1 / sE)) ^ sE = (4 * Cs)⁻¹ * B := by
    dsimp [c]
    rw [Real.mul_rpow (Real.rpow_pos_of_pos (by positivity : 0 < 4 * Cs) _).le
      (Real.rpow_pos_of_pos hB _).le,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4 * Cs),
      ← Real.rpow_mul hB.le, he1, he2, Real.rpow_neg_one, Real.rpow_one]
  have hcost : 2 * Cs * S.seed.HE * C.g ^ sE ≤
      2 * Cs * S.seed.HE * ((4 * Cs)⁻¹ * B) := by
    rw [← hpowEq]
    exact mul_le_mul_of_nonneg_left hgpow (by positivity)
  change 2 * Cs * S.seed.HE * C.g ^ sE ≤ v * S.seed.d₀ / 2000
  calc
    2 * Cs * S.seed.HE * C.g ^ sE ≤
        2 * Cs * S.seed.HE * ((4 * Cs)⁻¹ * B) := hcost
    _ = v * S.seed.d₀ / 2000 := by
      dsimp [B]
      field_simp
      ring

theorem siteConsts_eD_power {d : ℕ} (S : SiteData d) (Cnet : ℝ) :
    SitePowerBounds (fun v => (siteConsts S Cnet v).eD) (1 / S.s) := by
  have h := sitePowerBounds_scale (siteVarsigmaTerm3_power S)
    (by norm_num : (0 : ℝ) < 4)
  apply sitePowerBounds_congr h
  intro v _ _
  change 4 * ((v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 8) =
    (v * S.seed.d₀ / (1000 * S.Hup)) ^ (1 / S.s) / 2
  -- The first term of (O8) is `eD/4`.
  ring

/-- Clause (b) of the corrected order lemma. -/
theorem siteConsts_spec_b {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet : ℝ) :
    ∃ vsite : ℝ, 0 < vsite ∧ vsite ≤ 1 / 100 ∧
      ∀ v, 0 < v → v ≤ vsite →
        let C := siteConsts S Cnet v
        S.seed.A * (2 * C.t₀) ^ S.seed.α + C.g + C.ω + C.ς ≤
          min C.eD (1 / 8) ∧
        2 * siteCS S.seed.sE * S.seed.HE * C.g ^ S.seed.sE +
          2 * C.t₀ * S.seed.ℓ₁ ≤ v * S.seed.d₀ / 1000 := by
  obtain ⟨ε, hε, hε1, heDsmall⟩ :=
    sitePowerBounds_small (siteConsts_eD_power S Cnet)
      (by positivity [S.s_pos] : 0 < 1 / S.s)
      (by norm_num : (0 : ℝ) < 1 / 8)
  let vsite := min (1 / 100 : ℝ) ε
  refine ⟨vsite, lt_min (by norm_num) hε, min_le_left _ _, ?_⟩
  intro v hv hvsite
  have hvε : v ≤ ε := hvsite.trans (min_le_right _ _)
  have hv1 : v ≤ 1 := hvε.trans hε1
  let C := siteConsts S Cnet v
  have hρ := siteConsts_gate_width_le_eD S hd Cnet v hv hv1
  have heD := heDsmall v hv hvε
  have hlead := siteConsts_lead_access_cost S hd Cnet v hv
  have hlength := siteConsts_length_cost S Cnet v hv hv1
  change S.seed.A * (2 * C.t₀) ^ S.seed.α + C.g + C.ω + C.ς ≤
      min C.eD (1 / 8) ∧
    2 * siteCS S.seed.sE * S.seed.HE * C.g ^ S.seed.sE +
      2 * C.t₀ * S.seed.ℓ₁ ≤ v * S.seed.d₀ / 1000
  constructor
  · exact le_min hρ (hρ.trans heD)
  · linarith

end HigherDimLQGContinuity
