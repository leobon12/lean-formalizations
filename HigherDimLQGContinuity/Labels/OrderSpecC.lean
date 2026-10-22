import HigherDimLQGContinuity.Labels.OrderSpecB

/-!
# Network and attachment inequalities of the explicit order
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem siteConsts_Anet_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) :
    0 < (siteConsts S Cnet v).Anet := by
  change 0 < Cnet * S.Hup * (siteConsts S Cnet v).ν ^ (-(8 * d : ℝ))
  have hH : 0 < S.Hup := by linarith [S.Hup_ge]
  have hν := siteConsts_ν_pos S hd Cnet v
  positivity

theorem siteConsts_delta_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) : 0 < (siteConsts S Cnet v).δsep := by
  change 0 < siteDeltaFromNu (siteConsts S Cnet v).ν
  unfold siteDeltaFromNu
  have hν := siteConsts_ν_pos S hd Cnet v
  have hc1 := Routing.gpC1_pos (show (0 : ℝ) ≤ 4 by norm_num)
  positivity

theorem siteConsts_theta_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) :
    0 < (siteConsts S Cnet v).θ := by
  let C := siteConsts S Cnet v
  have hAnet := siteConsts_Anet_pos S hd Cnet v hCnet
  have hδ := siteConsts_delta_pos S hd Cnet v
  have hε := siteData_eps0_pos S
  have hH : 0 < S.Hlo⁻¹ := by
    apply inv_pos.mpr
    linarith [S.Hlo_ge]
  change 0 < siteThetaNumerator S C.ν / (4 * C.Anet)
  unfold siteThetaNumerator
  have hδeq : siteDeltaFromNu C.ν = C.δsep := rfl
  rw [hδeq]
  positivity

theorem siteConsts_varsigma_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1) :
    0 < (siteConsts S Cnet v).ς := by
  obtain ⟨c, C, hc, hC, hb⟩ := siteConsts_ς_power S hd Cnet hCnet
  have h := (hb v hv hv1).1
  have hvpow : 0 < v ^ siteVarsigmaExponent S := Real.rpow_pos_of_pos hv _
  have hcv : 0 < c * v ^ siteVarsigmaExponent S := mul_pos hc hvpow
  exact lt_of_lt_of_le hcv h

theorem siteConsts_enet_eq {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) :
    (siteConsts S Cnet v).enet =
      siteThetaNumerator S (siteConsts S Cnet v).ν / 4 := by
  let C := siteConsts S Cnet v
  have hAnet := siteConsts_Anet_pos S hd Cnet v hCnet
  change C.θ * C.Anet = siteThetaNumerator S C.ν / 4
  have hθ : C.θ = siteThetaNumerator S C.ν / (4 * C.Anet) := rfl
  rw [hθ]
  change 0 < C.Anet at hAnet
  field_simp [ne_of_gt hAnet]

theorem siteRootBound {x H s y : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hs : 0 < s) (hy : 0 ≤ y)
    (h : y ≤ (x / H) ^ (1 / s)) :
    H * y ^ s ≤ x := by
  have hbase : 0 < x / H := div_pos hx hH
  have hpow := Real.rpow_le_rpow hy h hs.le
  have he : (1 / s) * s = 1 := by field_simp [ne_of_gt hs]
  rw [← Real.rpow_mul hbase.le, he, Real.rpow_one] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow hH.le
  have hcancel : H * (x / H) = x := by field_simp [ne_of_gt hH]
  exact hmul.trans_eq hcancel

theorem siteConsts_varsigma_le_term1 {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ς ≤ (siteConsts S Cnet v).δsep / 4 := by
  let C := siteConsts S Cnet v
  change siteVarsigmaFrom S v C.ν C.θ ≤ siteDeltaFromNu C.ν / 4
  unfold siteVarsigmaFrom siteVarsigmaTerm1
  exact min_le_left _ _

theorem siteConsts_varsigma_le_term2 {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ς ≤ (siteConsts S Cnet v).ω / 4 := by
  let C := siteConsts S Cnet v
  change siteVarsigmaFrom S v C.ν C.θ ≤ siteOmegaCoeff d * C.ν ^ 4 / 4
  unfold siteVarsigmaFrom siteVarsigmaTerm2
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem siteConsts_varsigma_le_term4 {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ς ≤
      ((S.Hlo⁻¹ * ((siteConsts S Cnet v).δsep / 2) ^ S.b) /
        (4 * S.Hup)) ^ (1 / S.s) / 4 := by
  let C := siteConsts S Cnet v
  change siteVarsigmaFrom S v C.ν C.θ ≤ siteVarsigmaTerm4 S C.ν
  unfold siteVarsigmaFrom
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))

theorem siteConsts_varsigma_le_term5 {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ς ≤
      (v * (siteConsts S Cnet v).θ * S.seed.d₀ /
        (1000 * S.seed.HE)) ^ (1 / S.seed.sE) / 4 := by
  let C := siteConsts S Cnet v
  change siteVarsigmaFrom S v C.ν C.θ ≤ siteVarsigmaTerm5 S v C.θ
  unfold siteVarsigmaFrom
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))

theorem siteConsts_enet_bounds {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) :
    (siteConsts S Cnet v).enet ≤ siteEps0 S.mc S.Hlo ∧
    (siteConsts S Cnet v).enet ≤
      (S.Hlo⁻¹ * ((siteConsts S Cnet v).δsep / 2) ^ S.b) / 4 := by
  let C := siteConsts S Cnet v
  rw [siteConsts_enet_eq S hd Cnet v hCnet]
  have hε : 0 < siteEps0 S.mc S.Hlo := siteData_eps0_pos S
  have hmin1 : siteThetaNumerator S C.ν ≤ siteEps0 S.mc S.Hlo := by
    unfold siteThetaNumerator
    exact min_le_left _ _
  have hmin2 : siteThetaNumerator S C.ν ≤
      S.Hlo⁻¹ * (C.δsep / 2) ^ S.b := by
    unfold siteThetaNumerator
    exact min_le_right _ _
  constructor
  · linarith
  · linarith

theorem siteConsts_eatt_bound {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1) :
    (siteConsts S Cnet v).eatt ≤
      (S.Hlo⁻¹ * ((siteConsts S Cnet v).δsep / 2) ^ S.b) / 4 := by
  let C := siteConsts S Cnet v
  have hδ := siteConsts_delta_pos S hd Cnet v
  have hHlo : 0 < S.Hlo⁻¹ := by
    apply inv_pos.mpr
    linarith [S.Hlo_ge]
  have hx : 0 < S.Hlo⁻¹ * (C.δsep / 2) ^ S.b := by positivity
  have hH : 0 < 4 * S.Hup := by linarith [S.Hup_ge]
  have hς : 0 ≤ C.ς :=
    (siteConsts_varsigma_pos S hd Cnet v hCnet hv hv1).le
  have hterm := siteConsts_varsigma_le_term4 S Cnet v
  have hroot : 4 * C.ς ≤
      ((S.Hlo⁻¹ * (C.δsep / 2) ^ S.b) / (4 * S.Hup)) ^ (1 / S.s) := by
    linarith
  have hbound := siteRootBound hx hH S.s_pos (by linarith : 0 ≤ 4 * C.ς) hroot
  change S.Hup * (4 * C.ς) ^ S.s ≤ _
  nlinarith

theorem siteConsts_secondary_attachment_bound {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hCnet : 0 < Cnet)
    (hv : 0 < v) (hv1 : v ≤ 1) :
    S.seed.HE * (4 * (siteConsts S Cnet v).ς) ^ S.seed.sE ≤
      v * (siteConsts S Cnet v).θ * S.seed.d₀ / 1000 := by
  let C := siteConsts S Cnet v
  have hθ := siteConsts_theta_pos S hd Cnet v hCnet
  have hHE : 0 < S.seed.HE := by linarith [S.seed.HE_ge]
  have hx : 0 < v * C.θ * S.seed.d₀ / 1000 := by
    positivity [S.seed.d₀_pos]
  have hς : 0 ≤ C.ς :=
    (siteConsts_varsigma_pos S hd Cnet v hCnet hv hv1).le
  have hterm := siteConsts_varsigma_le_term5 S Cnet v
  have hbaseEq :
      v * C.θ * S.seed.d₀ / (1000 * S.seed.HE) =
        (v * C.θ * S.seed.d₀ / 1000) / S.seed.HE := by ring
  have hroot : 4 * C.ς ≤
      ((v * C.θ * S.seed.d₀ / 1000) / S.seed.HE) ^ (1 / S.seed.sE) := by
    rw [← hbaseEq]
    linarith
  exact siteRootBound hx hHE S.seed.sE_pos (by linarith : 0 ≤ 4 * C.ς) hroot

/-- Clause (c) of the corrected order lemma. -/
theorem siteConsts_spec_c {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1) :
    let C := siteConsts S Cnet v
    C.enet ≤ siteEps0 S.mc S.Hlo ∧
    4 * C.ς ≤ C.δsep ∧ C.ς ≤ C.ω / 4 ∧
    2 * C.eatt + C.enet < S.Hlo⁻¹ * (C.δsep / 2) ^ S.b ∧
    S.seed.HE * (4 * C.ς) ^ S.seed.sE ≤
      v * C.θ * S.seed.d₀ / 1000 := by
  let C := siteConsts S Cnet v
  have hδ := siteConsts_delta_pos S hd Cnet v
  have hHlo : 0 < S.Hlo⁻¹ := by
    apply inv_pos.mpr
    linarith [S.Hlo_ge]
  have htarget : 0 < S.Hlo⁻¹ * (C.δsep / 2) ^ S.b := by positivity
  have henet := siteConsts_enet_bounds S hd Cnet v hCnet
  have hςδ := siteConsts_varsigma_le_term1 S Cnet v
  have hςω := siteConsts_varsigma_le_term2 S Cnet v
  have heatt := siteConsts_eatt_bound S hd Cnet v hCnet hv hv1
  have hE := siteConsts_secondary_attachment_bound S hd Cnet v hCnet hv hv1
  change C.enet ≤ siteEps0 S.mc S.Hlo ∧
    4 * C.ς ≤ C.δsep ∧ C.ς ≤ C.ω / 4 ∧
    2 * C.eatt + C.enet < S.Hlo⁻¹ * (C.δsep / 2) ^ S.b ∧
    S.seed.HE * (4 * C.ς) ^ S.seed.sE ≤
      v * C.θ * S.seed.d₀ / 1000
  refine ⟨henet.1, by linarith, hςω, ?_, hE⟩
  linarith [henet.2]

end HigherDimLQGContinuity
