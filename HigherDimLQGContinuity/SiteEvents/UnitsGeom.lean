import HigherDimLQGContinuity.SiteEvents.UnitsArithmetic
import HigherDimLQGMetric.Shell.Across
import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Events.AnnulusDiameter

/-! Deterministic metric geometry for the eligible site unit. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open scoped ENNReal
open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- An ambient distance from inside one sphere to the next dominates the across distance. -/
theorem q10_across_le_point {d : ℕ} (G : ContMetric d) (hG : G.IsLength)
    {z x y : Rd d} {a b : ℝ} (hab : a ≤ b)
    (hx : ‖x - z‖ ≤ a) (hy : b ≤ ‖y - z‖) :
    acrossDist G z a b ≤ ENNReal.ofReal (G.1 (x, y)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, hPc, hPa, hPb, hlen⟩ :=
    (G.isLength_iff_curves.mp hG) x y ε (by exact_mod_cast hε)
  have hcont : ContinuousOn (fun t => ‖P t - z‖) (Icc (0 : ℝ) 1) :=
    (hPc.sub continuousOn_const).norm
  have h0 : ‖P 0 - z‖ ≤ a := by simpa only [hPa] using hx
  have h1 : b ≤ ‖P 1 - z‖ := by simpa only [hPb] using hy
  obtain ⟨t₁, ht₁, hft₁⟩ := intermediate_value_Icc zero_le_one hcont ⟨h0.trans hab, h1⟩
  change ‖P t₁ - z‖ = b at hft₁
  obtain ⟨t₀, ht₀, hft₀⟩ :=
    intermediate_value_Icc ht₁.1 (hcont.mono (Icc_subset_Icc le_rfl ht₁.2))
      ⟨h0, by rw [hft₁]; exact hab⟩
  have hmema : P t₀ ∈ sphere z a := by rw [mem_sphere, dist_eq_norm]; exact hft₀
  have hmemb : P t₁ ∈ sphere z b := by rw [mem_sphere, dist_eq_norm]; exact hft₁
  calc
    acrossDist G z a b ≤ ENNReal.ofReal (G.1 (P t₀, P t₁)) :=
      (iInf₂_le _ hmema).trans (iInf₂_le _ hmemb)
    _ ≤ G.len P t₀ t₁ := G.ofReal_le_len P ht₀.2
    _ ≤ G.len P 0 1 := G.len_mono P ht₀.1 ht₁.2
    _ ≤ ENNReal.ofReal (G.1 (x, y)) + ENNReal.ofReal ε := hlen
    _ = ENNReal.ofReal (G.1 (x, y)) + ε := by rw [ENNReal.ofReal_coe_nnreal]

/-- The outer site collar imposes a lower bound on the distance from the origin to radius three. -/
theorem q10_site_outer_cross_point {d : ℕ} (hd : 1 ≤ d) (G : ContMetric d)
    (hG : G.IsLength) {Hup σ Hlo β mc A0 : ℝ} (_hmc : 0 ≤ mc)
    (hR : SiteRefs Hup σ Hlo β mc A0 G) :
    mc ≤ G.1 (0, (3 : ℝ) • e₁ d) := by
  have hsub : annCl (0 : Rd d) (5 / 2) 3 ⊆ siteA d := by
    intro u hu
    simp only [siteA, annA, ann, sub_zero] at ⊢
    simp only [annCl, sub_zero] at hu
    change (5 / 2 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 3 at hu
    constructor <;> linarith
  have hAo : IsOpen (siteA d) := isOpen_ann _ _ _
  have hcross : ENNReal.ofReal mc ≤ acrossDist G 0 (5 / 2) 3 := by
    rw [acrossDist_eq_setDistIn G hG hAo (by norm_num : (5 / 2 : ℝ) < 3)]
    · exact hR.2.2.2.1
    · simpa only [siteA] using hsub
  have hnorm : ‖(3 : ℝ) • e₁ d - (0 : Rd d)‖ = 3 := by
    simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [HigherDimLFPP.norm_e₁ (by omega : 0 < d)]
    ring
  have hpt := q10_across_le_point G hG (z := 0) (x := 0)
    (y := (3 : ℝ) • e₁ d) (a := 5 / 2) (b := 3)
    (by norm_num) (by norm_num) (by rw [hnorm])
  exact (ENNReal.ofReal_le_ofReal_iff (G.nonneg _ _)).1 (hcross.trans hpt)

/-- The outer collar reference and the global doubled-ball bound control the physical site unit. -/
theorem q10_site_unit_upper {d : ℕ} (hd : 1 ≤ d) (G : ContMetric d) (hG : G.IsLength)
    {z : Rd d} {s S R H σ Hup σup Hlo β mc A0 : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hS : 0 < S) (hR : 4 ≤ R)
    (hH : 0 < H) (hmc : 0 < mc) (hz : z ∈ ball (0 : Rd d) 3)
    (hglob : ∀ w ∈ closedBall (0 : Rd d) R, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      diamIn G (ball w (2 * r)) (ball w r) ≤ ENNReal.ofReal (H * r ^ σ))
    (hRefs : SiteRefs Hup σup Hlo β mc A0
      ((G.affine s hs.ne' z).smul S⁻¹ (inv_pos.mpr hS))) :
    mc * S ≤ H * (4 * s) ^ σ := by
  let u : Rd d := s • ((3 : ℝ) • e₁ d) + z
  have he₁ : ‖e₁ d‖ = 1 := HigherDimLFPP.norm_e₁ (by omega : 0 < d)
  have huNorm : ‖u - z‖ = 3 * s := by
    simp only [u, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs, abs_of_pos (by norm_num : (0 : ℝ) < 3), he₁]
    ring
  have hzin : z ∈ closedBall (0 : Rd d) R := by
    have hzn : ‖z‖ < 3 := by simpa only [mem_ball, dist_zero_right] using hz
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hr : 4 * s ∈ Set.Ioc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
  have hballz : z ∈ ball z (4 * s) := mem_ball_self (by positivity)
  have hballu : u ∈ ball z (4 * s) := by
    rw [mem_ball, dist_eq_norm, huNorm]
    linarith
  have hDle : G.1 (z, u) ≤ H * (4 * s) ^ σ := by
    have h₁ := G.ofReal_le_internal (ball z (2 * (4 * s))) z u
    have h₂ : G.internal (ball z (2 * (4 * s))) z u ≤
        diamIn G (ball z (2 * (4 * s))) (ball z (4 * s)) := by
      unfold diamIn
      exact le_iSup_of_le z (le_iSup_of_le hballz
        (le_iSup_of_le u (le_iSup_of_le hballu le_rfl)))
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hH.le (Real.rpow_nonneg (by positivity) _))).1
      ((h₁.trans h₂).trans (hglob z hzin (4 * s) hr))
  let Ghat : ContMetric d := (G.affine s hs.ne' z).smul S⁻¹ (inv_pos.mpr hS)
  have hGhat : Ghat.IsLength :=
    ContMetric.isLength_smul (inv_pos.mpr hS) (ContMetric.isLength_affine hs.ne' z hG)
  have hCrossPt := q10_site_outer_cross_point hd Ghat hGhat hmc.le hRefs
  have hCross : mc ≤ S⁻¹ * G.1 (z, u) := by
    simpa only [Ghat, u, ContMetric.smul_apply, ContMetric.affine_apply,
      smul_zero, zero_add] using hCrossPt
  have hCrossMul := mul_le_mul_of_nonneg_right hCross hS.le
  have hcancel : (S⁻¹ * G.1 (z, u)) * S = G.1 (z, u) := by
    field_simp
  rw [hcancel] at hCrossMul
  exact hCrossMul.trans hDle

/-- The diameter reference on the collector and the global lower envelope control the site unit below. -/
theorem q10_site_unit_lower {d : ℕ} (hd : 1 ≤ d) (G : ContMetric d)
    {z : Rd d} {s S R H β Hup σup Hlo b mc A0 : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hS : 0 < S) (hR : 4 ≤ R)
    (_hH : 0 < H) (hA0 : 0 < A0) (hz : z ∈ ball (0 : Rd d) 3)
    (hglob : ∀ u ∈ closedBall (0 : Rd d) R, ∀ v ∈ closedBall (0 : Rd d) R,
      H⁻¹ * ‖u - v‖ ^ β ≤ G.1 (u, v))
    (hRefs : SiteRefs Hup σup Hlo b mc A0
      ((G.affine s hs.ne' z).smul S⁻¹ (inv_pos.mpr hS))) :
    H⁻¹ * (4 * s) ^ β / A0 ≤ S := by
  let a : Rd d := (2 : ℝ) • e₁ d
  let bpt : Rd d := (-2 : ℝ) • e₁ d
  let u : Rd d := s • a + z
  let v : Rd d := s • bpt + z
  have he₁ : ‖e₁ d‖ = 1 := HigherDimLFPP.norm_e₁ (by omega : 0 < d)
  have haNorm : ‖a‖ = 2 := by
    simp only [a, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), he₁]
    ring
  have hbNorm : ‖bpt‖ = 2 := by
    simp only [bpt, norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num : (-2 : ℝ) < 0), he₁]
    ring
  have hmemA : a ∈ siteC d := by
    simp only [siteC, annCl, sub_zero]
    change (3 / 2 : ℝ) ≤ ‖a‖ ∧ ‖a‖ ≤ 5 / 2
    rw [haNorm]
    constructor <;> norm_num
  have hmemB : bpt ∈ siteC d := by
    simp only [siteC, annCl, sub_zero]
    change (3 / 2 : ℝ) ≤ ‖bpt‖ ∧ ‖bpt‖ ≤ 5 / 2
    rw [hbNorm]
    constructor <;> norm_num
  have hdiff : ‖u - v‖ = 4 * s := by
    have heq : u - v = s • ((4 : ℝ) • e₁ d) := by
      dsimp [u, v, a, bpt]
      rw [add_sub_add_right_eq_sub, ← smul_sub, ← sub_smul]
      congr 1
      ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hs, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4), he₁]
    ring
  have hzn : ‖z‖ < 3 := by simpa only [mem_ball, dist_zero_right] using hz
  have huR : u ∈ closedBall (0 : Rd d) R := by
    rw [mem_closedBall, dist_zero_right]
    have hnorm : ‖u‖ ≤ s * ‖a‖ + ‖z‖ := by
      dsimp [u]
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hs] using norm_add_le (s • a) z
    rw [haNorm] at hnorm
    nlinarith only [hnorm, hzn, hs4, hR, hs]
  have hvR : v ∈ closedBall (0 : Rd d) R := by
    rw [mem_closedBall, dist_zero_right]
    have hnorm : ‖v‖ ≤ s * ‖bpt‖ + ‖z‖ := by
      dsimp [v]
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hs] using norm_add_le (s • bpt) z
    rw [hbNorm] at hnorm
    nlinarith only [hnorm, hzn, hs4, hR, hs]
  let Ghat : ContMetric d := (G.affine s hs.ne' z).smul S⁻¹ (inv_pos.mpr hS)
  have hdiam := hRefs.2.2.2.2
  have hGa : Ghat.1 (a, bpt) ≤ A0 := by
    have h₁ := Ghat.ofReal_le_internal (siteA d) a bpt
    have h₂ : Ghat.internal (siteA d) a bpt ≤ diamIn Ghat (siteA d) (siteC d) := by
      unfold diamIn
      exact le_iSup_of_le a (le_iSup_of_le hmemA
        (le_iSup_of_le bpt (le_iSup_of_le hmemB le_rfl)))
    exact (ENNReal.ofReal_le_ofReal_iff hA0.le).1 ((h₁.trans h₂).trans hdiam)
  have hGaScaled : S⁻¹ * G.1 (u, v) ≤ A0 := by
    simpa only [Ghat, u, v, ContMetric.smul_apply, ContMetric.affine_apply] using hGa
  have hGaPhysical : G.1 (u, v) ≤ A0 * S := by
    have h := mul_le_mul_of_nonneg_right hGaScaled hS.le
    have hcancel : (S⁻¹ * G.1 (u, v)) * S = G.1 (u, v) := by field_simp
    rw [hcancel] at h
    exact h
  have hlow := hglob u huR v hvR
  rw [hdiff] at hlow
  apply (div_le_iff₀ hA0).2
  nlinarith only [hlow, hGaPhysical]

/-- Equation (4.23): a referenced site unit is polynomially bounded on the inspected scales. -/
theorem siteUnit_bounds {d : ℕ} (hd : 3 ≤ d) (G : ContMetric d) (hG : G.IsLength)
    {z : Rd d} {s S R H σ β Hup σup Hlo b mc A0 : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hS : 0 < S) (hR : 16 ≤ R)
    (hH : 0 < H) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hβ : 1 ≤ β)
    (hmc : 0 < mc) (hA0 : 0 < A0) (hz : z ∈ ball (0 : Rd d) 3)
    (hglobUp : ∀ w ∈ closedBall (0 : Rd d) R, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      diamIn G (ball w (2 * r)) (ball w r) ≤ ENNReal.ofReal (H * r ^ σ))
    (hglobLow : ∀ u ∈ closedBall (0 : Rd d) R, ∀ v ∈ closedBall (0 : Rd d) R,
      H⁻¹ * ‖u - v‖ ^ β ≤ G.1 (u, v))
    (hRefs : SiteRefs Hup σup Hlo b mc A0
      ((G.affine s hs.ne' z).smul S⁻¹ (inv_pos.mpr hS))) :
    (H⁻¹ * (4 * s) ^ β / A0 ≤ S ∧ S ≤ H * (4 * s) ^ σ / mc) ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ min (1 / 4) (min (4 ^ β / (H * A0)) (mc / H)) →
        Δ ^ (2 : ℕ) ≤ s → s ≤ Δ →
          Δ ^ (2 * β + 1) ≤ S ∧ S ≤ Δ ^ (-(2 * β + 1)) := by
  have hR4 : 4 ≤ R := by linarith
  have hlow := q10_site_unit_lower (by omega : 1 ≤ d) G hs hs4 hS hR4 hH hA0 hz hglobLow hRefs
  have hmcS := q10_site_unit_upper (by omega : 1 ≤ d) G hG hs hs4 hS hR4 hH hmc hz hglobUp hRefs
  have hup : S ≤ H * (4 * s) ^ σ / mc :=
    (le_div_iff₀ hmc).2 (by nlinarith only [hmcS])
  refine ⟨⟨hlow, hup⟩, ?_⟩
  intro Δ hΔ hΔmax hΔs hsΔ
  have hΔq : Δ ≤ 1 / 4 := hΔmax.trans (min_le_left _ _)
  have hΔlo : Δ ≤ 4 ^ β / (H * A0) :=
    hΔmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔhi : Δ ≤ mc / H :=
    hΔmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact site_unit_window hH hA0 hmc hβ hσ hσ1 hΔ hΔq hΔs hsΔ hΔlo hΔhi hlow hup

end HigherDimLQGContinuity
