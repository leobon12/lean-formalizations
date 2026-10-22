import HigherDimLQGContinuity.Network.CountPower
import HigherDimLQGContinuity.Network.Diameter

/-! # The quantitative site network bound -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

def siteNetCnet {d : ℕ} (S : SiteData d) : ℝ :=
  1 + (4 / (1 - (1 / 2 : ℝ) ^ S.s)) * siteNetCountCoeff S

theorem siteNetCountCoeff_nonneg {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) : 0 ≤ siteNetCountCoeff S := by
  have hμ : 0 < siteMuCoeff d := siteMuCoeff_pos hd
  have hω : 0 < siteOmegaCoeff d := siteOmegaCoeff_pos d (by omega)
  have hL : 0 ≤ S.boxHalfSide := (S.boxHalfSide_pos hd).le
  have hCN : 0 ≤ siteCN d := (siteCN_pos d).le
  unfold siteNetCountCoeff
  positivity

theorem siteNetCnet_ge_one {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) : 1 ≤ siteNetCnet S := by
  have hpow : (1 / 2 : ℝ) ^ S.s < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) S.s_pos
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ S.s := by linarith
  unfold siteNetCnet
  have hc := siteNetCountCoeff_nonneg S hd
  have hnonneg : 0 ≤ (4 / (1 - (1 / 2 : ℝ) ^ S.s)) *
      siteNetCountCoeff S := mul_nonneg (div_nonneg (by norm_num) hden.le) hc
  linarith

/-- The exact network inequality (4.7), using the fixed count coefficient. -/
theorem labelNet_internal_bound {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S (siteNetCnet S) v))
    (hC : SiteConstsC S (siteConsts S (siteNetCnet S) v) v)
    {Kl : ℕ}
    (ℓ : SiteLabel S (labelCellCutoff S (siteConsts S (siteNetCnet S) v).μ) Kl
      (siteConsts S (siteNetCnet S) v).N (siteConsts S (siteNetCnet S) v).μ
      (siteConsts S (siteNetCnet S) v).ν (siteConsts S (siteNetCnet S) v).r
      (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S (siteNetCnet S) v).t₀)
    (D : ContMetric d) (hD : D.IsLength)
    (hDup : DUpper D (siteA d) S.Hup S.s)
    (x y : Rd d)
    (hx : x ∈ (labelNet S (siteConsts S (siteNetCnet S) v) ℓ).Uo)
    (hy : y ∈ (labelNet S (siteConsts S (siteNetCnet S) v) ℓ).Uo) :
    D.internal (labelNet S (siteConsts S (siteNetCnet S) v) ℓ).Uo x y ≤
      ENNReal.ofReal (siteConsts S (siteNetCnet S) v).Anet := by
  let Cnet := siteNetCnet S
  let C := siteConsts S Cnet v
  let F := labelBallSpecs ℓ C.g C.ω
  have hCnet : 0 < Cnet := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (siteNetCnet_ge_one S hd)
  have hball : ∀ p ∈ F, closedBall p.1 p.2 ⊆ siteA d := by
    intro p hp
    exact labelNet_ball_subset_siteA S hd Cnet v hCnet hv hv1 hA hC ℓ p hp
  have hmetric := q4_labelNet_internal_of_ball_bounds S hd Cnet v hv hv1
    ℓ hreal D hD hDup hball x y hx hy
  have hsum := labelBallSpecs_radius_sum_power S hd Cnet v hv ℓ
  have hpow : 0 ≤ C.ν ^ (-(8 * d : ℝ)) :=
    Real.rpow_nonneg (siteConsts_ν_pos S hd Cnet v).le _
  have hcount : 0 ≤ siteNetCountCoeff S := siteNetCountCoeff_nonneg S hd
  have hfac : 0 < 4 / (1 - (1 / 2 : ℝ) ^ S.s) := by
    have hsmall : (1 / 2 : ℝ) ^ S.s < 1 :=
      Real.rpow_lt_one (by norm_num) (by norm_num) S.s_pos
    positivity
  have hH : 0 ≤ S.Hup := by linarith [S.Hup_ge]
  have hcoef : (4 / (1 - (1 / 2 : ℝ) ^ S.s)) * siteNetCountCoeff S ≤ Cnet := by
    unfold Cnet siteNetCnet
    linarith
  have hbound : (4 / (1 - (1 / 2 : ℝ) ^ S.s)) * S.Hup *
      (∑ p ∈ F, p.2 ^ S.s) ≤ C.Anet := by
    have h1 := mul_le_mul_of_nonneg_left hsum (mul_nonneg hfac.le hH)
    have h2 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hH hpow)
    change (4 / (1 - (1 / 2 : ℝ) ^ S.s)) * S.Hup *
      (∑ p ∈ F, p.2 ^ S.s) ≤ Cnet * S.Hup * C.ν ^ (-(8 * d : ℝ))
    nlinarith
  have hmetric' : D.internal (labelNet S C ℓ).Uo x y ≤
      ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ S.s)) * S.Hup *
        (∑ p ∈ F, p.2 ^ S.s)) := by
    have heq : (∑ p : F, p.1.2 ^ S.s) =
        ∑ p ∈ F, p.2 ^ S.s :=
      Finset.sum_coe_sort F (fun p : Rd d × ℝ => p.2 ^ S.s)
    change D.internal (labelNet S C ℓ).Uo x y ≤
      ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ S.s)) * S.Hup *
        (∑ p : F, p.1.2 ^ S.s)) at hmetric
    rw [heq] at hmetric
    exact hmetric
  exact hmetric'.trans (ENNReal.ofReal_le_ofReal hbound)

end HigherDimLQGContinuity
