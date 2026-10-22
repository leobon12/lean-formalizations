import HigherDimLQGMetric.Freq.Telescope
import HigherDimLQGMetric.Proper.Proper

/-! The deterministic contradiction behind Proposition 5.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open scoped ENNReal

variable {d : ℕ}

/-- On confinement, modulus and shell-cover events, the ratio event cannot
occur. All probability estimates are separated from this deterministic fact. -/
theorem s4c_no_G_of_cover
    (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ t u β R ε α Lcov : ℝ)
    (g : DistRd d)
    (hA : (A g).IsLength) [ProperSpace (A g).Space]
    (hratio : ∀ x y : Rd d, (B g).1 (x, y) ≤ U * (A g).1 (x, y))
    (hℓ : 0 < ℓ) (hℓa : ℓ < a / 100) (haA₀ : 0 < a ∧ a < A₀)
    (ht : 0 < t) (htU : t < U) (hKu : U - a / A₀ * (U - t) < u)
    (hR : 0 < R) (hε : 0 < ε)
    (hε1 : ε < 1 / 8) (hεβ : 8 * ε < β)
    (hgap : 2 * U * (8 * ε) ^ α <
      (u - (U - a / A₀ * (U - t))) * β)
    (T : Finset ℤ) (hT : ∀ j ∈ T, j ∈ scaleWin ε R)
    (hconf : ¬ ∃ (γ : ℝ → Rd d) (L : ℝ), 0 ≤ L ∧
      IsGeodesicCurve ((A g).pt ∘ γ) 0 L ∧
      ‖γ 0‖ < 3 * R ∧ ‖γ L‖ < 3 * R ∧
      ∃ s ∈ Icc (0 : ℝ) L, Lcov * R ≤ ‖γ s‖)
    (hmod : ¬ ∃ x y : Rd d, ‖x‖ < 3 * R ∧ ‖y‖ < 3 * R ∧
      ‖x - y‖ ≤ 8 * ε * R ∧
      (8 * ε) ^ α * sNorm ξ Q g R 0 < (A g).1 (x, y))
    (hcov : ∀ w ∈ ball (0 : Rd d) (Lcov * R),
      ∃ j ∈ T, ∃ k : Fin d → ℤ,
        ‖w - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
        g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ ((64 : ℝ) ^ j)
          (latPt ((64 : ℝ) ^ j / (100 * d)) k) \
            WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j)
              (latPt ((64 : ℝ) ^ j / (100 * d)) k)) :
    g ∉ GEvent A B ξ Q u β R := by
  intro hG
  obtain ⟨x, hx, y, hy, hxy, hAlong, hAhigh, hBhigh⟩ := hG
  let D := A g
  let E := B g
  let L := D.1 (x, y)
  let q := 4 * ε * R
  let M := (8 * ε) ^ α * sNorm ξ Q g R 0
  have hU : 0 < U := ht.trans htU
  have hq : 0 < q := by dsimp [q]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.rpow_pos_of_pos (by positivity) α).le
      (sNorm_pos ξ Q g hR 0).le
  have hx2 : ‖x‖ ≤ 2 * R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hy2 : ‖y‖ ≤ 2 * R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hx3 : ‖x‖ < 3 * R := by linarith only [hx2, hR]
  have hy3 : ‖y‖ < 3 * R := by linarith only [hy2, hR]
  have hxy8 : 8 * ε * R < ‖x - y‖ := by
    have hmul := mul_lt_mul_of_pos_right hεβ hR
    linarith only [hmul, hxy]
  obtain ⟨P, hP0, hPL, hgeo, hu, hdist⟩ := D.exists_geodesic hA x y
  have hL : 0 ≤ L := hgeo.1
  have hPc : ContinuousOn P (Icc 0 L) := D.continuousOn_pt_comp_iff.mp hgeo.2.1
  have hunit : ∀ s ∈ Icc 0 L, ∀ v ∈ Icc 0 L, s ≤ v →
      D.len P s v = ENNReal.ofReal (v - s) ∧ D.1 (P s, P v) = v - s := by
    intro s hs v hv hsv
    constructor
    · exact curveLength_of_hasUnitSpeedOn hu hs hv
    · rw [hdist s hs v hv, abs_of_nonneg (sub_nonneg.mpr hsv)]
  have hPconf : ∀ s ∈ Icc 0 L, ‖P s‖ < Lcov * R := by
    intro s hs
    by_contra hn
    have hbad : Lcov * R ≤ ‖P s‖ := le_of_not_gt hn
    exact hconf ⟨P, L, hL, hgeo, by rw [hP0]; exact hx3,
      by rw [hPL]; exact hy3, s, hs, hbad⟩
  obtain ⟨a₀, b₀, ha₀, hab, hbL, hPa, hPb, hafterX, hbeforeY⟩ :=
    s4c_macro_times P x y hL hq hPc hP0 hPL (by dsimp [q]; linarith only [hxy8])
  have hεR : 0 < ε * R := mul_pos hε hR
  have hq8 : q ≤ 8 * ε * R := by dsimp [q]; linarith only [hεR.le]
  have hqR : q < R := by dsimp [q]; nlinarith only [hε1, hε, hR]
  have hPa3 : ‖P a₀‖ < 3 * R := by
    have htri : ‖P a₀‖ ≤ ‖P a₀ - x‖ + ‖x‖ := by
      calc
        ‖P a₀‖ = ‖(P a₀ - x) + x‖ := by congr 1; abel
        _ ≤ ‖P a₀ - x‖ + ‖x‖ := norm_add_le _ _
    linarith only [htri, hPa, hx2, hqR]
  have hPb3 : ‖P b₀‖ < 3 * R := by
    have htri : ‖P b₀‖ ≤ ‖P b₀ - y‖ + ‖y‖ := by
      calc
        ‖P b₀‖ = ‖(P b₀ - y) + y‖ := by congr 1; abel
        _ ≤ ‖P b₀ - y‖ + ‖y‖ := norm_add_le _ _
    linarith only [htri, hPb, hy2, hqR]
  have hAfirst : D.1 (x, P a₀) ≤ M := by
    have hmod' : ¬ M < D.1 (x, P a₀) := by
      intro hbad
      exact hmod ⟨x, P a₀, hx3, hPa3, by
        rw [norm_sub_rev]
        exact hPa.trans_le hq8, hbad⟩
    exact le_of_not_gt hmod'
  have hAlast : D.1 (P b₀, y) ≤ M := by
    have hmod' : ¬ M < D.1 (P b₀, y) := by
      intro hbad
      exact hmod ⟨P b₀, y, hPb3, hy3, hPb.le.trans hq8, hbad⟩
    exact le_of_not_gt hmod'
  have haI : a₀ ∈ Icc 0 L := ⟨ha₀.le, hab.le.trans hbL⟩
  have hbI : b₀ ∈ Icc 0 L := ⟨ha₀.le.trans hab.le, hbL⟩
  have hfirst : a₀ ≤ M := by
    have hdist := (hunit 0 ⟨le_rfl, hL⟩ a₀ haI ha₀.le).2
    simp only [sub_zero] at hdist
    rw [hP0] at hdist
    exact hdist ▸ hAfirst
  have hlast : L - b₀ ≤ M := by
    rw [← (hunit b₀ hbI L ⟨hL, le_rfl⟩ hbL).2, hPL]
    exact hAlast
  have hfar : ∀ s ∈ Ico a₀ b₀,
      4 * (ε * R) ≤ ‖P s - x‖ ∧ 4 * (ε * R) ≤ ‖P s - y‖ := by
    intro s hs
    constructor
    · by_cases hsa : s = a₀
      · rw [hsa, hPa]
        dsimp [q]
        nlinarith
      · have hslt : a₀ < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
        simpa only [q, mul_assoc] using
          (hafterX s ⟨hslt, hs.2.le.trans hbL⟩).le
    · simpa only [q, mul_assoc] using (hbeforeY s hs).le
  have hcover : ∀ s ∈ Ico a₀ b₀, ∃ r : ℝ, ∃ z : Rd d,
      ε ^ 2 * R ≤ r ∧ r ≤ ε * R ∧ ‖P s - z‖ < r / 2 ∧
      g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z \
        WitEvent A B ξ Q U a A₀ ℓ β₀ t r z := by
    intro s hs
    have hsI : s ∈ Icc 0 L := ⟨ha₀.le.trans hs.1, hs.2.le.trans hbL⟩
    have hball : P s ∈ ball (0 : Rd d) (Lcov * R) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hPconf s hsI
    obtain ⟨j, hj, k, hnear, hgood⟩ := hcov (P s) hball
    let r : ℝ := (64 : ℝ) ^ j
    let z : Rd d := latPt (r / (100 * d)) k
    exact ⟨r, z, (hT j hj).1, (hT j hj).2, hnear, hgood⟩
  have hK0 : 0 ≤ U - a / A₀ * (U - t) := by
    have hA₀pos : 0 < A₀ := haA₀.1.trans haA₀.2
    have hfrac : a / A₀ < 1 := (div_lt_one hA₀pos).2 haA₀.2
    have hfrac0 : 0 ≤ a / A₀ := div_nonneg haA₀.1.le (by linarith [haA₀.2])
    nlinarith only [hfrac, hfrac0, ht.le, htU.le]
  have htel := s4c_telescope A B ξ Q U a A₀ ℓ β₀ t g hℓ hℓa
    (by linarith [haA₀.2]) ht.le htU.le hA hratio P x y hP0 hPL
    ha₀.le hab.le hbL hPc hunit (by positivity : 0 < ε ^ 2 * R)
    hfar hcover hM hfirst hlast hK0
  have hsR : 0 < sNorm ξ Q g R 0 := sNorm_pos ξ Q g hR 0
  have hdiff : 0 < u - (U - a / A₀ * (U - t)) := sub_pos.mpr hKu
  have hgap' : 2 * U * M <
      (u - (U - a / A₀ * (U - t))) * β * sNorm ξ Q g R 0 := by
    dsimp [M]
    calc
      2 * U * ((8 * ε) ^ α * sNorm ξ Q g R 0) =
          (2 * U * (8 * ε) ^ α) * sNorm ξ Q g R 0 := by ring
      _ < ((u - (U - a / A₀ * (U - t))) * β) * sNorm ξ Q g R 0 :=
        mul_lt_mul_of_pos_right hgap hsR
  have hgap'' : (u - (U - a / A₀ * (U - t))) * β * sNorm ξ Q g R 0 ≤
      (u - (U - a / A₀ * (U - t))) * L := by
    calc
      (u - (U - a / A₀ * (U - t))) * β * sNorm ξ Q g R 0 =
          (u - (U - a / A₀ * (U - t))) * (β * sNorm ξ Q g R 0) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAlong hdiff.le
  have hBhigh' : u * L < E.1 (x, y) := hBhigh
  linarith only [htel, hgap', hgap'', hBhigh']

end HigherDimLQGMetric
