import GaussianLQG.LQG.Euclid
import GaussianLQG.LQG.Euclid.Coupling
import GaussianLQG.LQG.Euclid.Moments
import GaussianLQG.LQG.Localization

/-!
# Convergence in energy (blueprint Lemma `lem:energy-approx`)

For compact `K`, `δ > 0` and `p ≥ 1` there are `γ_* > 0` and `C` such that for every
`γ ∈ (0, γ_*]` there is a measurable `Y_γ ≥ 0` with `E[Y_γ^p] ≤ C ξ_γ^{p/24}` and, almost surely,
`‖ν_η - λ_{z,w}‖_*² ≤ Y_γ²` for all `z, w ∈ K` with `|z - w| ≥ δ` and every constant-speed
`D^γ`-geodesic `η` from `z` to `w`, whose length measure `ν_η` is moreover regular
(`Setup.energyApprox : S.EnergyApprox`).

Proof (blueprint). Let `R₁ ≥ 1` with `K ⊆ B̄_{R₁-1}(0)`, `R = 4R₁`, `ε₀ = min(R₁/4, 1/(16R₁))`,
`𝖤 = 𝖤_γ(R)` (Lemma `lem:euclidean`) and `T, B, Θ` as in Lemma `lem:T-B`. On the event of Lemma
`lem:T-B`:
* on the good event `{𝖤 ≤ ε₀}`, the tube lemma and the coupling estimate (`energy_quad_le_of_tube`)
  give `‖ν_η - λ‖_*² ≤ 2 (1 + B + 2/δ) (8 R₁ 𝖤)^{1/6} ≤ c₁² (1 + B) 𝖤^{1/6}`;
* off it, `‖ν_η - λ‖_*² ≤ 2ℰ(ν_η,ν_η) + 2ℰ(λ,λ) ≤ 2Θ² + 2Λ² ≤ (2(Θ + Λ))²`, with
  `Λ² = 2 log max(1, 2/δ) + 2 + 2 log R₁ ≥ ℰ(λ_{z,w}, λ_{z,w})` (Lemma `lem:energy-bound`).
So `Y = c₁ (1 + B)^{1/2} 𝖤^{1/12} 1_{𝖤 ≤ ε₀} + 2(Θ + Λ) 1_{𝖤 > ε₀}` (`energyY`) works, and its
moments are bounded by `exists_lintegral_energyY_le` from Lemma `lem:T-B` (moments of `B`, `Θ`) and
Lemma `lem:euclidean` (moments of `𝖤`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-- `(c (1 + B)^{1/2} E^{1/12})² = c² (1 + B) E^{1/6}` in `[0, ∞]`. -/
theorem sq_ofReal_mul_rpow_mul_rpow (c : ℝ) (B E : ℝ≥0∞) :
    (ENNReal.ofReal c * (1 + B) ^ (1 / 2 : ℝ) * E ^ (1 / 12 : ℝ)) ^ 2 =
      ENNReal.ofReal c ^ 2 * (1 + B) * E ^ (1 / 6 : ℝ) := by
  rw [mul_pow, mul_pow, ← ENNReal.rpow_natCast ((1 + B) ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_natCast (E ^ (1 / 12 : ℝ)), ← ENNReal.rpow_mul]
  norm_num

namespace Setup

variable (S : Setup)

/-- **Blueprint Lemma `lem:energy-approx`.** For compact `K`, `δ > 0` and `p ≥ 1` there are
`γ_* > 0` and `C` such that for `γ ∈ (0, γ_*]` some measurable `Y_γ ≥ 0` has
`E[Y_γ^p] ≤ C ξ_γ^{p/24}`, and almost surely, for all `z, w ∈ K` with `|z - w| ≥ δ` and every
constant-speed geodesic `η` from `z` to `w`, `ν_η` is regular and `‖ν_η - λ_{z,w}‖_*² ≤ Y_γ²`. -/
theorem energyApprox : S.EnergyApprox := by
  intro K hK δ hδ p hp
  have hp0 : 0 < p := by linarith
  have hA := S.holderScaling
  have hL := S.annulusScaling
  -- the geometry: `K ⊆ B̄_{R₁-1}(0)`, `R = 4R₁`, `ε₀ = min(R₁/4, 1/(16R₁))`
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R₁ : ℝ := max r 0 + 1 with hR₁_def
  have hR₁ : 1 ≤ R₁ := by linarith [le_max_right r 0]
  have hKR : K ⊆ Metric.closedBall 0 (R₁ - 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (by rw [hR₁_def]; linarith [le_max_left r 0]))
  have hRb : 1 ≤ 4 * R₁ := by linarith
  set ε0 : ℝ := min (R₁ / 4) (1 / (16 * R₁)) with hε0_def
  have hε0 : 0 < ε0 := lt_min (by linarith) (by positivity)
  -- the constants
  have hc1sq0 : 0 ≤ 2 * (1 + 2 / δ) * (8 * R₁) ^ (1 / 6 : ℝ) := by positivity
  set c1 : ℝ := Real.sqrt (2 * (1 + 2 / δ) * (8 * R₁) ^ (1 / 6 : ℝ)) with hc1_def
  set Λ2 : ℝ := 2 * Real.log (max 1 (2 / δ)) + 2 + 2 * Real.log R₁ with hΛ2_def
  have hΛ2 : 0 ≤ Λ2 := by
    have h1 := Real.log_nonneg (le_max_left 1 (2 / δ))
    have h2 := Real.log_nonneg hR₁
    linarith
  set Λ : ℝ := Real.sqrt Λ2 with hΛ_def
  -- the inputs
  obtain ⟨γE, CE, hγE, hEuc⟩ := S.euclidApprox (4 * R₁) hRb p hp
  obtain ⟨γl, hγl, hmom⟩ := S.exists_locMoments hA hL (2 * p) (by linarith)
  obtain ⟨Cl, hCl, hClb⟩ := hmom K hK δ hδ
  obtain ⟨γl1, hγl1, hmom1⟩ := S.exists_locMoments hA hL p hp
  obtain ⟨Cl1, hCl1, hCl1b⟩ := hmom1 K hK δ hδ
  obtain ⟨γT, hγT, hloc⟩ := S.ae_localization hA hL
  obtain ⟨γe, C1, hγe, hγe2, hexp⟩ := S.exists_exponents
  obtain ⟨C, hC⟩ := exists_lintegral_energyY_le hp c1 Λ ε0 (max CE 0) hε0 hCl1 hCl
  refine ⟨min (min γE γl) (min (min γl1 γT) γe), C,
    lt_min (lt_min hγE hγl) (lt_min (lt_min hγl1 hγT) hγe), fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγE' : γ ≤ γE := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγl' : γ ≤ γl := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγl1' : γ ≤ γl1 :=
    hγle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hγT' : γ ≤ γT :=
    hγle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hγe' : γ ≤ γe := hγle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := lt_of_le_of_lt hγe' hγe2
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ0 hγ2
  have hξ1 : S.ξ γ ≤ 1 := (hexp γ ⟨hγ0, hγe'⟩).2.2.1.trans (by norm_num)
  have hBm := (S.measurable_loc γ K δ).2.1
  have hΘm := (S.measurable_loc γ K δ).2.2
  have hEm := S.measurable_euclidErr γ (4 * R₁)
  refine ⟨fun ω => energyY c1 Λ ε0 (S.locB γ K δ ω) (S.locTheta γ K δ ω)
    (S.euclidErr γ (4 * R₁) ω), measurable_energyY c1 Λ ε0 hBm hΘm hEm, ?_, ?_⟩
  · -- the moments
    have hBp : ∫⁻ ω, S.locB γ K δ ω ^ p ∂stdP ≤ Cl1 := by
      refine le_trans (lintegral_mono fun ω => ?_) (hCl1b γ ⟨hγ0, hγl1'⟩).2
      exact le_add_right le_add_self
    have hΘp : ∫⁻ ω, S.locTheta γ K δ ω ^ (2 * p) ∂stdP ≤ Cl := by
      refine le_trans (lintegral_mono fun ω => ?_) (hClb γ ⟨hγ0, hγl'⟩).2
      exact le_add_self
    have hEp : ∫⁻ ω, S.euclidErr γ (4 * R₁) ω ^ p ∂stdP ≤
        ENNReal.ofReal (max CE 0 * S.ξ γ ^ (p / 2)) :=
      (hEuc γ ⟨hγ0, hγE'⟩).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (Real.rpow_nonneg hξ.le _)))
    exact hC hBm hΘm hEm hξ hξ1 hBp hΘp hEp
  · -- the almost-sure bound
    filter_upwards [hloc γ ⟨hγ0, hγT'⟩ K hK δ hδ] with ω hω
    obtain ⟨-, hB, hΘ, hgeod⟩ := hω
    intro z hz w hw hzw η hη
    obtain ⟨-, hball, hreg, hEν⟩ := hgeod z hz w hw hzw η hη
    refine ⟨hreg, ?_⟩
    set Eω := S.euclidErr γ (4 * R₁) ω with hEω_def
    set B := S.locB γ K δ ω with hB_def
    set Θ := S.locTheta γ K δ ω with hΘ_def
    have hz1 : ‖z‖ ≤ R₁ - 1 := mem_closedBall_zero_iff.1 (hKR hz)
    have hw1 : ‖w‖ ≤ R₁ - 1 := mem_closedBall_zero_iff.1 (hKR hw)
    obtain ⟨hsreg, hsE⟩ := energy_segMeasure_le_of_mem hR₁ hδ hz1 hw1 hzw
    unfold energyY
    split_ifs with hG
    · -- the good event: tube lemma and coupling
      have hEtop : Eω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hG
      have hE : ∀ x ∈ Metric.closedBall (0 : ℂ) (4 * R₁), ∀ y ∈ Metric.closedBall (0 : ℂ) (4 * R₁),
          |Real.exp (-S.b γ) * (S.D γ ω).1 (x, y) - ‖x - y‖| ≤ Eω.toReal := by
        intro x hx y hy
        rw [← ENNReal.ofReal_le_iff_le_toReal hEtop, hEω_def]
        unfold euclidErr
        exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
      have hE₀ : Eω.toReal ≤ min (R₁ / 4) (1 / (16 * R₁)) :=
        ENNReal.toReal_le_of_le_ofReal hε0.le hG
      have hQ := energy_quad_le_of_tube hR₁ hKR hE hE₀ hδ ENNReal.toReal_nonneg hz hw hzw hη hreg
        hball
      have hE0 : 0 ≤ Eω.toReal := ENNReal.toReal_nonneg
      have hBt : 0 ≤ B.toReal := ENNReal.toReal_nonneg
      have hreal : 2 * (1 + B.toReal + 2 / δ) * (8 * R₁ * Eω.toReal) ^ (1 / 6 : ℝ) ≤
          c1 ^ 2 * (1 + B.toReal) * Eω.toReal ^ (1 / 6 : ℝ) := by
        rw [hc1_def, Real.sq_sqrt hc1sq0, Real.mul_rpow (by positivity) hE0]
        have h1 : 1 + B.toReal + 2 / δ ≤ (1 + 2 / δ) * (1 + B.toReal) := by
          have : 0 ≤ 2 / δ * B.toReal := by positivity
          nlinarith
        have h2 : 0 ≤ (8 * R₁) ^ (1 / 6 : ℝ) * Eω.toReal ^ (1 / 6 : ℝ) := by positivity
        calc 2 * (1 + B.toReal + 2 / δ) * ((8 * R₁) ^ (1 / 6 : ℝ) * Eω.toReal ^ (1 / 6 : ℝ))
            ≤ 2 * ((1 + 2 / δ) * (1 + B.toReal)) *
                ((8 * R₁) ^ (1 / 6 : ℝ) * Eω.toReal ^ (1 / 6 : ℝ)) := by gcongr
          _ = 2 * (1 + 2 / δ) * (8 * R₁) ^ (1 / 6 : ℝ) * (1 + B.toReal) *
                Eω.toReal ^ (1 / 6 : ℝ) := by ring
      rw [sq_ofReal_mul_rpow_mul_rpow]
      calc ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η) -
            2 * energy (lengthMeasure η) (segMeasure z w) +
              energy (segMeasure z w) (segMeasure z w))
          ≤ ENNReal.ofReal (c1 ^ 2 * (1 + B.toReal) * Eω.toReal ^ (1 / 6 : ℝ)) :=
            ENNReal.ofReal_le_ofReal (hQ.trans hreal)
        _ = ENNReal.ofReal c1 ^ 2 * (1 + B) * Eω ^ (1 / 6 : ℝ) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_pow (Real.sqrt_nonneg _),
              ENNReal.ofReal_add zero_le_one hBt, ENNReal.ofReal_one, ENNReal.ofReal_toReal hB,
              ← ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num), ENNReal.ofReal_toReal hEtop]
    · -- off the good event: `‖ν - λ‖_*² ≤ 2Θ² + 2Λ²`
      have hQ := energy_quad_le_two_mul S.frame hreg hsreg
      have hΘt : 0 ≤ Θ.toReal := ENNReal.toReal_nonneg
      have hΛ0 : 0 ≤ Λ := Real.sqrt_nonneg _
      have hΛsq : Λ ^ 2 = Λ2 := Real.sq_sqrt hΛ2
      have hreal : 2 * energy (lengthMeasure η) (lengthMeasure η) +
          2 * energy (segMeasure z w) (segMeasure z w) ≤ (2 * (Θ.toReal + Λ)) ^ 2 := by
        have h1 : 2 * energy (lengthMeasure η) (lengthMeasure η) ≤ 2 * Θ.toReal ^ 2 := by
          linarith
        have h2 : 2 * energy (segMeasure z w) (segMeasure z w) ≤ 2 * Λ ^ 2 := by
          rw [hΛsq]
          linarith
        nlinarith [mul_nonneg hΘt hΛ0]
      calc ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η) -
            2 * energy (lengthMeasure η) (segMeasure z w) +
              energy (segMeasure z w) (segMeasure z w))
          ≤ ENNReal.ofReal ((2 * (Θ.toReal + Λ)) ^ 2) :=
            ENNReal.ofReal_le_ofReal (hQ.trans hreal)
        _ = (2 * (Θ + ENNReal.ofReal Λ)) ^ 2 := by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul zero_le_two,
              ENNReal.ofReal_add hΘt hΛ0, ENNReal.ofReal_toReal hΘ, ENNReal.ofReal_ofNat]

end Setup

end GaussianLQG
