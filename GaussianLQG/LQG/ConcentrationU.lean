import GaussianLQG.LQG.Concentration
import GaussianLQG.LQG.Localization
import GaussianLQG.LQG.Geodesics
import GaussianLQG.LQG.Scaling

/-!
# Concentration of `log D(0, 1)`, unconditional form (blueprint Corollary `cor:logD-concentration`)

Blueprint Corollary `cor:logD-concentration` (source (3.4)) for an arbitrary `Setup`: for every
`p ≥ 1` there are `γ_* > 0` and `C_p` such that `‖log D^γ(0,1) - b_γ‖_p ≤ C_p ξ_γ` for
`γ ∈ (0, γ_*]` (`Setup.concentration`).

Proof (blueprint). The conditional form `Setup.eLpNorm_logD_sub_b_le_ennreal` gives
`‖log D^γ(0,1) - b_γ‖_p ≤ c_p ξ_γ ‖Θ‖_p` as soon as (i) geodesics from `0` to `1` exist a.s.
(Lemma `lem:geodesics-exist`, `Setup.exists_ae_geodesics`), (ii) every such geodesic has a regular
length measure with `ℰ(ν_η, ν_η) ≤ Θ²` a.s., and (iii) `log D^γ(0,1) ∈ L^p` (Lemma `lem:scaling`(a),
`Setup.memLp_log_D`). For (ii) take `Θ` of Lemma `lem:T-B` with `K = B̄_1(0)` and `δ = 1`
(`Setup.ae_localization`); its moments are bounded uniformly in small `γ`
(`Setup.exists_locMoments`), which makes the constant uniform.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

namespace Setup

variable (S : Setup)

/-- **Blueprint Corollary `cor:logD-concentration`** (source (3.4)). For every `p ≥ 1` there are
`γ_* > 0` and `C` such that `‖log D^γ(0,1) - b_γ‖_p ≤ C ξ_γ` for all `γ ∈ (0, γ_*]`. -/
theorem concentration : ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
    eLpNorm (fun ω => Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal (C * S.ξ γ) := by
  intro p hp
  have hp0 : 0 < p := by linarith
  have hA := S.holderScaling
  have hL := S.annulusScaling
  set K : Set ℂ := Metric.closedBall (0 : ℂ) 1 with hK
  have hKc : IsCompact K := isCompact_closedBall 0 1
  obtain ⟨γ1, hγ1, hmom⟩ := S.exists_locMoments hA hL p hp
  obtain ⟨C1, hC1, hC1b⟩ := hmom K hKc 1 one_pos
  obtain ⟨γT, hγT, hloc⟩ := S.ae_localization hA hL
  obtain ⟨γg, hγg, hγg2, hgeo⟩ := S.exists_ae_geodesics hL
  obtain ⟨γm, hγm, hmem⟩ := S.memLp_log_D p hp
  set cp : ℝ := Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p) with hcp
  have hcp0 : 0 ≤ cp :=
    mul_nonneg (by positivity)
      (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _) _)
  have hC1p : C1 ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hC1
  refine ⟨min (min γ1 γT) (min γg γm), cp * (C1 ^ (1 / p)).toReal,
    lt_min (lt_min hγ1 hγT) (lt_min hγg hγm), fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγ1' : γ ≤ γ1 := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγT' : γ ≤ γT := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγg' : γ ≤ γg := hγle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγm' : γ ≤ γm := hγle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := lt_of_le_of_lt hγg' hγg2
  -- (i) geodesics from `0` to `1`
  have hgeo01 : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η := by
    filter_upwards [hgeo γ ⟨hγ0, hγg'⟩] with ω hω using hω.2.2.2 0 1
  -- (ii) the energy majorant `Θ` of Lemma `lem:T-B` with `K = B̄_1(0)`, `δ = 1`
  have h0K : (0 : ℂ) ∈ K := Metric.mem_closedBall_self zero_le_one
  have h1K : (1 : ℂ) ∈ K := by
    rw [hK, mem_closedBall_zero_iff, norm_one]
  have h01 : (1 : ℝ) ≤ ‖(0 : ℂ) - 1‖ := by
    rw [zero_sub, norm_neg, norm_one]
  have hΘ : ∀ᵐ ω ∂stdP, ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η →
      IsRegular (lengthMeasure η) ∧
        ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η)) ≤
          S.locTheta γ K 1 ω ^ 2 := by
    filter_upwards [hloc γ ⟨hγ0, hγT'⟩ K hKc 1 one_pos] with ω hω η hη
    obtain ⟨-, -, hΘtop, hgeod⟩ := hω
    obtain ⟨-, -, hreg, hE⟩ := hgeod 0 h0K 1 h1K h01 η hη
    refine ⟨hreg, ?_⟩
    calc ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η))
        ≤ ENNReal.ofReal ((S.locTheta γ K 1 ω).toReal ^ 2) := ENNReal.ofReal_le_ofReal hE
      _ = S.locTheta γ K 1 ω ^ 2 := by
          rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hΘtop]
  -- (iii) integrability
  have hFp := hmem γ ⟨hγ0, hγm'⟩
  have hmain := S.eLpNorm_logD_sub_b_le_ennreal hγ0 hγ2 hp hgeo01 hΘ hFp
  -- the `L^p` norm of `Θ` is bounded uniformly
  have hΘp : eLpNorm (S.locTheta γ K 1) (ENNReal.ofReal p) stdP ≤ C1 ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    simp_rw [enorm_eq_self]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine le_trans (lintegral_mono fun ω => ?_) (hC1b γ ⟨hγ0, hγ1'⟩).2
    exact le_add_self
  calc eLpNorm (fun ω => Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) (ENNReal.ofReal p) stdP
      ≤ ENNReal.ofReal cp * ENNReal.ofReal (S.ξ γ) *
          eLpNorm (S.locTheta γ K 1) (ENNReal.ofReal p) stdP := hmain
    _ ≤ ENNReal.ofReal cp * ENNReal.ofReal (S.ξ γ) * C1 ^ (1 / p) := by gcongr
    _ = ENNReal.ofReal (cp * (C1 ^ (1 / p)).toReal * S.ξ γ) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hcp0 ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul hcp0, ENNReal.ofReal_toReal hC1p]
        ring

end Setup

end GaussianLQG
