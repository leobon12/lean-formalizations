import GaussianLQG.LQG.Derivative
import GaussianLQG.Probability.GaussianLp

/-!
# Concentration of `log D(0, 1)` (blueprint Corollary `cor:logD-concentration`)

Blueprint Corollary `cor:logD-concentration` (source (3.4)), in conditional form: the energy bound
`‖ν_η‖_* ≤ Θ` along geodesics (blueprint Lemma `lem:T-B` with `K = B̄_1(0)`, `δ = 1`), the existence
of geodesics (Lemma `lem:geodesics-exist`) and the integrability of `log D(0, 1)` (Lemma
`lem:scaling` (a)) are hypotheses, to be discharged by the packets proving those lemmas.

`Setup.eLpNorm_logD_sub_b_le`: for `0 < γ < 2`, `1 ≤ p` and `Θ : ℝ^ℕ → ℝ` such that a.s.
a constant-speed geodesic from `0` to `1` exists, and a.s. every such geodesic `η` has a regular
length measure with `ℰ(ν_η, ν_η) ≤ Θ²`, and `log D(0, 1) ∈ L^p`:
`‖log D^γ(0, 1) - b_γ‖_p ≤ c_p ξ_γ ‖Θ‖_p`, with `c_p = (π/2) ‖N‖_p` the constant of
`GaussianLQG.gaussian_Lp_inequality`. `Setup.eLpNorm_logD_sub_b_le_ennreal` is the same statement
for a `[0, ∞]`-valued `Θ` (with `ofReal ℰ(ν_η, ν_η) ≤ Θ²`). No measurability of `Θ` is needed.

Proof (blueprint). Lemma `lem:derivative` (a) gives hypothesis (H) of the Gaussian `L^p` inequality
with `L_j = ξ ‖e_j‖_∞`. Almost surely, by Lemma `lem:derivative` (b) (`∂_j F = ξ ∫ e_j dν_η`) and the
frame identity (`IsGFFFrame`, with `μ = ν = ν_η`),
`∑_j (∂_j F)² = ξ² ∑_j (∫ e_j dν_η)² = ξ² ℰ(ν_η, ν_η) ≤ ξ² Θ²`.
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

/-- The square function of `log D(z, w)`: almost surely, if some geodesic from `z` to `w` exists
and every such geodesic `η` has a regular length measure with `ℰ(ν_η, ν_η) ≤ Θ²`
(`Θ` valued in `[0, ∞]`), then `∑_j (∂_j F)² ≤ (ξ Θ)²`. -/
theorem ae_tsum_coordDeriv_sq_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {z w : ℂ} (hzw : z ≠ w)
    {Θ : Coord → ℝ≥0∞}
    (hgeo : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η)
    (hΘ : ∀ᵐ ω ∂stdP, ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η →
      IsRegular (lengthMeasure η) ∧
        ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η)) ≤ Θ ω ^ 2) :
    ∀ᵐ ω ∂stdP, (∑' j, ENNReal.ofReal
        (coordDeriv (fun ω => Real.log ((S.D γ ω).1 (z, w))) j ω ^ 2)) ≤
      (ENNReal.ofReal (S.ξ γ) * Θ ω) ^ 2 := by
  filter_upwards [S.ae_coordDeriv_logD_eq hγ hγ2 hzw, hgeo, hΘ] with ω hd hg hθ
  obtain ⟨η, hη⟩ := hg
  obtain ⟨hreg, hE⟩ := hθ η hη
  have hsum := (S.frame.2.2 _ _ hreg hreg).mul_left (S.ξ γ ^ 2)
  have hterm : ∀ j, coordDeriv (fun ω => Real.log ((S.D γ ω).1 (z, w))) j ω ^ 2 =
      S.ξ γ ^ 2 * ((∫ x, S.e j x ∂(lengthMeasure η)) * (∫ x, S.e j x ∂(lengthMeasure η))) :=
    fun j => by rw [hd j η hη]; ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (mul_self_nonneg _))
    hsum.summable, hsum.tsum_eq, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_pow (S.ξ_pos γ hγ hγ2).le, mul_pow]
  exact mul_le_mul' le_rfl hE

/-- `(∫⁻ ((ofReal ξ) Θ)^{2 · p/2})^{1/p} = ofReal ξ · ‖Θ‖_p` for `p > 0` and `Θ` valued in
`[0, ∞]`. -/
theorem lintegral_ofReal_mul_sq_rpow (ξ : ℝ) {p : ℝ} (hp : 0 < p) (Θ : Coord → ℝ≥0∞) :
    (∫⁻ ω, ((ENNReal.ofReal ξ * Θ ω) ^ 2) ^ (p / 2) ∂stdP) ^ (1 / p) =
      ENNReal.ofReal ξ * eLpNorm Θ (ENNReal.ofReal p) stdP := by
  have hpt : ∀ ω, ((ENNReal.ofReal ξ * Θ ω) ^ 2) ^ (p / 2) =
      ENNReal.ofReal ξ ^ p * ‖Θ ω‖ₑ ^ p := fun ω => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring,
      ENNReal.mul_rpow_of_nonneg _ _ hp.le, enorm_eq_self]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hp.le), one_div,
    ENNReal.rpow_rpow_inv hp.ne',
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, one_div]

/-- **Blueprint Corollary `cor:logD-concentration`** (source (3.4)), conditional form with a
`[0, ∞]`-valued majorant. Let `0 < γ < 2`, `1 ≤ p`, and `Θ : ℝ^ℕ → [0, ∞]` such that (i) a.s. there
is a constant-speed `D^γ`-geodesic from `0` to `1`; (ii) a.s. every such geodesic `η` has a regular
length measure with `ℰ(ν_η, ν_η) ≤ Θ²`; (iii) `log D^γ(0, 1) ∈ L^p`. Then
`‖log D^γ(0, 1) - b_γ‖_p ≤ c_p ξ_γ ‖Θ‖_p`, `c_p = (π/2) (E|N|^p)^{1/p}`. -/
theorem eLpNorm_logD_sub_b_le_ennreal {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {p : ℝ} (hp : 1 ≤ p)
    {Θ : Coord → ℝ≥0∞}
    (hgeo : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η)
    (hΘ : ∀ᵐ ω ∂stdP, ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η →
      IsRegular (lengthMeasure η) ∧
        ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η)) ≤ Θ ω ^ 2)
    (hFp : MemLp (fun ω => Real.log ((S.D γ ω).1 (0, 1))) (ENNReal.ofReal p) stdP) :
    eLpNorm (fun ω => Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)) *
        ENNReal.ofReal (S.ξ γ) * eLpNorm Θ (ENNReal.ofReal p) stdP := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ω, hΩm, hΩc, hH⟩ := S.exists_logD_shiftLipschitz hγ hγ2
  have hW1 := gaussian_Lp_inequality (F := fun ω => Real.log ((S.D γ ω).1 (0, 1)))
    (S.measurable_log_D γ 0 1) hΩm hΩc (L := fun j => S.ξ γ * S.supE j)
    (fun ω hω v v' => hH ω hω 0 1 zero_ne_one v v') hp hFp
  have hsq := S.ae_tsum_coordDeriv_sq_le hγ hγ2 zero_ne_one hgeo hΘ
  rw [mul_assoc, ← lintegral_ofReal_mul_sq_rpow (S.ξ γ) hp0 Θ]
  refine hW1.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (lintegral_mono_ae ?_)
    (one_div_nonneg.2 hp0.le)))
  filter_upwards [hsq] with ω hω
  exact ENNReal.rpow_le_rpow hω (by positivity)

/-- **Blueprint Corollary `cor:logD-concentration`** (source (3.4)), conditional form. Let
`0 < γ < 2`, `1 ≤ p`, and `Θ : ℝ^ℕ → ℝ` such that (i) a.s. there is a constant-speed
`D^γ`-geodesic from `0` to `1`; (ii) a.s. every such geodesic `η` has a regular length measure with
`ℰ(ν_η, ν_η) ≤ Θ²`; (iii) `log D^γ(0, 1) ∈ L^p`. Then
`‖log D^γ(0, 1) - b_γ‖_p ≤ c_p ξ_γ ‖Θ‖_p`, `c_p = (π/2) (E|N|^p)^{1/p}`. -/
theorem eLpNorm_logD_sub_b_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {p : ℝ} (hp : 1 ≤ p)
    {Θ : Coord → ℝ}
    (hgeo : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η)
    (hΘ : ∀ᵐ ω ∂stdP, ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η →
      IsRegular (lengthMeasure η) ∧ energy (lengthMeasure η) (lengthMeasure η) ≤ Θ ω ^ 2)
    (hFp : MemLp (fun ω => Real.log ((S.D γ ω).1 (0, 1))) (ENNReal.ofReal p) stdP) :
    eLpNorm (fun ω => Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)) *
        ENNReal.ofReal (S.ξ γ) * eLpNorm Θ (ENNReal.ofReal p) stdP := by
  have hΘ' : ∀ᵐ ω ∂stdP, ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η →
      IsRegular (lengthMeasure η) ∧
        ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η)) ≤ ‖Θ ω‖ₑ ^ 2 := by
    filter_upwards [hΘ] with ω hω η hη
    refine ⟨(hω η hη).1, ?_⟩
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    exact ENNReal.ofReal_le_ofReal (hω η hη).2
  have h := S.eLpNorm_logD_sub_b_le_ennreal hγ hγ2 hp hgeo hΘ' hFp
  rwa [eLpNorm_enorm] at h

end Setup

end GaussianLQG
