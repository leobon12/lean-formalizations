import HigherDimLFPP.Var.Theorem11
import LQGDimension.Assembly.Theorem11
import GaussianLQG.LQG.Dimension

/-!
# The LQG dimension for small `γ`: `(d_γ - 2)/γ^{4/3} → 2^{-1/3} κ₂`

Ruling H9 (ii): `LQGDimension.theorem11_dimension` (the 2D paper's Theorem 1.1, (1.6)) with its two
hypotheses discharged for the LQG dimension `LQGMetric.dGamma`:

* `d_γ → 2` as `γ ↓ 0`, from `GaussianLQG.dimensionInput_holds` (`|d_γ - 2| ≤ C γ` for small `γ`);
* the exponent relation `λ(γ/d_γ) = 1 - (2 + γ²/2)/d_γ` for `γ ∈ (0, 2)`, from
  `LQGMetric.DG.isLFPPExponent_of_dgThm1_5 GaussianLQG.dgThm1_5_holds` (Ding–Gwynne Theorem 1.5,
  proved in `GaussianLQG`), since `dgLambda γ = 1 - 2/d_γ - γ²/(2 d_γ) = 1 - (2 + γ²/2)/d_γ`;

applied to a circle-average process of the whole-plane GFF (`LQGMetric.DG.exists_circleAvgProcess`).
Finally `a*/log 16 = κ₂` (`kappa_two_eq_impl`).

This file has no 2D counterpart to port: it is the d = 2 corollary, assembled from
`LQGDimension/Assembly/Theorem11.lean` and `gaussian_lqg_distance/GaussianLQG/LQG/Dimension.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

namespace TwoD

/-- `d_γ → 2` as `γ ↓ 0` (from `|d_γ - 2| ≤ C₀ γ` for `γ ∈ (0, γ₀]`). -/
theorem dGamma_tendsto : Tendsto LQGMetric.dGamma (𝓝[>] 0) (𝓝 2) := by
  obtain ⟨γ₀, C₀, hγ₀, hbd⟩ := GaussianLQG.dimensionInput_holds
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min γ₀ (ε / (|C₀| + 1)), by positivity, fun γ hγ hdist => ?_⟩
  have hγ0 : 0 < γ := hγ
  rw [Real.dist_eq, sub_zero, abs_of_pos hγ0] at hdist
  have h1 : γ ≤ γ₀ := (lt_of_lt_of_le hdist (min_le_left _ _)).le
  have h2 : γ < ε / (|C₀| + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
  rw [Real.dist_eq]
  have hb := hbd γ ⟨hγ0, h1⟩
  have hC : C₀ * γ ≤ |C₀| * γ := mul_le_mul_of_nonneg_right (le_abs_self C₀) hγ0.le
  have h3 : (|C₀| + 1) * γ < ε := by
    rw [lt_div_iff₀ (by positivity)] at h2; linarith
  nlinarith [abs_nonneg C₀]

/-- The exponent relation (1.1) of the 2D paper for the LQG dimension: for `γ ∈ (0, 2)` and every
circle-average process of the whole-plane GFF, `1 - (2 + γ²/2)/d_γ` is the LFPP exponent at
`ξ = γ/d_γ`. -/
theorem isLFPPExponent_dGamma {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hc : ℝ → ℂ → Ω → ℝ} (hG : LQGDimension.IsGFFCircleAverage hc P) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) :
    LQGDimension.IsLFPPExponent hc P (γ / LQGMetric.dGamma γ)
      (1 - (2 + γ ^ 2 / 2) / LQGMetric.dGamma γ) := by
  have hexp := LQGMetric.DG.isLFPPExponent_of_dgThm1_5 GaussianLQG.dgThm1_5_holds hγ0 hγ2 hG
  have hd : LQGMetric.dGamma γ ≠ 0 := (LQGMetric.DG.dGamma_pos γ).ne'
  have hlam : LQGMetric.DG.dgLambda γ = 1 - (2 + γ ^ 2 / 2) / LQGMetric.dGamma γ := by
    unfold LQGMetric.DG.dgLambda
    field_simp
    ring
  rw [hlam] at hexp
  exact hexp

/-- `(d_γ - 2)/γ^{4/3} → 2^{-1/3} a*/log 16`, with no hypotheses. -/
theorem lqg_dimension_asymptotics_aStar :
    Tendsto (fun γ : ℝ => (LQGMetric.dGamma γ - 2) / γ ^ (4 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (2 ^ (-1 / 3 : ℝ) * LQGDimension.aStar / Real.log 16)) := by
  obtain ⟨Ω, _, P, hc, hG⟩ := LQGMetric.DG.exists_circleAvgProcess
  exact LQGDimension.theorem11_dimension Ω P hc hG LQGMetric.dGamma dGamma_tendsto
    ⟨2, two_pos, fun γ hγ => isLFPPExponent_dGamma hG hγ.1 hγ.2⟩

end TwoD

/-- **d = 2, LQG dimension** (ruling H9 (ii)): `(d_γ - 2)/γ^{4/3} → 2^{-1/3} κ₂` as `γ ↓ 0`. -/
theorem lqg_dimension_asymptotics_impl :
    Tendsto (fun γ : ℝ => (LQGMetric.dGamma γ - 2) / γ ^ (4 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (2 ^ (-1 / 3 : ℝ) * kappa 2)) := by
  rw [kappa_two_eq_impl, ← mul_div_assoc]
  exact TwoD.lqg_dimension_asymptotics_aStar

end HigherDimLFPP
