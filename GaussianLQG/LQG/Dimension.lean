import LQGMetric.Assembly.MainFinal
import LQGMetric.Papers.DG.S3Wire3
import LQGMetric.Papers.DG.S3L37Q1
import LQGMetric.Papers.DG.S3P16D3
import LQGMetric.Papers.DG.BallMass
import LQGMetric.Papers.DG.XiQBound
import LQGMetric.Papers.DG.Adapter
import LQGMetric.Papers.DZZ.S5L53W1

/-!
# Input (S1) is a theorem: `d_γ = 2 + O(γ)`

The blueprint's (S1) (source (1.3), from [DG20, Thm 1.2]) follows from results already certified in
this repository:
* the small-ξ asymptotics `λ(ξ)/ξ^{4/3} → a*/log 16` of the LFPP exponent (`LQGDimension`), applied to
  the LFPP exponent supplied by Ding–Gwynne Theorem 1.5 (assembled in `LQGMetric`);
* the identity `(1 - λ_DG(γ)) d_γ = 2 + γ²/2` (`ξ Q = 1 - λ`) and `d_γ ≥ 1` (`DG.chiLeTwo`).
Hence `|λ_DG(γ)| ≤ K γ` and `|d_γ - 2| ≤ (5K + 1) γ` for small γ.

The proof was found and compiled by the independent statement audit S1
(`planning/audits/S1-statement-audit-main-draft.md`, Appendix A) and is reproduced verbatim.
-/

set_option autoImplicit false

namespace GaussianLQG
open MeasureTheory Filter Topology Set
open LQGMetric

theorem dgThm1_5_holds : DG.DGThm1_5 :=
  DG.wire_dgThm1_5_of DG.L37Q.dgLem3_7 (DG.dgProp3_16_of_lem37 DG.L37Q.dgLem3_7)
    (DG.dzzInputsDGForm_of (DZZ.dzzInputsDG_of_exp (DZZ.dzzLem53ExpAll_of_hbadB l53HbadBAll_proved)))

theorem dimensionInput_holds :
    ∃ γ₀ C₀ : ℝ, 0 < γ₀ ∧ ∀ γ ∈ Ioc (0 : ℝ) γ₀, |dGamma γ - 2| ≤ C₀ * γ := by
  obtain ⟨Ω, _, P, hc, hG⟩ := DG.exists_circleAvgProcess
  have hLA := LQGDimension.lambdaAsymptotics_of LQGDimension.theorem11.1
    LQGDimension.prop12Upper LQGDimension.prop12Lower
  obtain ⟨ξ₁, hξ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hLA Ω P hc hG 1 one_pos)
  have hξ₁' : (0 : ℝ) < ξ₁ := hξ₁
  set a := LQGDimension.aStar / Real.log 16 with ha
  set K := |a| + 1 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨min (min 1 (ξ₁ / 2)) (1 / (2 * K)), 5 * K + 1, by positivity, ?_⟩
  rintro γ ⟨hγ0, hγle⟩
  have hγ1 : γ ≤ 1 := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγξ : γ ≤ ξ₁ / 2 := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγK : γ ≤ 1 / (2 * K) := hγle.trans (min_le_right _ _)
  have hγ2 : γ < 2 := by linarith
  have hd1 : 1 ≤ dGamma γ := DG.one_le_dGamma DG.chiLeTwo hγ0 hγ2
  have hξ0 : 0 < xiGamma γ := DG.xiGamma_pos hγ0
  have hξγ : xiGamma γ ≤ γ := div_le_self hγ0.le hd1
  have hexp := DG.isLFPPExponent_of_dgThm1_5 dgThm1_5_holds hγ0 hγ2 hG
  have hb : |DG.dgLambda γ / xiGamma γ ^ (4 / 3 : ℝ) - a| ≤ 1 :=
    hsub ⟨hξ0, by linarith⟩ (DG.dgLambda γ) hexp
  have hp : 0 < xiGamma γ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hξ0 _
  have hp1 : xiGamma γ ^ (4 / 3 : ℝ) ≤ xiGamma γ := by
    have h1 : xiGamma γ ≤ 1 := by linarith
    calc xiGamma γ ^ (4 / 3 : ℝ) ≤ xiGamma γ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hξ0 h1 (by norm_num)
      _ = xiGamma γ := Real.rpow_one _
  have hlam : |DG.dgLambda γ| ≤ K * γ := by
    have h1 : |DG.dgLambda γ / xiGamma γ ^ (4 / 3 : ℝ)| ≤ K := by
      have := abs_add_le (DG.dgLambda γ / xiGamma γ ^ (4 / 3 : ℝ) - a) a
      rw [sub_add_cancel] at this
      linarith
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp] at h1
    calc |DG.dgLambda γ| ≤ K * xiGamma γ ^ (4 / 3 : ℝ) := h1
      _ ≤ K * γ := by gcongr; linarith
  have hd0 : dGamma γ ≠ 0 := by linarith
  have hid : (1 - DG.dgLambda γ) * dGamma γ = 2 + γ ^ 2 / 2 := by
    unfold DG.dgLambda; field_simp; ring
  have hlamhalf : |DG.dgLambda γ| ≤ 1 / 2 := by
    calc |DG.dgLambda γ| ≤ K * γ := hlam
      _ ≤ K * (1 / (2 * K)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hl := abs_le.1 hlamhalf
  have hdle : dGamma γ ≤ 5 := by
    have hm : dGamma γ * (1 / 2) ≤ dGamma γ * (1 - DG.dgLambda γ) :=
      mul_le_mul_of_nonneg_left (by linarith [hl.2]) (by linarith)
    nlinarith [hid, sq_nonneg γ]
  have hdiff : dGamma γ - 2 = dGamma γ * DG.dgLambda γ + γ ^ 2 / 2 := by linear_combination hid
  rw [hdiff]
  have e1 : |dGamma γ * DG.dgLambda γ| ≤ 5 * (K * γ) := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < dGamma γ)]
    exact mul_le_mul hdle hlam (abs_nonneg _) (by norm_num)
  have e2 : |γ ^ 2 / 2| ≤ γ := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  calc |dGamma γ * DG.dgLambda γ + γ ^ 2 / 2|
      ≤ |dGamma γ * DG.dgLambda γ| + |γ ^ 2 / 2| := abs_add_le _ _
    _ ≤ 5 * (K * γ) + γ := add_le_add e1 e2
    _ = (5 * K + 1) * γ := by ring

end GaussianLQG
