import GaussianLQG.LQG.Localization.Defs
import GaussianLQG.Energy.Bound

/-!
# Localization and ball masses along geodesics (blueprint Lemma `lem:T-B`, pathwise part)

For every `ω` with `T(ω) < ∞`, every `z, w ∈ K` with `|z - w| ≥ δ`, and every constant-speed
`D^γ(ω)`-geodesic `η` from `z` to `w` (blueprint (`eq:T-B`)):

* `η([0,1]) ⊆ B_T(0)` (`Setup.range_subset_ball_locT`): if `T = 2R_*` with `L_{R_*} > U`, a geodesic
  leaving `B_{2R_*}(0)` would give `D(z, w) ≥ L_{R_*} > U ≥ D(z, w)`
  (Lemma `lem:geodesic-props`(c));
* `ν_η(B_r(u)) ≤ B r^{1/2}` (`Setup.lengthMeasure_ball_le_locB`): by Lemma `lem:geodesic-props`(b),
  `ν_η(B_r(u)) ≤ A_γ(B̄_T(0)) (2r)^{1/2} / D(z, w)` and `D(z, w) ≥ I_γ(K, δ)`;
* if also `B < ∞`: `ν_η` is regular and `ℰ(ν_η, ν_η) ≤ Θ²`
  (`Setup.isRegular_and_energy_le_locTheta`),
  by Lemma `lem:energy-bound` (`isRegular_and_energy_le`).

No assumption on `ω` beyond `T(ω) < ∞` (and `B(ω) < ∞` for the energy bound) is needed: the geodesic
is arbitrary, and the bounds hold for all geodesics simultaneously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-- `D(z, w) ≤ A(K) |z - w|^{1/2}` in `ℝ≥0∞`, for `z, w ∈ K` (blueprint (1.10)). -/
theorem ofReal_le_holderConst_mul (D : ContMetric) {K : Set ℂ} {z w : ℂ} (hz : z ∈ K)
    (hw : w ∈ K) :
    ENNReal.ofReal (D.1 (z, w)) ≤ holderConst D.1 K * ENNReal.ofReal (‖z - w‖ ^ (1 / 2 : ℝ)) := by
  rcases eq_or_ne z w with rfl | hzw
  · rw [D.2.self_eq_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hc : 0 < ‖z - w‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hzw)) _
  have h1 : ENNReal.ofReal (D.1 (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) ≤ holderConst D.1 K := by
    unfold holderConst
    exact le_iSup₂_of_le z hz (le_iSup₂_of_le w hw (le_iSup_of_le hzw le_rfl))
  calc ENNReal.ofReal (D.1 (z, w))
      = ENNReal.ofReal (D.1 (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (‖z - w‖ ^ (1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (div_nonneg (ContMetric.nonneg D z w) hc.le),
          div_mul_cancel₀ _ hc.ne']
    _ ≤ holderConst D.1 K * ENNReal.ofReal (‖z - w‖ ^ (1 / 2 : ℝ)) := by gcongr

namespace Setup

variable {S : Setup} {γ : ℝ} {K : Set ℂ} {δ : ℝ} {ω : Coord}

/-- `D(z, w) ≤ U` for `z, w ∈ K`. -/
theorem ofReal_le_locU {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) :
    ENNReal.ofReal ((S.D γ ω).1 (z, w)) ≤ S.locU γ K ω :=
  le_iSup₂_of_le z hz (le_iSup₂_of_le w hw le_rfl)

/-- `D(z, w) ≥ I(K, δ)` for `z, w ∈ K` with `|z - w| ≥ δ`. -/
theorem sepInf_le_ofReal_of_mem {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) (hzw : δ ≤ ‖z - w‖) :
    sepInf (S.D γ ω).1 K δ ≤ ENNReal.ofReal ((S.D γ ω).1 (z, w)) :=
  iInf₂_le_of_le z hz (iInf₂_le_of_le w hw (iInf_le_of_le hzw le_rfl))

/-- **Blueprint Lemma `lem:T-B`, containment.** If `T < ∞`, every constant-speed geodesic between
two points of `K` stays in `B_T(0)`. -/
theorem range_subset_ball_locT (hK : Bornology.IsBounded K) (hT : S.locT γ K ω ≠ ⊤) {z w : ℂ}
    (hz : z ∈ K) (hw : w ∈ K) {η : C(unitInterval, ℂ)} (hη : IsGeod01 (S.D γ ω) z w η) :
    range η ⊆ Metric.ball 0 (S.locT γ K ω).toReal := by
  obtain ⟨k, hk, hTk⟩ := exists_eq_locT hT
  have hR0 : 0 ≤ 2 ^ k * locR0 K := mul_nonneg (pow_nonneg zero_le_two k) (locR0_pos K).le
  have hTR : (S.locT γ K ω).toReal = 2 * (2 ^ k * locR0 K) := by
    rw [hTk, ENNReal.toReal_ofReal (mul_nonneg zero_le_two hR0)]
  rw [hTR]
  by_contra hout
  have hzR : ‖z‖ ≤ 2 ^ k * locR0 K := by
    have h1 := (locR0_spec hK).2 hz
    rw [mem_ball_zero_iff] at h1
    have h2 : locR0 K ≤ 2 ^ k * locR0 K :=
      le_mul_of_one_le_left (locR0_pos K).le (one_le_pow₀ one_le_two)
    linarith
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_crossing_of_isGeod01 hη hzR hout
  have h1 : annulusCross (S.D γ ω).1 (2 ^ k * locR0 K) ≤ ENNReal.ofReal ((S.D γ ω).1 (x, y)) := by
    unfold annulusCross
    exact (iInf₂_le x (mem_sphere_zero_iff_norm.2 hx)).trans
      (iInf₂_le y (mem_sphere_zero_iff_norm.2 hy))
  have h2 := h1.trans ((ENNReal.ofReal_le_ofReal hxy).trans (ofReal_le_locU hz hw))
  exact absurd hk (not_lt.2 h2)

/-- **Blueprint Lemma `lem:T-B`, ball masses.** If `T < ∞`, then for `z, w ∈ K` with `|z - w| ≥ δ`
and every constant-speed geodesic `η` from `z` to `w`, `ν_η(B_r(u)) ≤ B r^{1/2}` for all `u` and
`r > 0`. -/
theorem lengthMeasure_ball_le_locB (hK : Bornology.IsBounded K) (hδ : 0 < δ)
    (hT : S.locT γ K ω ≠ ⊤) {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) (hzw : δ ≤ ‖z - w‖)
    {η : C(unitInterval, ℂ)} (hη : IsGeod01 (S.D γ ω) z w η) (u : ℂ) {r : ℝ} (hr : 0 < r) :
    lengthMeasure η (Metric.ball u r) ≤ S.locB γ K δ ω * ENNReal.ofReal (r ^ (1 / 2 : ℝ)) := by
  set D := S.D γ ω with hD
  set A := holderConst D.1 (Metric.closedEBall (0 : ℂ) (S.locT γ K ω)) with hA
  set I := sepInf D.1 K δ with hI
  have hzw' : z ≠ w := by
    intro h
    rw [h, sub_self, norm_zero] at hzw
    linarith
  have hL : 0 < D.1 (z, w) :=
    lt_of_le_of_ne (ContMetric.nonneg D z w) fun h => hzw' (D.2.eq_of_eq_zero z w h.symm)
  have hIle : I ≤ ENNReal.ofReal (D.1 (z, w)) := sepInf_le_ofReal_of_mem hz hw hzw
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIle
  have hrpos : 0 < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hBge : ENNReal.ofReal (Real.sqrt 2) * A / I ≤ S.locB γ K δ ω := le_max_right _ _
  have hsqrt2 : ENNReal.ofReal (Real.sqrt 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  by_cases hAtop : A = ⊤
  · have hB : S.locB γ K δ ω = ⊤ := by
      refine top_le_iff.1 (le_trans ?_ hBge)
      rw [hAtop, ENNReal.mul_top hsqrt2, ENNReal.top_div_of_ne_top hItop]
    rw [hB, ENNReal.top_mul (by rwa [ne_eq, ENNReal.ofReal_eq_zero, not_le])]
    exact le_top
  · have hrange : range η ⊆ Metric.closedEBall (0 : ℂ) (S.locT γ K ω) := by
      rw [eclosedBall_locT hT]
      exact (range_subset_ball_locT hK hT hz hw hη).trans Metric.ball_subset_closedBall
    have hW5 := lengthMeasure_ball_le_of_isGeod01 hη hL hrange hAtop u hr
    have h2r : (2 * r) ^ (1 / 2 : ℝ) = Real.sqrt 2 * r ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow zero_le_two hr.le, Real.sqrt_eq_rpow]
    calc lengthMeasure η (Metric.ball u r)
        = ENNReal.ofReal ((lengthMeasure η (Metric.ball u r)).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (A.toReal * (2 * r) ^ (1 / 2 : ℝ) / D.1 (z, w)) :=
          ENNReal.ofReal_le_ofReal hW5
      _ = ENNReal.ofReal (Real.sqrt 2) * A * ENNReal.ofReal (r ^ (1 / 2 : ℝ)) /
            ENNReal.ofReal (D.1 (z, w)) := by
          rw [ENNReal.ofReal_div_of_pos hL, h2r, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hAtop, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
          ring_nf
      _ ≤ ENNReal.ofReal (Real.sqrt 2) * A * ENNReal.ofReal (r ^ (1 / 2 : ℝ)) / I :=
          ENNReal.div_le_div_left hIle _
      _ = ENNReal.ofReal (Real.sqrt 2) * A / I * ENNReal.ofReal (r ^ (1 / 2 : ℝ)) :=
          ENNReal.mul_div_right_comm
      _ ≤ S.locB γ K δ ω * ENNReal.ofReal (r ^ (1 / 2 : ℝ)) := by gcongr

/-- **Blueprint Lemma `lem:T-B`, energy.** If `T < ∞` and `B < ∞`, then for `z, w ∈ K` with
`|z - w| ≥ δ` and every constant-speed geodesic `η` from `z` to `w`, the length measure `ν_η` is
regular and `ℰ(ν_η, ν_η) ≤ Θ²` (Lemma `lem:energy-bound`). -/
theorem isRegular_and_energy_le_locTheta (hK : Bornology.IsBounded K) (hδ : 0 < δ)
    (hT : S.locT γ K ω ≠ ⊤) (hB : S.locB γ K δ ω ≠ ⊤) {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K)
    (hzw : δ ≤ ‖z - w‖) {η : C(unitInterval, ℂ)} (hη : IsGeod01 (S.D γ ω) z w η) :
    IsRegular (lengthMeasure η) ∧
      energy (lengthMeasure η) (lengthMeasure η) ≤ (S.locTheta γ K δ ω).toReal ^ 2 := by
  rw [toReal_locTheta_sq hT hB]
  have hT1 : 1 ≤ (S.locT γ K ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hT one_le_locT
  have hB1 : 1 ≤ (S.locB γ K δ ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hB one_le_locB
  refine isRegular_and_energy_le hT1 ?_ hB1 fun u r hr _ => ?_
  · exact measure_mono_null (compl_subset_compl.2 ((range_subset_ball_locT hK hT hz hw hη).trans
      Metric.ball_subset_closedBall)) (lengthMeasure_compl_range η)
  · refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hB]
    exact lengthMeasure_ball_le_locB hK hδ hT hz hw hzw hη u hr

end Setup

end GaussianLQG
