import HigherDimLQGMetric.ConvField.RadialDet
import LQGMetric.Papers.DFGPS.L2_1RadialMeas

/-! An `L¹` rate for convergence of mollified sphere averages. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private theorem l2b_enorm_le_of_sq {D : Ω → ℝ} {B : ℝ}
    (hB : 0 < B) (hi : Integrable (fun ω => D ω ^ 2) P)
    (hb : ∫ ω, D ω ^ 2 ∂P ≤ B ^ 2) :
    ∫⁻ ω, ‖D ω‖ₑ ∂P ≤ ENNReal.ofReal B := by
  have haux : Integrable (fun ω => (D ω ^ 2 / B + B) / 2) P :=
    ((hi.div_const B).add (integrable_const B)).div_const 2
  calc
    ∫⁻ ω, ‖D ω‖ₑ ∂P ≤
        ∫⁻ ω, ENNReal.ofReal ((D ω ^ 2 / B + B) / 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (LQGMetric.DFGPS.abs_le_sq_div_add hB)
    _ = ENNReal.ofReal (∫ ω, (D ω ^ 2 / B + B) / 2 ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal haux
        (Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ ENNReal.ofReal B := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [integral_div, integral_add (hi.div_const B) (integrable_const B),
        integral_div, integral_const, probReal_univ, one_smul]
      have : (∫ ω, D ω ^ 2 ∂P) / B ≤ B := by
        rw [div_le_iff₀ hB]
        nlinarith
      linarith

theorem l2b_exists_lintegral_enorm_sphereAvgSeq_sub_le {d : ℕ} (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ {r : ℝ}, 0 < r →
        ∀ (z : Rd d) (n : ℕ),
          (∫⁻ ω, ‖sphereAvgSeq (h ω) r z n - sphereAvg (h ω) r z‖ₑ ∂P) ≤
            ENNReal.ofReal (A / Real.sqrt r) *
              ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ)) ^ n *
                (1 - ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ)))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphMol_sub_le hd
  let A : ℝ := C + 1
  have hA : 0 < A := by dsimp [A]; linarith
  refine ⟨A, hA.le, ?_⟩
  intro Ω _ P _ h hh r hr z n
  let s : ℝ := Real.sqrt (1 / 2 : ℝ)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs1 : s < 1 := by
    dsimp [s]
    rw [Real.sqrt_lt' one_pos]
    norm_num
  let X : ℕ → Ω → ℝ := fun j ω => sphereAvgSeq (h ω) r z j
  let D : ℕ → Ω → ℝ := fun j ω => X (j + 1) ω - X j ω
  have hsq : ∀ j : ℕ, Integrable (fun ω => D j ω ^ 2) P ∧
      ∫ ω, D j ω ^ 2 ∂P ≤ C / (2 * r) * (1 / 2 : ℝ) ^ j := by
    intro j
    simp_rw [D, X, sphereAvgSeq_eq_apply_sphMol]
    obtain ⟨hi, -, hb⟩ := hC hh (ε := ((2 : ℝ) ^ (j + 1))⁻¹)
      (ε' := ((2 : ℝ) ^ j)⁻¹) (by positivity) (by positivity) hr hr z z
    refine ⟨hi, hb.trans (le_of_eq ?_)⟩
    have e : |((2 : ℝ) ^ (j + 1))⁻¹ - ((2 : ℝ) ^ j)⁻¹| =
        (1 / 2 : ℝ) ^ j * (1 / 2) := by
      rw [← inv_pow, ← inv_pow, pow_succ, one_div,
        show (2 : ℝ)⁻¹ ^ j * 2⁻¹ - 2⁻¹ ^ j = -(2⁻¹ ^ j * 2⁻¹) by ring,
        abs_neg, abs_of_pos (by positivity)]
    rw [sub_self, norm_zero, sub_self, abs_zero, zero_add, zero_add, min_self, e]
    ring
  have hED : ∀ j : ℕ, ∫⁻ ω, ‖D j ω‖ₑ ∂P ≤ ENNReal.ofReal (A / Real.sqrt r * s ^ j) := by
    intro j
    let B : ℝ := A / Real.sqrt r * s ^ j
    have hB : 0 < B := by dsimp [B]; positivity
    have hs2 : s ^ 2 = (1 / 2 : ℝ) := by
      dsimp [s]
      rw [Real.sq_sqrt (by norm_num)]
    have hB2 : B ^ 2 = A ^ 2 / r * (1 / 2 : ℝ) ^ j := by
      dsimp [B]
      rw [mul_pow, div_pow, Real.sq_sqrt hr.le, ← pow_mul, mul_comm j 2, pow_mul, hs2]
    have hle : ∫ ω, D j ω ^ 2 ∂P ≤ B ^ 2 := by
      rw [hB2]
      refine (hsq j).2.trans ?_
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * r) hr]
      dsimp [A]
      nlinarith [sq_nonneg C]
    exact l2b_enorm_le_of_sq hB (hsq j).1 hle
  have hpt : ∀ᵐ ω ∂P,
      ‖X n ω - sphereAvg (h ω) r z‖ₑ ≤ ∑' j, ‖D (n + j) ω‖ₑ := by
    filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω ⟨a, ha⟩
    rw [sphereAvg_eq_of_tendsto ha]
    have hX : Tendsto (fun k => X k ω) atTop (𝓝 a) := ha
    have h2 : Tendsto (fun k => ‖X n ω - X (k + n) ω‖ₑ) atTop (𝓝 ‖X n ω - a‖ₑ) :=
      (continuous_enorm.tendsto _).comp
        (tendsto_const_nhds.sub (hX.comp (tendsto_add_atTop_nat n)))
    refine le_of_tendsto' h2 fun k => ?_
    have htel := Finset.sum_range_sub (fun i => X (n + i) ω) k
    simp only [add_zero] at htel
    calc
      ‖X n ω - X (k + n) ω‖ₑ = ‖∑ j ∈ Finset.range k, D (n + j) ω‖ₑ := by
        rw [← enorm_neg, neg_sub, add_comm k n, ← htel]
        congr 1
      _ ≤ ∑ j ∈ Finset.range k, ‖D (n + j) ω‖ₑ := enorm_sum_le _ _
      _ ≤ ∑' j, ‖D (n + j) ω‖ₑ := ENNReal.sum_le_tsum _
  have hDm : ∀ j, Measurable (D j) := by
    intro j
    exact ((measurable_sphereAvgSeq_left r z (j + 1)).comp hh.measurable).sub
      ((measurable_sphereAvgSeq_left r z j).comp hh.measurable)
  calc
    ∫⁻ ω, ‖X n ω - sphereAvg (h ω) r z‖ₑ ∂P ≤
        ∫⁻ ω, ∑' j, ‖D (n + j) ω‖ₑ ∂P := lintegral_mono_ae hpt
    _ = ∑' j, ∫⁻ ω, ‖D (n + j) ω‖ₑ ∂P :=
      lintegral_tsum fun j => (hDm (n + j)).enorm.aemeasurable
    _ ≤ ∑' j, ENNReal.ofReal (A / Real.sqrt r * s ^ (n + j)) :=
      ENNReal.tsum_le_tsum fun j => hED _
    _ = ENNReal.ofReal (A / Real.sqrt r) * ENNReal.ofReal s ^ n *
          (1 - ENNReal.ofReal s)⁻¹ := by
      have e : ∀ j, ENNReal.ofReal (A / Real.sqrt r * s ^ (n + j)) =
          ENNReal.ofReal (A / Real.sqrt r) * ENNReal.ofReal s ^ n *
            ENNReal.ofReal s ^ j := by
        intro j
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hs0.le, pow_add, mul_assoc]
      simp_rw [e]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

end HigherDimLQGMetric
