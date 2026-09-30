import QuantumZipper.Proofs.Thm18.G1Z2MeasRep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-MEAS, part 2: scaling lemmas (quantile points, scale parameter, canonical description)

Deterministic tools for the scale invariance of the rerooted canonical side data:

* `g1z2_lenLeft_map_div`, `g1z2_lenRight_map_div`: the quantile points of `m.map (· / b)` are those
  of `m` divided by `b`.
* `g1z2_scaleParam_rescale`: area-only version of `GoodTransforms.scaleParam_rescale`
  (only regularity and the area limit are used, not the global boundary limit).
* `g1z2_scaleParam_pos`: the scale parameter is positive when the area limit charges some ball
  around `0` with mass `≥ 1` and some ball with mass `< 1`.
* `g1z2_canonical_rescale_apply`: area-only version of `G1.canonical_rescale_apply_map`.

Own elementary arguments (copies of the cited proofs with weaker hypotheses).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology Pointwise

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

theorem g1z2_preimage_div_Icc_left {b : ℝ} (hb : 0 < b) (y : ℝ) :
    (fun u : ℝ => u / b) ⁻¹' Icc (-y) 0 = Icc (-(y * b)) 0 := by
  ext u
  simp only [mem_preimage, mem_Icc]
  rw [le_div_iff₀ hb, div_nonpos_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    rcases h2 with ⟨-, h⟩ | ⟨h, -⟩
    · linarith
    · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, Or.inr ⟨h2, hb.le⟩⟩

theorem g1z2_preimage_div_Icc_right {b : ℝ} (hb : 0 < b) (y : ℝ) :
    (fun u : ℝ => u / b) ⁻¹' Icc 0 y = Icc 0 (y * b) := by
  ext u
  simp only [mem_preimage, mem_Icc]
  rw [div_le_iff₀ hb, le_div_iff₀ hb, zero_mul]

/-- Quantile point (left) of a dilated measure. -/
theorem g1z2_lenLeft_map_div (m : Measure ℝ) {b : ℝ} (hb : 0 < b) (ℓ : ℝ) :
    lenLeft (m.map fun u => u / b) ℓ = lenLeft m ℓ / b := by
  have hmeas : Measurable fun u : ℝ => u / b := measurable_id.div_const b
  unfold lenLeft
  have e : {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ (m.map fun u => u / b) (Icc (-y) 0)} =
      b⁻¹ • {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc (-y) 0)} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hb.ne'), inv_inv, smul_eq_mul]
    simp only [mem_ofPred_eq]
    rw [Measure.map_apply hmeas measurableSet_Icc, g1z2_preimage_div_Icc_left hb, mul_comm b y]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hb, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hb.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul]
  ring

/-- Quantile point (right) of a dilated measure. -/
theorem g1z2_lenRight_map_div (m : Measure ℝ) {b : ℝ} (hb : 0 < b) (ℓ : ℝ) :
    lenRight (m.map fun u => u / b) ℓ = lenRight m ℓ / b := by
  have hmeas : Measurable fun u : ℝ => u / b := measurable_id.div_const b
  unfold lenRight
  have e : {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ (m.map fun u => u / b) (Icc 0 y)} =
      b⁻¹ • {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc 0 y)} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hb.ne'), inv_inv, smul_eq_mul]
    simp only [mem_ofPred_eq]
    rw [Measure.map_apply hmeas measurableSet_Icc, g1z2_preimage_div_Icc_right hb, mul_comm b y]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hb, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hb.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul, div_eq_inv_mul]

/-- The side quantile point of a dilated side measure. -/
theorem g1z2_sidePt_of_map {γ : ℝ} {left : Bool} {x x' : FieldSample} {b : ℝ} (hb : 0 < b)
    (h : g1SideNu γ left x' = (g1SideNu γ left x).map fun u => u / b) (ℓ : ℝ) :
    g1SidePt γ left x' ℓ = g1SidePt γ left x ℓ / b := by
  unfold g1SidePt
  rw [h]
  cases left
  · simp only [Bool.false_eq_true, ite_false]; exact g1z2_lenRight_map_div _ hb ℓ
  · simp only [ite_true]; exact g1z2_lenLeft_map_div _ hb ℓ

/-- **Scale parameter of a rescaled field**, area-only hypotheses. -/
theorem g1z2_scaleParam_rescale {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y)
    (hγ : 0 < γ) {μ : Measure ℂ} (hμ : HasAreaLimit γ y μ) {b : ℝ} (hb : 0 < b) :
    scaleParam γ (rescale y (Qc γ) b) = scaleParam γ y / b := by
  have h1 : qAreaMeasure γ (rescale y (Qc γ) b) = μ.map fun z : ℂ => z / (b : ℂ) :=
    GoodSample.qAreaMeasure_eq_of_hasAreaLimit (hy.rescale' (Qc γ) hb)
      (GoodTransforms.hasAreaLimit_rescale hy hγ hμ hb)
  have h2 : qAreaMeasure γ y = μ := GoodSample.qAreaMeasure_eq_of_hasAreaLimit hy hμ
  unfold scaleParam
  rw [h1, h2]
  have hmeas : Measurable (fun z : ℂ => z / (b : ℂ)) := measurable_id.div_const _
  have e : {a : ℝ | 0 < a ∧ 1 ≤ (μ.map fun z : ℂ => z / (b : ℂ)) (Metric.ball (0 : ℂ) a ∩ H)} =
      b⁻¹ • {a : ℝ | 0 < a ∧ 1 ≤ μ (Metric.ball (0 : ℂ) a ∩ H)} := by
    ext a
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hb.ne'), inv_inv, smul_eq_mul]
    simp only [mem_ofPred_eq]
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      GoodTransforms.preimage_div_ball_inter_H hb, mul_comm b a]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hb, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hb.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul, div_eq_inv_mul]

/-- **Positivity of the scale parameter.** -/
theorem g1z2_scaleParam_pos {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ y μ)
    (hsmall : ∃ a₀ : ℝ, 0 < a₀ ∧ μ (Metric.ball (0 : ℂ) a₀ ∩ H) < 1)
    (hbig : ∃ a₁ : ℝ, 0 < a₁ ∧ 1 ≤ μ (Metric.ball (0 : ℂ) a₁ ∩ H)) :
    0 < scaleParam γ y := by
  obtain ⟨a₀, ha₀, h₀⟩ := hsmall
  obtain ⟨a₁, ha₁, h₁⟩ := hbig
  unfold scaleParam
  rw [GoodSample.qAreaMeasure_eq_of_hasAreaLimit hy hμ]
  refine lt_of_lt_of_le ha₀ (le_csInf ⟨a₁, ha₁, h₁⟩ fun a ha => ?_)
  by_contra hlt
  push_neg at hlt
  have hmono : μ (Metric.ball (0 : ℂ) a ∩ H) ≤ μ (Metric.ball (0 : ℂ) a₀ ∩ H) :=
    measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hlt.le))
  exact absurd (ha.2.trans hmono) (not_le.2 h₀)

/-- **Canonical description of a rescaled field**, one evaluation, area-only hypotheses (cf.
`G1.canonical_rescale_apply_map`). -/
theorem g1z2_canonical_rescale_apply {γ : ℝ} (hγ : 0 < γ) {y : FieldSample}
    (hy : IsRegularSample y) {μ : Measure ℂ} (hμ : HasAreaLimit γ y μ)
    {b : ℝ} (hb : 0 < b) (hs : 0 < scaleParam γ y) (ν : Measure ℂ)
    (hsc : G1.ScaleConsistentAt y (Qc γ) b (ν.map fun z => ((scaleParam γ y / b : ℝ) : ℂ) * z)) :
    canonical γ (rescale y (Qc γ) b) ν = canonical γ y ν := by
  have hsb : 0 < scaleParam γ y / b := div_pos hs hb
  unfold canonical
  rw [g1z2_scaleParam_rescale hy hγ hμ hb]
  unfold G1.ScaleConsistentAt at hsc
  set y' := rescale y (Qc γ) b with hy'
  unfold rescale coordChange
  rw [G1.integral_log_deriv_mul' hsb, G1.integral_log_deriv_mul' hs]
  rw [hsc, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
  have e : ((fun z : ℂ => (b : ℂ) * z) ∘ fun z : ℂ => ((scaleParam γ y / b : ℝ) : ℂ) * z) =
      fun z : ℂ => (scaleParam γ y : ℂ) * z := by
    funext z
    simp only [Function.comp]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hb.ne']
  have hm : (ν.map fun z => ((scaleParam γ y / b : ℝ) : ℂ) * z).real univ = ν.real univ := by
    simp only [measureReal_def]
    rw [Measure.map_apply (measurable_const_mul _) MeasurableSet.univ, preimage_univ]
  rw [e, hm, Real.log_div hs.ne' hb.ne']
  ring

end Thm18Asm
end QuantumZipper
