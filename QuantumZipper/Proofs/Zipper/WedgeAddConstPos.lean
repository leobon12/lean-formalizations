import QuantumZipper.Proofs.Zipper.WedgeAddConstRef

/-!
# WEDGE-ADDCONST (2): positivity of the canonical scale of `W + k`

For the reference wedge `W = canonical γ Z`, `Z = wedgeField (lateralPart X) A Q`, and any constant
`k`, almost surely `0 < scaleParam γ (W + k)`: the area measure of `W + k` is
`e^{γk} (·/s)_* μ_Z` (Sheffield, arXiv:1012.4797, §1.6, (1.8) and the coordinate change rule;
`GoodTransforms.qAreaMeasure_rescale`, `GoodSample.qAreaMeasure_addConst`), so its area profile is
`b ↦ e^{γk} μ_Z(B(0, s b) ∩ ℍ)` and inherits the profile properties of `Z`
(`Wire2.ae_hasAreaProfile_wedgeField`, R23 (a)); then `CanonicalGood.scaleParam_spec`.

This splits `F1.WedgeRefAddConstStmt` into this positivity part (proved) and its law part
`WedgeRefAddConstLawStmt` (`wedgeRefAddConstStmt_of_law`, `wedgeAddConstLawStmt_of_refLaw`).

Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open AreaProfile

theorem profile_smul_map_div (C : ℝ≥0∞) (μ : Measure ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    profile (C • μ.map fun z : ℂ => z / (a : ℂ)) b = C * profile μ (b * a) := by
  simp only [profile, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (show Measurable fun z : ℂ => z / (a : ℂ) from measurable_id.div_const _)
      (measurableSet_ball_inter_H b),
    GoodTransforms.preimage_div_ball_inter_H ha]

theorem hasAreaProfile_smul_map_div {γ : ℝ} {x y : FieldSample} {C : ℝ≥0∞} (hC0 : C ≠ 0)
    (hCt : C ≠ ⊤) {a : ℝ} (ha : 0 < a) (hx : HasAreaProfile γ x)
    (hy : qAreaMeasure γ y = C • (qAreaMeasure γ x).map fun z : ℂ => z / (a : ℂ)) :
    HasAreaProfile γ y := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  have e : profile (qAreaMeasure γ y) = fun b => C * profile (qAreaMeasure γ x) (b * a) := by
    funext b; rw [hy, profile_smul_map_div C _ ha b]
  rw [HasAreaProfile, e]
  have hma : Continuous fun b : ℝ => b * a := continuous_id.mul continuous_const
  refine ⟨fun b => ENNReal.mul_ne_top hCt (h1 _),
    (ENNReal.continuous_const_mul hCt).comp (h2.comp hma), ?_, ?_, ?_⟩
  · intro u hu v hv huv
    have hu' : u * a ∈ Ici (0 : ℝ) := mul_nonneg (mem_Ici.1 hu) ha.le
    have hv' : v * a ∈ Ici (0 : ℝ) := mul_nonneg (mem_Ici.1 hv) ha.le
    show C * _ < C * _
    rw [mul_comm C, mul_comm C]
    exact ENNReal.mul_lt_mul_left hC0 hCt (h3 hu' hv' (mul_lt_mul_of_pos_right huv ha))
  · have ht : Tendsto (fun b : ℝ => b * a) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using (hma.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with b hb
        exact mul_pos (mem_Ioi.1 hb) ha
    simpa using ENNReal.Tendsto.const_mul (h4.comp ht) (Or.inr hCt)
  · have ht : Tendsto (fun b : ℝ => b * a) atTop atTop := tendsto_id.atTop_mul_const ha
    simpa [ENNReal.mul_top hC0] using ENNReal.Tendsto.const_mul (h5.comp ht) (Or.inr hCt)

/-- The area profile passes to `rescale x Q a + c`. -/
theorem hasAreaProfile_addConst_rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample}
    (hg : IsLQGGood γ x) (hx : HasAreaProfile γ x) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    HasAreaProfile γ (addConst (rescale x (Qc γ) a) c) :=
  hasAreaProfile_smul_map_div (C := ENNReal.ofReal (Real.exp (γ * c)))
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top ha hx
    (by rw [GoodSample.qAreaMeasure_addConst (hg.rescale hγ ha) c,
      GoodTransforms.qAreaMeasure_rescale hg hγ ha])

/-- **Positivity for the reference wedge.** -/
theorem ae_pos_scaleParam_addConst_wedgeRef {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < Qc γ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') (k : ℝ) :
    ∀ᵐ ω ∂P', 0 < scaleParam γ (addConst (WedgeMeas.wedgeRef γ X A ω) k) := by
  filter_upwards [LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A inferInstance hX hA hI,
    Wire2.ae_hasAreaProfile_wedgeField hγ hγ2 hα hX hA hI] with ω hg hp
  have hs := (CanonicalGood.scaleParam_spec hp).1
  exact (CanonicalGood.scaleParam_spec (hasAreaProfile_addConst_rescale hγ hg hp hs k)).1

/-- **B4(c) for the reference wedge, law part** (open node). -/
def WedgeRefAddConstLawStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' → ∀ k : ℝ,
      fieldLawFull H (fun ω => canonical γ (addConst (WedgeMeas.wedgeRef γ X A ω) k)) P' =
        fieldLawFull H (WedgeMeas.wedgeRef γ X A) P'

theorem wedgeRefAddConstStmt_of_law {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hlaw : WedgeRefAddConstLawStmt γ α) : WedgeRefAddConstStmt γ α :=
  fun P' _ X A hX hA hI k =>
    ⟨ae_pos_scaleParam_addConst_wedgeRef hγ hγ2 hα hX hA hI k, hlaw P' X A hX hA hI k⟩

/-- **Field-level B4(c) from its law part for the reference wedge.** -/
theorem wedgeAddConstLawStmt_of_refLaw
    (hlaw : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeRefAddConstLawStmt γ α) :
    WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_ref fun γ α hγ hγ2 hα =>
    wedgeRefAddConstStmt_of_law hγ hγ2 hα (hlaw γ α hγ hγ2 hα)

end F1
end QuantumZipper
