import HigherDimLQGMetric.Limits.RandomPrecompact
import HigherDimLQGMetric.Determ.LengthBorel
import HigherDimLQGMetric.Config.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section
open MeasureTheory Set Topology
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private def defaultD : ContMetric d := fieldLfppMetric 0 (0 : C(Rd d, ℝ))
private theorem defaultD_len : (defaultD (d := d)).IsLength :=
  fieldLfppMetric_isLength 0 (0 : C(Rd d, ℝ))

private def metricLift (X : C(Rd d × Rd d, ℝ)) : ContMetric d := by
  classical
  exact if h : IsContinuousMetric X then ⟨X,h⟩ else defaultD

private theorem metricLift_meas : Measurable (metricLift (d := d)) := by
  classical
  have hEmb : MeasurableEmbedding
      ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  apply (hEmb.measurable_comp_iff).mp
  have heq : ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) ∘ metricLift =
      (fun X => if h : IsContinuousMetric X then X else (defaultD (d := d)).1) := by
    funext X
    simp only [Function.comp_def, metricLift]
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (measurableSet_isContinuousMetric_select d)
    measurable_id measurable_const

private theorem metricLift_eq {X : C(Rd d × Rd d, ℝ)} (hX : IsContinuousMetric X) :
    (metricLift X).1 = X := by classical simp [metricLift, hX]


/-- The length-metric predicate is universally measurable on ambient continuous maps. -/
theorem l6c_uMeasurableSet_contLength :
    LQGMetric.UMeasurableSet {X : C(Rd d × Rd d, ℝ) | IsContLengthFn X} := by
  let T : Set C(Rd d × Rd d, ℝ) := {X | IsContinuousMetric X}
  let L : Set (ContMetric d) := {D | D.IsLength}
  have hL : LQGMetric.UMeasurableSet L := determ_uMeasurableSet_isLength d
  have hT : LQGMetric.UMeasurableSet T :=
    LQGMetric.UMeasurableSet.of_measurableSet (measurableSet_isContinuousMetric_select d)
  have heq : {X : C(Rd d × Rd d, ℝ) | IsContLengthFn X} =
      T ∩ metricLift (d := d) ⁻¹' L := by
    ext X
    constructor
    · rintro ⟨hM, hLen⟩
      refine ⟨hM, ?_⟩
      have he : metricLift X = (⟨X, hM⟩ : ContMetric d) := Subtype.ext (metricLift_eq hM)
      simpa [L, he] using hLen
    · rintro ⟨hM, hLen⟩
      refine ⟨hM, ?_⟩
      have he : metricLift X = (⟨X, hM⟩ : ContMetric d) := Subtype.ext (metricLift_eq hM)
      simpa [L, he] using hLen
  rw [heq]
  exact hT.inter (hL.preimage metricLift_meas)

/-- A measure-specific Borel version of the intrinsic metric on length metrics. -/
theorem l6c_exists_internal_borel_version
    (ν : Measure C(Rd d × Rd d, ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ X ∂ν, IsContLengthFn X)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    ∃ F : C(Rd d × Rd d, ℝ) → C(U × U, ℝ), Measurable F ∧
      ∀ᵐ X ∂ν, ∃ D : ContMetric d, ∃ hD : D.IsLength, D.1 = X ∧
        F X = internalC D hD hU hUc := by
  classical
  let μ : Measure (ContMetric d) := ν.map (metricLift (d := d))
  have hμprob : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff metricLift_meas.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure μ := hμprob
  obtain ⟨M, hMsub, hMmeas, hMae⟩ :=
    (determ_uMeasurableSet_isLength d μ inferInstance).exists_measurable_subset_ae_eq
  have hMmeas' : MeasurableSet M := hMmeas
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ := exists_measurable_superset_of_null
    (show μ ({D : ContMetric d | D.IsLength} \ M) = 0 from ae_le_set.1 hMae.symm.le)
  let Dgood : C(Rd d × Rd d, ℝ) → ContMetric d :=
    fun X => if h : metricLift X ∈ M then metricLift X else defaultD
  have hDgood : ∀ X, (Dgood X).IsLength := by
    intro X
    dsimp [Dgood]
    split_ifs with hh
    · exact hMsub hh
    · exact defaultD_len
  have hDmeas : Measurable Dgood := by
    exact Measurable.ite (metricLift_meas hMmeas')
      metricLift_meas measurable_const
  let F : C(Rd d × Rd d, ℝ) → C(U × U, ℝ) :=
    fun X => internalC (Dgood X) (hDgood X) hU hUc
  let _ := hU.locallyCompactSpace
  have hFm : Measurable F := measurable_internalC_of_measurable Dgood hDmeas hDgood hU hUc
  refine ⟨F, hFm, ?_⟩
  have hNbad : ∀ᵐ X ∂ν, metricLift X ∉ N := by
    have hmap : ν {X | metricLift X ∈ N} = 0 := by
      change ν (metricLift ⁻¹' N) = 0
      rw [← Measure.map_apply metricLift_meas hNmeas]
      exact hNzero
    exact measure_eq_zero_iff_ae_notMem.mp hmap
  have hgood : ∀ᵐ X ∂ν, metricLift X ∈ M := by
    filter_upwards [hν, hNbad] with X hX hnot
    by_contra hbad
    obtain ⟨hMetric, hLen⟩ := hX
    have hlenLift : (metricLift X).IsLength := by
      simpa [metricLift, hMetric] using hLen
    exact hnot (hNsub ⟨hlenLift, hbad⟩)
  filter_upwards [hν, hgood] with X hX hXM
  obtain ⟨hMetric, hLen⟩ := hX
  refine ⟨metricLift X, ?_, metricLift_eq hMetric, ?_⟩
  · simpa [metricLift, hMetric] using hLen
  · simp [F, Dgood, hXM]

end HigherDimLQGMetric
