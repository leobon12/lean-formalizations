import MatedCRTHarmonic.Canon.Data
import MatedCRTHarmonic.CellScaling.JointScalingOArea
import MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import MatedCRTHarmonic.LQGCone.AreaBridge
import MatedCRTHarmonic.LQGCoord.WPArea
import MatedCRTHarmonic.GMCFacts.ConeCompare
import MatedCRTHarmonic.MoTPort.Foundations.ConeMeas
import MatedCRTHarmonic.CellScaling.Model
import LQGMetric.Papers.GM.S1.Dilate
import QuantumZipper.Proofs.LQG.MeasurabilityAE
import QuantumZipper.Proofs.Thm18.RTMeasArea
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The zero-cone mass clock is measurable from the field and Lebesgue curve

The measurable segment-area functional for area-parametrized curves is reused. Its equality with
the actual GMC trace follows from V3Sanity's vague-limit theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The cone field is almost surely measurable from the frozen GFF and
radial Brownian paths. -/
theorem aemeasurable_cone_field
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => (coneSample D hγ ω).field) P := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  let A : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t
  have hA : MoTPort.IsConeProcess γ (QuantumZipper.Qc γ) A P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B D.bm_B' D.indep_cone.2
  have hm := MoTPort.ConeMeas2.aemeasurable_coneField D.gff hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  exact (LQGCone.coneField_eq_motConeField γ γ (X ω)
    (fun t => B t ω) (fun t => B' t ω)).symm

/-- The zero-cone field is almost surely a measurable function of the frozen
whole-plane GFF and radial Brownian paths. -/
theorem aemeasurable_reference_field
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => (referenceSample D hγ ω).zeroConeField) P := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  let A : ℝ → Ω → ℝ := fun t ω =>
    LQGCone.motConeRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t
  have hA : MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ) A P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hm := MoTPort.ConeMeas2.aemeasurable_coneField D.gff₀ hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  exact (LQGCone.coneField_eq_motConeField γ 0 (X₀ ω)
    (fun t => B₀ t ω) (fun t => B₀' t ω)).symm

/-- The measurable trace functional agrees almost surely with the
reference GMC image clock at each fixed Lebesgue time. -/
theorem ae_referenceClock_eq_areaSeg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (t : ℝ) :
    ∀ᵐ ω ∂P, referenceClock D hγ ω t =
      CellScaling.JointScalingO.areaSeg γ (referenceSample D hγ ω).zeroConeField (ηL ω) t := by
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ] with ω hex
  have he : ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (coneField (X₀ ω)
        (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))) μ := hex
  have hv : CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (referenceSample D hγ ω).zeroConeField)
      (referenceSample D hγ ω).area := by
    change CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (coneField (X₀ ω)
        (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω))))
      (CellScaling.lqgArea γ (coneField (X₀ ω)
        (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω))))
    rw [CellScaling.lqgArea, dite_eq_left he]
    exact he.choose_spec
  rw [CellScaling.JointScalingO.areaSeg_eq γ hv (ηL ω) t]
  by_cases ht : 0 ≤ t
  · simp only [referenceClock, ite_eq_left ht, uIcc_of_le ht]
  · simp only [referenceClock, ite_eq_right ht, uIcc_of_ge (le_of_not_ge ht)]

/-- At every fixed time, the actual reference image-mass clock is almost
surely measurable as a function of the field and Lebesgue curve. -/
theorem aemeasurable_referenceClock_at
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (t : ℝ) :
    AEMeasurable (fun ω => referenceClock D hγ ω t) P := by
  have hm : AEMeasurable (fun ω =>
      CellScaling.JointScalingO.areaSeg γ (referenceSample D hγ ω).zeroConeField (ηL ω) t) P := by
    have hpair : AEMeasurable (fun ω =>
        ((referenceSample D hγ ω).zeroConeField, ηL ω)) P :=
      (aemeasurable_reference_field D hγ).prodMk D.measurable_curves.1.aemeasurable
    simpa only [Function.comp_def] using
      (CellScaling.JointScalingO.measurable_areaSeg γ t).comp_aemeasurable hpair
  have heq : (fun ω => referenceClock D hγ ω t) =ᵐ[P]
      (fun ω => CellScaling.JointScalingO.areaSeg γ
        (referenceSample D hγ ω).zeroConeField (ηL ω) t) :=
    ae_referenceClock_eq_areaSeg D hγ t
  exact hm.congr heq.symm

/-- The cone image clock is measurable at every fixed Lebesgue time. -/
theorem aemeasurable_coneClock_at
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (t : ℝ) :
    AEMeasurable (fun ω => coneClock D hγ ω t) P := by
  have hpair : AEMeasurable (fun ω =>
      ((coneSample D hγ ω).field, ηL ω)) P :=
    (aemeasurable_cone_field D hγ).prodMk D.measurable_curves.1.aemeasurable
  have hm : AEMeasurable (fun ω => CellScaling.JointScalingO.areaSeg γ
      (coneSample D hγ ω).field (ηL ω) t) P := by
    simpa only [Function.comp_def] using
      (CellScaling.JointScalingO.measurable_areaSeg γ t).comp_aemeasurable hpair
  have heq : (fun ω => coneClock D hγ ω t) =ᵐ[P]
      (fun ω => CellScaling.JointScalingO.areaSeg γ
        (coneSample D hγ ω).field (ηL ω) t) := by
    filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ] with ω hex
    have he : ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (coneSample D hγ ω).field) μ := hex
    change ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (coneField (X ω)
        (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))) μ at he
    have hv : CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (coneSample D hγ ω).field)
        (coneSample D hγ ω).area := by
      change CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))))
        (CellScaling.lqgArea γ (coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))))
      rw [CellScaling.lqgArea, dite_eq_left he]
      exact he.choose_spec
    rw [CellScaling.JointScalingO.areaSeg_eq γ hv (ηL ω) t]
    by_cases ht : 0 ≤ t
    · simp only [coneClock, ite_eq_left ht, uIcc_of_le ht]
    · simp only [coneClock, ite_eq_right ht, uIcc_of_ge (le_of_not_ge ht)]
  exact hm.congr heq.symm

/-- The normalized whole-plane GMC image clock agrees with the measurable
segment-mass functional at each fixed time. -/
theorem ae_wholePlaneClock_eq_areaSeg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (t : ℝ) :
    ∀ᵐ ω ∂P, wholePlaneClock D hγ ω t =
      CellScaling.JointScalingO.areaSeg γ
        (referenceSample D hγ ω).wholePlaneGFF (ηL ω) t := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hv := LQGCoord.ae_exists_isVagueLimitC_wp
    (normalizedWPGFF_of_coupling D).1 hγ.1 hγ.2
  filter_upwards [hv] with ω hex
  have he : ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (referenceSample D hγ ω).wholePlaneGFF) μ := hex
  have hval : CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (referenceSample D hγ ω).wholePlaneGFF)
      (referenceSample D hγ ω).wholePlaneArea := by
    change CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (normalizeWholePlane (X₀ ω)))
      (CellScaling.lqgArea γ (normalizeWholePlane (X₀ ω)))
    rw [CellScaling.lqgArea, dite_eq_left hex]
    exact hex.choose_spec
  rw [CellScaling.JointScalingO.areaSeg_eq γ hval (ηL ω) t]
  by_cases ht : 0 ≤ t
  · simp only [wholePlaneClock, ite_eq_left ht, uIcc_of_le ht]
  · simp only [wholePlaneClock, ite_eq_right ht, uIcc_of_ge (le_of_not_ge ht)]

theorem aemeasurable_wholePlaneClock_at
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (t : ℝ) :
    AEMeasurable (fun ω => wholePlaneClock D hγ ω t) P := by
  have hpair : Measurable fun ω =>
      ((referenceSample D hγ ω).wholePlaneGFF, ηL ω) :=
    (measurable_normalizedWholePlane D).prodMk D.measurable_curves.1
  have hm : Measurable fun ω => CellScaling.JointScalingO.areaSeg γ
      (referenceSample D hγ ω).wholePlaneGFF (ηL ω) t := by
    simpa only [Function.comp_def] using
      (CellScaling.JointScalingO.measurable_areaSeg γ t).comp hpair
  have heq : (fun ω => wholePlaneClock D hγ ω t) =ᵐ[P]
      (fun ω => CellScaling.JointScalingO.areaSeg γ
        (referenceSample D hγ ω).wholePlaneGFF (ηL ω) t) :=
    ae_wholePlaneClock_eq_areaSeg D hγ t
  exact hm.aemeasurable.congr heq.symm

end MatedCRTHarmonic.Canon
