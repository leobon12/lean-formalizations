import SupercriticalConformalCovariance.Selection.JVN
import LQGMetric.Meas.UM

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SupercriticalConformalCovariance.Small

/-- The exact law of a Polish coordinate transfers universally measurable
events, including analytic witness projections. -/
theorem equal_law_preimage_um
    {Ω₁ Ω₂ X : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace X] (P : Measure Ω₁) (Q : Measure Ω₂)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω₁ → X) (g : Ω₂ → X)
    (hf : Measurable f) (hg : Measurable g)
    (hlaw : P.map f = Q.map g)
    (A : Set X) (hA : LQGMetric.UMeasurableSet A) :
    P (f ⁻¹' A) = Q (g ⁻¹' A) := by
  have hP : NullMeasurableSet A (P.map f) := hA _ inferInstance
  have hQ : NullMeasurableSet A (Q.map g) := hA _ inferInstance
  rw [← Measure.map_apply₀ hf.aemeasurable hP,
    ← Measure.map_apply₀ hg.aemeasurable hQ, hlaw]

theorem ae_of_equal_law_um
    {Ω₁ Ω₂ X : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace X] (P : Measure Ω₁) (Q : Measure Ω₂)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω₁ → X) (g : Ω₂ → X)
    (hf : Measurable f) (hg : Measurable g)
    (hlaw : P.map f = Q.map g)
    (A : Set X) (hA : LQGMetric.UMeasurableSet A)
    (hae : ∀ᵐ ω ∂P, f ω ∈ A) :
    ∀ᵐ ω ∂Q, g ω ∈ A := by
  apply ae_iff.mpr
  have hzero : P (f ⁻¹' Aᶜ) = 0 := by
    simpa only [Set.preimage, Set.mem_compl_iff] using (ae_iff.mp hae)
  have htransfer := equal_law_preimage_um P Q f g hf hg hlaw Aᶜ hA.compl
  rw [hzero] at htransfer
  simpa only [Set.preimage, Set.mem_compl_iff] using htransfer.symm

/-- An analytic failure event has a Borel failure flag after modification
on a null set, suitable as a compact Skorokhod mark. -/
theorem measurable_bool_flag_of_um
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : LQGMetric.UMeasurableSet A) :
    ∃ flag : Ω → Bool, Measurable flag ∧
      ∀ᵐ ω ∂P, (flag ω = true ↔ ω ∈ A) := by
  classical
  let B : Set Ω := toMeasurable P A
  have hB : MeasurableSet B := measurableSet_toMeasurable P A
  have hBA : B =ᵐ[P] A := (hA P inferInstance).toMeasurable_ae_eq
  refine ⟨fun ω => if ω ∈ B then true else false,
    measurable_const.ite hB measurable_const, ?_⟩
  filter_upwards [hBA] with ω hω
  simp only [B] at hω ⊢
  simp [hω]


end SupercriticalConformalCovariance.Small
