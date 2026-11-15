/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetMean

/-! # The canonical GFF law of the E-to-Q field -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4 Prop513Schedule

/-- GFF covariance for the concrete E-to-Q chart transport. The mean is fixed
by its bounded harmonic extension and the exact Q boundary limits. -/
theorem gff {κ q : ℝ} (hq : 0 < q)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hL : IsPiecewiseConstantBoundaryData bL JL)
    (hU : IsPiecewiseConstantBoundaryData bU JU)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h bL bU JL JU) :
    IsGFFWithBoundaryData P (fun ω => targetField κ q hq (h ω))
      (stripQHData κ q bL bU) (stripQHJumps q JL JU) := by
  have hc := targetChart_isConformal hq
  have hl := Chart.locallyIntegrableOn_of_continuousOn (continuousOn_lift_inv hq)
  refine ⟨(measurable_targetField κ q hq).comp hG.1, fun u₀ hu₀ => ?_⟩
  obtain ⟨u, hu, _⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    (isPiecewiseConstantBoundaryData_stripHData κ hL hU)
  have hm := harmonicExtension hq hu
  have heq := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension
    (stripQHJumps q JL JU).finite_toSet hm hu₀
  have key : ∀ U : TopologicalSpace.Opens ℂ, U = upperHalfPlaneOpens →
      LQGMetric.IsZBGFFProcess U
        (fun ψ ω => h ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, u z * ψ z) P := by
    rintro U rfl
    have hid : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
        GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens ψ = ψ := by
      intro ψ
      ext z
      exact congrFun (GFF.coe_testIncl le_rfl ψ) z
    simp only [hid]
    exact hG.2 u hu
  have hX := Chart.isZBGFFProcess_chartTransport hc hl (chiC κ) (key _ (dom_eq hq))
  convert hX using 2 with φ
  funext ω
  have hi₁ : Integrable (fun z => u ((targetChart q).2.1 z) * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (hu.1.continuousOn.comp hc.1.continuousOn hc.2.1) φ φ.tsupport_subset
  have hi₂ : Integrable (fun z => (targetChart q).2.2 ((targetChart q).2.1 z) * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (continuousOn_lift_inv hq) φ φ.tsupport_subset
  have e₀ : (fun z => u₀ z * φ z) = fun z =>
      (u ((targetChart q).2.1 z) + chiC κ * (targetChart q).2.2 ((targetChart q).2.1 z)) * φ z := by
    funext z
    by_cases hz : z ∈ H
    · rw [heq hz]
    · have h0 : φ z = 0 :=
        φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
      rw [h0, mul_zero, mul_zero]
  have e₁ : (∫ z, u₀ z * φ z) = (∫ z, u ((targetChart q).2.1 z) * φ z) +
      chiC κ * (∫ z, (targetChart q).2.2 ((targetChart q).2.1 z) * φ z) := by
    rw [e₀]
    simp_rw [add_mul, mul_assoc]
    rw [integral_add hi₁ (hi₂.const_mul (chiC κ)), integral_const_mul]
  rw [e₁]
  rfl

/-- The previously named target-coordinate field input is now proved. No
positivity assumption on `κ` is needed for covariance itself. -/
theorem canonicalFieldStatement {κ x₀ : ℝ}
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hL : IsPiecewiseConstantBoundaryData bL JL)
    (hU : IsPiecewiseConstantBoundaryData bU JU)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} :
    TargetCanonicalFieldStatement κ x₀ bL bU JL JU P h :=
  fun hG => gff (Real.exp_pos _) hL hU hG

end InteractingSLE.Sec5.Prop513Target
