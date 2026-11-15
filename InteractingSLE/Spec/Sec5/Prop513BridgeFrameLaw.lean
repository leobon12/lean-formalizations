/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeFrame
import InteractingSLE.Spec.Sec5.Prop513FieldLaw
import InteractingSLE.Spec.Sec5.Carrier

/-!
# Gaussian law of the concrete inverse strip frame

A parameter field with the canonical transported boundary data returns to the
original GFF law. The proof reuses the forward bounded harmonic extension and
conformal covariance, so it introduces no inverse boundary-limit assumption.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Prop513Bridge

open Sec4 CrossRestart Sec7.StripSysField

/-- Conformal covariance for the landed inverse test transport. -/
theorem isZBGFFProcess_cfBackTest {q : ℝ} (hq : 0 < q)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hP : Ω → DistOn upperHalfPlaneOpens} {m : ℂ → ℝ}
    (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun ψ ω => hP ω ψ - ∫ z, m z * ψ z) P) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => hP ω (cfBackTest hq φ) -
        (∫ z, m ((stripCounterflowChart q).1 z) * φ z)) P := by
  have key : ∀ U : TopologicalSpace.Opens ℂ, U = upperHalfPlaneOpens →
      LQGMetric.IsZBGFFProcess U
        (fun ψ ω => hP ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) P := by
    rintro U rfl
    have hid : ∀ ψ : TestOn upperHalfPlaneOpens,
        GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens ψ = ψ := by
      intro ψ
      ext z
      exact congrFun (GFF.coe_testIncl le_rfl ψ) z
    simp only [hid]
    exact hX
  have h := SupercriticalConformalCovariance.ZBConformal.isZBGFFProcess_pullProcess
    (backChart_isConformal hq).isConformalBijection (key _ (backChart_dom hq))
  convert h using 2 with φ
  funext ω
  change _ = hP ω (Chart.pushTest (backChart_isConformal hq) φ) -
    (∫ z, m z * SupercriticalConformalCovariance.confPushTest
      (backChart_isConformal hq).isConformalBijection φ z)
  rw [pushTest_backChart hq,
    SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest]
  simp_rw [backChart_inv hq]

/-- The inverse transport recovers the source GFF from its canonical parameter
boundary law; there is no additional field-covariance hypothesis. -/
theorem isGFFWithBoundaryData_parameterSource {q : ℝ} (hq : 0 < q) (a k : ℝ)
    {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hP : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsGFFWithBoundaryData P hP (Prop513Field.data q a k b)
      (Prop513Field.jumps q J)) :
    IsGFFWithBoundaryData P (fun ω => parameterSource hq a k (hP ω)) b J := by
  refine ⟨(measurable_parameterSource hq a k).comp hG.1, fun u hu => ?_⟩
  let v : ℂ → ℝ := fun z => -u ((stripCounterflowChart q).2.1 z) + a +
    k * (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z)
  have hv := Prop513Field.harmonicExtension hq a k hu
  have hX := isZBGFFProcess_neg (isZBGFFProcess_cfBackTest hq (hG.2 v hv))
  convert hX using 2 with φ
  funext ω
  have hiu := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    hu.1.continuousOn φ φ.tsupport_subset
  have his := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    (continuousOn_cfShift q a k) φ φ.tsupport_subset
  have he : (∫ z, v ((stripCounterflowChart q).1 z) * φ z) =
      -(∫ z, u z * φ z) + (∫ z, cfShift q a k z * φ z) := by
    have hf : (fun z => v ((stripCounterflowChart q).1 z) * φ z) =
        fun z => -(u z * φ z) + cfShift q a k z * φ z := by
      funext z
      by_cases hz : z ∈ H
      · dsimp only [v]
        rw [stripCounterflowChart_inv_fwd hq (WangWu.ne_zero_of_mem_H hz)]
        dsimp only [cfShift]
        ring
      · have h0 : φ z = 0 := φ.zero_on_compl hz
        rw [h0, mul_zero, mul_zero, mul_zero, neg_zero, zero_add]
    rw [hf, integral_add (f := fun z => -(u z * φ z))
      (g := fun z => cfShift q a k z * φ z) hiu.neg his, integral_neg]
  rw [parameterSource_apply, he]
  ring

/-- The source-law hypothesis `hGF` for the concrete recovered frame, specialized
to Fig. 5.1. Only the actual parameter field's canonical boundary word is needed. -/
theorem isStripGFF_parameterSource {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hP : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsGFFWithBoundaryData P hP
      (stripCounterflowData κ 0 (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b'))
      (Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}))) :
    IsStripGFF κ P
      (fun ω => parameterSource (Real.exp_pos (π * x₀)) (-(π * QuantumZipper.chiC κ))
        (QuantumZipper.chiC (16 / κ)) (hP ω))
      (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} := by
  apply isGFFWithBoundaryData_parameterSource
  have hd := Prop513Field.data_eq hκ (Real.exp_pos (π * x₀)) 0
    (fig51Lower a b) (fig51Upper x₀ a' b')
  simp only [zero_add] at hd
  rw [hd]
  exact hG

end InteractingSLE.Sec5.Prop513Bridge
