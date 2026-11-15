/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513FieldChart
import InteractingSLE.GFF.PushforwardLaw

/-!
# GFF covariance with the canonical strip counterflow boundary data

The zero-boundary covariance is reused from `Chart.isZBGFFProcess_chartTransport`.
The mean is the bounded harmonic extension proved in `Prop513FieldChart`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Field

open QuantumZipper Sec4 Sec7.StripSysField

/-- Signed GFF covariance under `M_q`, with the explicit transported data and
finite exceptional set. -/
theorem gff {q : ℝ} (hq : 0 < q) (a k : ℝ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hG : IsGFFWithBoundaryData P h b J)
    (hT : ∀ ω, IsChartTransport (stripCounterflowChart q) (-1) a k (h ω) (h' ω)) :
    IsGFFWithBoundaryData P h' (data q a k b) (jumps q J) := by
  have hc := isConformal hq
  have hl := Chart.locallyIntegrableOn_of_continuousOn (continuousOn_lift_inv hq)
  have he : h' = fun ω => Chart.chartTransport hc (-1) a k (h ω) :=
    funext fun ω => (hT ω).eq_chartTransport hc hl
  refine ⟨?_, fun u₀ hu₀ => ?_⟩
  · rw [he]
    exact (Chart.measurable_chartTransport hc (-1) a k).comp hG.1
  · obtain ⟨u, hu, _⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    have hm := harmonicExtension hq a k hu
    have heq := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension
      (jumps q J).finite_toSet hm hu₀
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
    have hX := isZBGFFProcess_neg (Chart.isZBGFFProcess_chartTransport hc hl
      (m := u) 0 (key _ (dom_eq hq)))
    convert hX using 2 with φ
    funext ω
    have hi₁ : Integrable (fun z => u ((stripCounterflowChart q).2.1 z) * φ z) :=
      Coupling.MartMeans2.integrable_mul_test_of_continuousOn
        (hu.1.continuousOn.comp hc.1.continuousOn hc.2.1) φ φ.tsupport_subset
    have hi₂ : Integrable (fun z =>
        (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z) * φ z) :=
      Coupling.MartMeans2.integrable_mul_test_of_continuousOn
        (continuousOn_lift_inv hq) φ φ.tsupport_subset
    have hi₃ : Integrable (fun z => a * φ z) :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul a
    have e₀ : (fun z => u₀ z * φ z) = fun z =>
        (-u ((stripCounterflowChart q).2.1 z) + a +
          k * (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z)) * φ z := by
      funext z
      by_cases hz : z ∈ H
      · rw [heq hz]
      · have h0 : φ z = 0 :=
          φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
        rw [h0, mul_zero, mul_zero]
    have e₁ : (∫ z, u₀ z * φ z) = -(∫ z, u ((stripCounterflowChart q).2.1 z) * φ z) +
        a * (∫ z, φ z) +
        k * (∫ z, (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z) * φ z) := by
      rw [e₀]
      simp_rw [add_mul, neg_mul, mul_assoc]
      rw [integral_add (f := fun z => -(u ((stripCounterflowChart q).2.1 z) * φ z) + a * φ z)
        (g := fun z => k * ((stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z) * φ z))
        (hi₁.neg.add hi₃) (hi₂.const_mul k),
        integral_add (f := fun z => -(u ((stripCounterflowChart q).2.1 z) * φ z))
          (g := fun z => a * φ z) hi₁.neg hi₃,
        integral_neg, integral_const_mul, integral_const_mul]
    rw [(hT ω).apply_eq hc φ, e₁, Chart.chartTransport_apply hc hl]
    ring

/-- The signed chart boundary datum is the canonical strip-counterflow datum. -/
theorem data_eq {κ q : ℝ} (hκ : 0 < κ) (hq : 0 < q) (α : ℝ) (bL bU : ℝ → ℝ) :
    data q (-((α + Real.pi) * chiC κ)) (chiC (16 / κ)) (stripHData κ bL bU) =
      stripCounterflowData κ α q bL bU := by
  funext x
  rw [data, chiC_sixteen_div hκ]
  have hc : 0 < 1 + q := by linarith
  by_cases hx : -1 < x
  · have hi : realInv q x < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hc) (by linarith)
    have hl : liftBoundary (realInv q x) = -(2 * Real.pi) := ite_eq_left hi
    rw [hl, stripCounterflowData, ite_eq_left hx]
    dsimp only [realInv]
    ring
  · have hi : 0 ≤ realInv q x :=
      div_nonneg_of_nonpos (neg_nonpos.2 hc.le) (by linarith)
    have hl : liftBoundary (realInv q x) = 0 := ite_eq_right (not_lt.2 hi)
    rw [hl, stripCounterflowData, ite_eq_right hx]
    dsimp only [realInv]
    ring

/-- Canonical field transport follows from the original strip GFF and its
piecewise-constant lower and upper data. -/
theorem canonicalFieldStatement {κ x₀ : ℝ} (hκ : 0 < κ)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hL : IsPiecewiseConstantBoundaryData bL JL)
    (hU : IsPiecewiseConstantBoundaryData bU JU)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h bL bU JL JU) :
    StripCounterflowCanonicalFieldStatement κ x₀ bL bU P h := by
  have hq : 0 < Real.exp (Real.pi * x₀) := Real.exp_pos _
  have hb := isPiecewiseConstantBoundaryData_stripHData κ hL hU
  have hd := data_eq hκ hq (-(Real.pi / 2)) bL bU
  refine ⟨jumps (Real.exp (Real.pi * x₀)) (stripHJumps JL JU), ?_, ?_⟩
  · rw [← hd]
    exact isPiecewiseConstant_data hq _ _ hb
  · intro h' hT
    rw [← hd]
    exact gff hq _ _ hb hG hT

end InteractingSLE.Sec5.Prop513Field
