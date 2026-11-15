/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1Base
import InteractingSLE.Spec.Supplement.GW1
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# The boundary data of the centred counterflow word

Packet PROVE-T14-CONE (a step of GW2's forced arcs, `GW2ConeArc.lean`). The frozen
`IsCenteredCounterflowDriver κ P h W ζ` says that `W` drives the flow line, at parameter `16/κ` and angle `0`, of a
field `h'` with *some* piecewise-constant data `b'`, where `h'` is the infinity-source transport of `h` (FD11.1,
FD12.1–FD12.2). This file identifies the force word: `b'` agrees with `Sec7.StripSysField.counterflowData κ b` off a
finite set, so the driver is the flow-line driver of the explicit word of `counterflowData κ b`
(`isFlowLineDriver_counterflowData`). The steps:

* `eq_returnField_of_isChartTransport`: the infinity-source transport determines `h` from `h'`
  (`h = −h' ∘ R + a + k ℓ`, the landed `returnField`);
* `eq_of_isGFFWithBoundaryData`: a GFF has at most one boundary datum off its exceptional sets (uniqueness of the mean
  of a zero-boundary GFF and of harmonic representatives, as in `GW1.eq_off_of_isGFF`);
* `isFlowLineDriver_counterflowData`: the assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Cone

open Sec7.StripSysField

/-- The infinity-source and return transports of test functions compose to the identity (the other order of
`Sec7.StripSysField.pushTest_return_pushTest`). -/
theorem pushTest_source_return (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest Chart.isConformal_infinitySourceChart (Chart.pushTest isConformal_infinityReturnChart φ) = φ := by
  ext z
  by_cases hz : z ∈ H
  · have hz' : z ∈ infinitySourceChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinitySourceChart]; exact hz
    have hRz : (-z⁻¹) ∈ infinityReturnChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinityReturnChart]; exact negInv_mem_H hz
    rw [Chart.pushTest_apply_of_mem _ _ hz']
    change ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2 * Chart.pushTest _ φ (-z⁻¹) = φ z
    rw [Chart.pushTest_apply_of_mem _ _ hRz]
    change ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2 * (‖deriv (fun z : ℂ => -z⁻¹) (-z⁻¹)‖ ^ 2 * φ (-(-z⁻¹)⁻¹)) = φ z
    rw [norm_deriv_negInv, norm_deriv_negInv, negInv_negInv, norm_neg, norm_inv, inv_inv, ← mul_assoc,
      ← mul_pow, ← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_H_ne_zero hz)), one_pow, one_pow, one_mul]
  · have hz' : z ∉ infinitySourceChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinitySourceChart]; exact hz
    rw [Chart.pushTest_apply_of_notMem _ _ hz']
    exact (φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)).symm

/-- **The infinity-source transport determines the field**: if `h'` is the transport of `h` by `R(z) = −1/z` with
coefficients `(−1, a, k)`, then `h` is the return field of `h'`. -/
theorem eq_returnField_of_isChartTransport {a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport infinitySourceChart (-1) a k h h') : h = returnField a k h' := by
  ext φ
  set ψ := Chart.pushTest isConformal_infinityReturnChart φ with hψ
  have h1 := ht.apply_eq Chart.isConformal_infinitySourceChart ψ
  have e0 : Chart.pushTest Chart.isConformal_infinitySourceChart ψ = φ := pushTest_source_return φ
  have e1 : ∫ w, ψ w = ∫ w, φ w := by
    have h := Chart.integral_mul_pushTest isConformal_infinityReturnChart φ (fun _ => 1)
    simpa only [one_mul] using h
  have e2 : ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * ψ w =
      ∫ w, infinitySourceChart.2.2 w * φ w := by
    rw [Chart.integral_mul_pushTest isConformal_infinityReturnChart φ]
    congr 1
    funext w
    change infinitySourceChart.2.2 (-(-w⁻¹)⁻¹) * φ w = _
    rw [negInv_negInv]
  rw [e0, e1, e2] at h1
  rw [returnField_apply, ← hψ, h1]
  ring

/-- **A GFF has at most one boundary datum** off the exceptional sets: if `h` is a GFF with data `g` (off `S`) and with
data `g'` (off `S'`), both admitting bounded harmonic extensions, then `g = g'` off `S ∪ S'`. -/
theorem eq_of_isGFFWithBoundaryData {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {g g' : ℝ → ℝ} {S S' : Set ℝ} {u u' : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hu' : IsBoundedHarmonicExtension g' S' u')
    (hh : IsGFFWithBoundaryData P h g S) (hh' : IsGFFWithBoundaryData P h g' S') :
    ∀ x : ℝ, x ∉ S → x ∉ S' → g x = g' x := by
  have hX := hh.2 u hu
  set c : TestOn upperHalfPlaneOpens → ℝ := fun φ => (∫ z, u z * φ z) - ∫ z, u' z * φ z with hc
  have hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => (h ω φ - ∫ z, u z * φ z) + c φ) P := by
    have e : (fun φ ω => (h ω φ - ∫ z, u z * φ z) + c φ) = (fun φ ω => h ω φ - ∫ z, u' z * φ z) := by
      funext φ ω
      rw [hc]
      ring
    rw [e]
    exact hh'.2 u' hu'
  have hc0 := GW1.eq_zero_of_isZBGFFProcess_add hX hY
  have heq : EqOn u' u H :=
    Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl hu'.1 hu.1 fun φ _ => by
      have := hc0 φ
      simp only [hc] at this
      linarith
  intro x hx hx'
  have t1 := hu.2.2 x hx
  have t2 : Tendsto u (𝓝[H] (x : ℂ)) (𝓝 (g' x)) :=
    (hu'.2.2 x hx').congr' (eventually_nhdsWithin_of_forall fun z hz => heq hz)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (x : ℂ)) (by simp)
  exact tendsto_nhds_unique t1 t2

/-- `IsTranslateAddConst 0 0` is the identity. -/
theorem eq_of_isTranslateAddConst_zero {c : ℝ} (hc : c = 0) {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsTranslateAddConst 0 c h h') : h' = h := by
  ext φ
  rw [ht φ φ fun z => by rw [Complex.ofReal_zero, add_zero], hc, zero_mul, add_zero]

/-- **The data of the counterflow field agree with `counterflowData κ b` off a finite set**: if `h` is a GFF with data
`b`, `h'` its infinity-source transport (coefficients `(−1, −πχ, χ(16/κ))`) and `h'` a GFF with data `b'`, then
`b' = counterflowData κ b` off a finite set. -/
theorem eq_counterflowData_off {κ : ℝ} {b b' : ℝ → ℝ} {jumps J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hb' : IsPiecewiseConstantBoundaryData b' J')
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hh' : IsGFFWithBoundaryData P h' b' J') :
    ∀ y, y ∉ returnExcept (jumps ∪ returnExcept J') → b' y = counterflowData κ b y := by
  have hR := isGFFWithBoundaryData_returnField (cfOffset κ) (cfCoeff κ)
    (by obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'; exact ⟨u, hu⟩) hh'
  have hfun : (fun ω => returnField (cfOffset κ) (cfCoeff κ) (h' ω)) = h :=
    funext fun ω => (eq_returnField_of_isChartTransport (htr ω)).symm
  rw [hfun] at hR
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨u', hu', -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    (isPiecewiseConstant_returnData (cfOffset κ) (cfCoeff κ) hb')
  have heq := eq_of_isGFFWithBoundaryData hu hu' hh hR
  intro y hy
  have hy0 : y ≠ 0 := ne_zero_of_notMem_returnExcept hy
  have hy1 : -y⁻¹ ∉ jumps ∪ returnExcept J' := negInv_notMem_of_notMem_returnExcept hy
  have e := heq (-y⁻¹) (fun hm => hy1 (Finset.mem_union_left _ hm)) (fun hm => hy1 (Finset.mem_union_right _ hm))
  have hl := liftBoundary_add_liftBoundary_negInv hy0
  have hyy : -(-y⁻¹)⁻¹ = y := by rw [inv_neg, inv_inv, neg_neg]
  simp only [returnData, hyy] at e
  simp only [counterflowData, inverseData, returnData]
  linear_combination e + cfCoeff κ * hl

/-- **The centred counterflow is the flow line of the explicit counterflow word** (FD11.1, FD12.1–FD12.2): for a GFF
`h` with data `b`, any driver `W` of the centred counterflow of `h` is, for the infinity-source transport `h'` of `h`,
the angle-`0` flow-line driver at parameter `16/κ` of the word of `counterflowData κ b`. -/
theorem isFlowLineDriver_counterflowData {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W ζ) :
    ∃ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
        (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) ∧
      IsFlowLineDriver (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 P h' W ζ := by
  obtain ⟨b', J', h', hb', htr, hfl⟩ := hcf
  have hκ' : 0 < 16 / κ := by positivity
  refine ⟨h', htr, ?_⟩
  have hgff : IsGFFWithBoundaryData P h' b' J' := by
    obtain ⟨h'', 𝓕, VL, VR, B, htac, hC⟩ := hfl
    have e : h'' = h' := funext fun ω => eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
    subst e
    exact isGFFWithBoundaryData_of_flowLineGFF hκ' hb' ⟨hC.2.1, hC.2.2.1⟩
  have hoff := eq_counterflowData_off hb hb' hh htr hgff
  have hlims := GW1.lims_eq_of_eq_off_finset (returnExcept (jumps ∪ returnExcept J')) hoff
  have hL : PiecewiseConstantBoundaryData.leftLim b' =
      PiecewiseConstantBoundaryData.leftLim (counterflowData κ b) := funext fun x => (hlims x).1
  have hR : PiecewiseConstantBoundaryData.rightLim b' =
      PiecewiseConstantBoundaryData.rightLim (counterflowData κ b) := funext fun x => (hlims x).2
  exact GW1.isFlowLineDriver_congr
    (GW1.jumpSet_eq_of_lims hb' (isPiecewiseConstant_counterflowData κ hb) hL hR) hL hR hfl

end GW2Cone

end Theorem14

end InteractingSLE
