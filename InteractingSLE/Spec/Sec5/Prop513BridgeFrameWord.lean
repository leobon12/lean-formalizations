/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeFrameLaw
import InteractingSLE.Spec.Restart.Datum

/-!
# The four intervals of the actual parameter word

The Fig. 5.1 parameter word has heights `-b-πχ`, `-b'`, `a'`,
`a+πχ` on the four intervals separated by `-1,0,exp(π x₀)`.
Finite exceptional-set differences do not affect its GFF law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Prop513Bridge
open Sec4 Sec7.StripSysField

/-- Far left parameter height. -/
theorem fig51Parameter_left {κ x₀ a b a' b' x : ℝ} (hx : x < -1) :
    stripCounterflowData κ 0 (Real.exp (π * x₀))
      (fig51Lower a b) (fig51Upper x₀ a' b') x = -b - π * chiC κ := by
  have hq := Real.exp_pos (π * x₀)
  have hy : 0 < -(1 + Real.exp (π * x₀)) / (x + 1) :=
    div_pos_of_neg_of_neg (by linarith) (by linarith)
  rw [stripCounterflowData, stripHData_fig51_of_pos _ _ _ _ _ _ hy,
    ite_eq_right (by linarith : ¬ (-1 < x)), zero_add, add_zero]

/-- The interval immediately to the left of the parameter seed. -/
theorem fig51Parameter_near_left {κ x₀ a b a' b' x : ℝ} (hx : x ∈ Ioo (-1) 0) :
    stripCounterflowData κ 0 (Real.exp (π * x₀))
      (fig51Lower a b) (fig51Upper x₀ a' b') x = -b' := by
  have hq := Real.exp_pos (π * x₀)
  have hy : -(1 + Real.exp (π * x₀)) / (x + 1) < -1 - Real.exp (π * x₀) := by
    rw [div_lt_iff₀ (by linarith [hx.1])]
    nlinarith only [hq, hx.2]
  rw [stripCounterflowData, stripHData_fig51_of_upper_right _ _ _ _ _ _ hy,
    ite_eq_left hx.1, zero_add]
  ring

/-- The interval immediately to the right of the parameter seed. -/
theorem fig51Parameter_near_right {κ x₀ a b a' b' x : ℝ}
    (hx : x ∈ Ioo 0 (Real.exp (π * x₀))) :
    stripCounterflowData κ 0 (Real.exp (π * x₀))
      (fig51Lower a b) (fig51Upper x₀ a' b') x = a' := by
  have hq := Real.exp_pos (π * x₀)
  have hy : -(1 + Real.exp (π * x₀)) / (x + 1) ∈
      Ioo (-1 - Real.exp (π * x₀)) (-1) := by
    constructor
    · rw [lt_div_iff₀ (by linarith [hx.1])]
      nlinarith only [hq, hx.1]
    · rw [div_lt_iff₀ (by linarith [hx.1])]
      linarith only [hx.2]
  rw [stripCounterflowData, stripHData_fig51_of_upper_left _ _ _ _ _ _ hy,
    ite_eq_left (by linarith [hx.1] : -1 < x), zero_add]
  ring

/-- Far right parameter height, retaining the inherited derivative argument. -/
theorem fig51Parameter_right {κ x₀ a b a' b' x : ℝ} (hx : Real.exp (π * x₀) < x) :
    stripCounterflowData κ 0 (Real.exp (π * x₀))
      (fig51Lower a b) (fig51Upper x₀ a' b') x = a + π * chiC κ := by
  have hq := Real.exp_pos (π * x₀)
  have hy : -(1 + Real.exp (π * x₀)) / (x + 1) ∈ Ioo (-1) 0 := by
    constructor
    · rw [lt_div_iff₀ (by linarith)]
      linarith only [hx]
    · exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  rw [stripCounterflowData, stripHData_fig51_of_mem_Ioo _ _ _ _ _ _ hy,
    ite_eq_left (by linarith : -1 < x), zero_add]
  ring

/-- Agreement off finitely many exceptional points transfers a boundary GFF
law, without requiring the two exceptional sets to coincide. -/
theorem isGFFWithBoundaryData_of_eq_off_union {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {b c : ℝ → ℝ} {J K : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J)
    (heq : ∀ x ∉ J ∪ K, b x = c x) : IsGFFWithBoundaryData P h c K := by
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  refine ⟨hh.1, fun v hv => ?_⟩
  have hu' : IsBoundedHarmonicExtension c (J ∪ K : Finset ℝ) u := by
    refine ⟨hu.1, hu.2.1, fun x hx => ?_⟩
    rw [← heq x hx]
    exact hu.2.2 x (fun hm => hx (Finset.mem_union_left _ hm))
  have hv' : IsBoundedHarmonicExtension c (J ∪ K : Finset ℝ) v :=
    ⟨hv.1, hv.2.1, fun x hx => hv.2.2 x (fun hm => hx (Finset.mem_union_right _ hm))⟩
  have he := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension
    (J ∪ K).finite_toSet hu' hv'
  convert hh.2 u hu using 2 with φ
  funext ω
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change v z * φ z = u z * φ z
    by_cases hz : z ∈ H
    · rw [he hz]
    · have h0 : φ z = 0 := φ.zero_on_compl hz
      rw [h0, mul_zero, mul_zero]

/-- Source-law realization for a recorded parameter field. The exact remaining
word identity is displayed pointwise off the two finite exceptional sets. -/
theorem isStripGFF_parameterSource_of_word {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hP : Ω → DistOn upperHalfPlaneOpens} {bP : ℝ → ℝ} {JP : Finset ℝ}
    (hbP : IsPiecewiseConstantBoundaryData bP JP) (hG : IsGFFWithBoundaryData P hP bP JP)
    (hword : ∀ x ∉ JP ∪ Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}),
      bP x = stripCounterflowData κ 0 (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b') x) :
    IsStripGFF κ P
      (fun ω => parameterSource (Real.exp_pos (π * x₀)) (-(π * chiC κ))
        (chiC (16 / κ)) (hP ω))
      (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} :=
  isStripGFF_parameterSource hκ (isGFFWithBoundaryData_of_eq_off_union hbP hG hword)

end InteractingSLE.Sec5.Prop513Bridge
