/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4TraverseField
import InteractingSLE.Spec.Supplement.GW2JointKernelProofWord
import InteractingSLE.Spec.Supplement.GW3Word

/-!
# GW1's restart laws: the canonical centred counterflow of a word and a field

Packet PROVE-GW1-LAWS. For a boundary word `c` and a field `f`, `cfDrvOf h12p hκ (c, f)` is the field-determined
driver and lifetime (Theorem 1.2 jointly measurable in the word, R44) of the angle-`0` flow line at `16/κ` of the
inverted parameter field `cfField κ f`, read with the returned word `cfWordOf κ c` of `c`. Unlike
`GW4Traverse.cfDrv` (one fixed datum), it is **jointly measurable in the word and the field**, so it can be evaluated
at a random conditional word.

* `measurable_cfDrvOf`;
* **`isCenteredCounterflowDriver_cfDrvOf`**: under every probability measure, for a GFF with the data of a sorted word,
  the canonical driver is a frozen centred counterflow driver;
* **`ae_cfDrvOf_snd_eq_top`**: if the word satisfies the two-sided bounds `c(y) − (π/2)χ < λ` (`y < 0`) and
  `−λ < c(y) + (π/2)χ` (`y > 0`) (the form of `GW1Conn.ambient_bounds`), the canonical lifetime is almost surely
  infinite (GW0's backward implication on the counterflow word).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Laws

open Restart Sec7.StripSysField GW4Traverse GW2JointKernel

/-- The returned (counterflow) word of a boundary word: its data is `counterflowData κ c.fn` off the jumps. -/
def cfWordOf (κ : ℝ) (c : BoundaryWord) : BoundaryWord :=
  retWord (cfOffset κ - 2 * Real.pi * cfCoeff κ) (-cfCoeff κ) c

theorem measurable_cfWordOf (κ : ℝ) : Measurable (cfWordOf κ) := measurable_retWord _ _

theorem isSorted_cfWordOf (κ : ℝ) {c : BoundaryWord} (hc : c.IsSorted) : (cfWordOf κ c).IsSorted :=
  isSorted_retWord hc _ _

theorem jumps_cfWordOf (κ : ℝ) {c : BoundaryWord} (hc : c.IsSorted) :
    (cfWordOf κ c).jumps = counterflowJumps c.jumps :=
  jumps_retWord hc _ _

theorem fn_cfWordOf (κ : ℝ) {c : BoundaryWord} (hc : c.IsSorted) {y : ℝ} (hy : y ∉ (cfWordOf κ c).jumps) :
    (cfWordOf κ c).fn y = counterflowData κ c.fn y :=
  fn_retWord hc _ _ hy

/-- The inverted parameter field of a GFF with the data of a sorted word is the GFF of its returned word. -/
theorem isGFFWithBoundaryData_cfField_cfWordOf (κ : ℝ) {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type*}
    [MeasurableSpace Ω] {Q : Measure Ω} {f : Ω → DistOn upperHalfPlaneOpens}
    (hf : IsGFFWithBoundaryData Q f c.fn c.jumps) :
    IsGFFWithBoundaryData Q (fun ω => cfField κ (f ω)) (cfWordOf κ c).fn (cfWordOf κ c).jumps :=
  isGFFWithBoundaryData_returnField_retWord hc _ _ hf

section Canonical

variable (h12p : Exist.Staged.Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)

/-- **The canonical centred counterflow of a word and a field**: the field-determined driver and lifetime of the
angle-`0` flow line at `16/κ` of `cfField κ f`, for the returned word. -/
def cfDrvOf (q : BoundaryWord × DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  Restart.driverOf h12p (sixteen_div_pos hκ) 0 (cfWordOf κ q.1, cfField κ q.2)

theorem measurable_cfDrvOf : Measurable (cfDrvOf h12p hκ) :=
  (Restart.measurable_driverOf h12p (sixteen_div_pos hκ) 0).comp
    (((measurable_cfWordOf κ).comp measurable_fst).prodMk ((measurable_cfField κ).comp measurable_snd))

/-- The canonical driver is continuous before its lifetime and starts at `0`. -/
theorem cfDrvOf_regular (q : BoundaryWord × DistOn upperHalfPlaneOpens) :
    ContinuousOn (cfDrvOf h12p hκ q).1 {t | (t : ℝ≥0∞) < (cfDrvOf h12p hκ q).2} ∧ (cfDrvOf h12p hκ q).1 0 = 0 := by
  unfold cfDrvOf
  rw [Restart.driverOf_mk]
  exact ⟨(Exist.Staged.drvOf_regular _).1, (Exist.Staged.drvOf_regular _).2.1⟩

/-- **The field-determined coupling of any almost sure version of the canonical driver** with the flow field of the
inverted field, for the flow-line word at `16/κ` of the returned word (`Restart.isOptionalHullCoupling_of_detAgree`):
a measurable driver and a measurable lifetime that almost surely equal the canonical ones. -/
theorem exists_coupling_of_ae_cfDrvOf (h13 : Exist.Theorem13Statement.{u}) {c : BoundaryWord}
    (hc : c.IsSorted) {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC c.fn c.jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hW : ∀ t, Measurable (W t)) (hζ : Measurable ζ)
    (hae : ∀ᵐ ω ∂Q, ζ ω = (cfDrvOf h12p hκ (c, hC ω)).2 ∧ ∀ t, W t ω = (cfDrvOf h12p hκ (c, hC ω)).1 t) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL (cfWordOf κ c).fn (cfWordOf κ c).jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR (cfWordOf κ c).fn (cfWordOf κ c).jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL (cfWordOf κ c).fn (cfWordOf κ c).jumps 0)
        (flowLineXR (cfWordOf κ c).fn (cfWordOf κ c).jumps 0)
        (flowLineRhoL (16 / κ) (cfWordOf κ c).fn (cfWordOf κ c).jumps 0 0)
        (flowLineRhoR (16 / κ) (cfWordOf κ c).fn (cfWordOf κ c).jumps 0 0) Q 𝓕 W VL VR B ζ
        (fun ω => Exist.flowField 0 (0 * chiC (16 / κ)) (cfField κ (hC ω))) := by
  have hκ' := sixteen_div_pos hκ
  set c' := cfWordOf κ c with hc'
  have hcw : IsGFFWithBoundaryData Q (fun ω => cfField κ (hC ω)) c'.fn c'.jumps :=
    isGFFWithBoundaryData_cfField_cfWordOf κ hc hh
  have hF := Theorem15.isOrderedForceWord_flowLine c'.fn c'.jumps 0
  have hh' := Exist.isGFFWithBoundaryData_flowField hκ' c'.isPiecewiseConstantBoundaryData 0 0 hcw
  refine Restart.isOptionalHullCoupling_of_detAgree h12p h13 hκ' hF hh' hW hζ (hae.mono fun ω hω => ?_)
  have e : cfDrvOf h12p hκ (c, hC ω) = Exist.Staged.drvOf (Exist.Staged.detCode
      (Exist.Staged.paramΦ h12p hκ' (flowLineNL c'.fn c'.jumps 0) (flowLineNR c'.fn c'.jumps 0))
      (((flowLineXL c'.fn c'.jumps 0, flowLineXR c'.fn c'.jumps 0),
        (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0, flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0)),
        Exist.flowField 0 (0 * chiC (16 / κ)) (cfField κ (hC ω)))) := by
    unfold cfDrvOf
    exact Restart.driverOf_mk h12p hκ' 0 _ _
  rw [← e]
  exact ⟨hω.1, hω.2 0, fun t _ => hω.2 t⟩

/-- **The field-determined coupling of the canonical driver** itself. -/
theorem exists_coupling_cfDrvOf (h13 : Exist.Theorem13Statement.{u}) {c : BoundaryWord}
    (hc : c.IsSorted) {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC c.fn c.jumps) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL (cfWordOf κ c).fn (cfWordOf κ c).jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR (cfWordOf κ c).fn (cfWordOf κ c).jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL (cfWordOf κ c).fn (cfWordOf κ c).jumps 0)
        (flowLineXR (cfWordOf κ c).fn (cfWordOf κ c).jumps 0)
        (flowLineRhoL (16 / κ) (cfWordOf κ c).fn (cfWordOf κ c).jumps 0 0)
        (flowLineRhoR (16 / κ) (cfWordOf κ c).fn (cfWordOf κ c).jumps 0 0) Q 𝓕
        (fun t ω => (cfDrvOf h12p hκ (c, hC ω)).1 t) VL VR B (fun ω => (cfDrvOf h12p hκ (c, hC ω)).2)
        (fun ω => Exist.flowField 0 (0 * chiC (16 / κ)) (cfField κ (hC ω))) := by
  have hD : Measurable fun ω => cfDrvOf h12p hκ (c, hC ω) :=
    (measurable_cfDrvOf h12p hκ).comp (measurable_const.prodMk hh.1)
  exact exists_coupling_of_ae_cfDrvOf h12p hκ h13 hc hh
    (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD)) (measurable_snd.comp hD)
    (Eventually.of_forall fun ω => ⟨rfl, fun _ => rfl⟩)

/-- **Any almost sure version of the canonical driver drives the centred counterflow** of a GFF with the data of a
sorted word. -/
theorem isCenteredCounterflowDriver_of_ae_cfDrvOf (h13 : Exist.Theorem13Statement.{u}) {c : BoundaryWord}
    (hc : c.IsSorted) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC c.fn c.jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hW : ∀ t, Measurable (W t)) (hζ : Measurable ζ)
    (hae : ∀ᵐ ω ∂Q, ζ ω = (cfDrvOf h12p hκ (c, hC ω)).2 ∧ ∀ t, W t ω = (cfDrvOf h12p hκ (c, hC ω)).1 t) :
    IsCenteredCounterflowDriver κ Q hC W ζ := by
  obtain ⟨𝓕, VL, VR, B, hcoup⟩ := exists_coupling_of_ae_cfDrvOf h12p hκ h13 hc hh hW hζ hae
  exact ⟨(cfWordOf κ c).fn, (cfWordOf κ c).jumps, fun ω => cfField κ (hC ω),
    (cfWordOf κ c).isPiecewiseConstantBoundaryData, fun ω => isChartTransport_cfField κ (hC ω), _, 𝓕, VL, VR, B,
    fun ω => Exist.isTranslateAddConst_flowField 0 _ _, hcoup⟩

/-- **The canonical driver drives the centred counterflow** of every GFF with the data of a sorted word, under every
probability measure (Theorem 1.2 jointly measurable in the word and Theorem 1.3). -/
theorem isCenteredCounterflowDriver_cfDrvOf (h13 : Exist.Theorem13Statement.{u}) {c : BoundaryWord}
    (hc : c.IsSorted) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC c.fn c.jumps) :
    IsCenteredCounterflowDriver κ Q hC (fun t ω => (cfDrvOf h12p hκ (c, hC ω)).1 t)
      (fun ω => (cfDrvOf h12p hκ (c, hC ω)).2) := by
  obtain ⟨𝓕, VL, VR, B, hcoup⟩ := exists_coupling_cfDrvOf h12p hκ h13 hc hh
  exact ⟨(cfWordOf κ c).fn, (cfWordOf κ c).jumps, fun ω => cfField κ (hC ω),
    (cfWordOf κ c).isPiecewiseConstantBoundaryData, fun ω => isChartTransport_cfField κ (hC ω), _, 𝓕, VL, VR, B,
    fun ω => Exist.isTranslateAddConst_flowField 0 _ _, hcoup⟩

/-- **The canonical lifetime is infinite under the two-sided height bounds** (GW0's backward implication on the
counterflow word): if `c(y) − (π/2)χ < λ` left of `0` and `−λ < c(y) + (π/2)χ` right of `0` (off the jumps), the
canonical counterflow of a GFF with the data of the sorted word `c` lives forever almost surely. -/
theorem ae_cfDrvOf_snd_eq_top (h13 : Exist.Theorem13Statement.{u}) {c : BoundaryWord} (hc : c.IsSorted)
    (hL : ∀ y, y < 0 → y ∉ c.jumps → c.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ y, 0 < y → y ∉ c.jumps → -sleLambda κ < c.fn y + Real.pi / 2 * chiC κ)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC c.fn c.jumps) :
    ∀ᵐ ω ∂Q, (cfDrvOf h12p hκ (c, hC ω)).2 = ⊤ := by
  have hκ' := sixteen_div_pos hκ
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  obtain ⟨𝓕, VL, VR, B, hcoup⟩ := exists_coupling_cfDrvOf h12p hκ h13 hc hh
  set c' := cfWordOf κ c with hc'
  have hF := Theorem15.isOrderedForceWord_flowLine c'.fn c'.jumps 0
  have hpc' := c'.isPiecewiseConstantBoundaryData
  have hdR : ∀ y, 0 < y → y ∉ c'.jumps → -sleLambda (16 / κ) < c'.fn y := by
    intro y hy hyJ
    rw [fn_cfWordOf κ hc hyJ, GW3Word.counterflowData_of_pos hκ c.fn hy, hΛ]
    rw [jumps_cfWordOf κ hc] at hyJ
    have hx : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
    have := hL (-y⁻¹) hx (negInv_notMem_of_notMem_returnExcept hyJ)
    linarith
  have hdL : ∀ y, y < 0 → y ∉ c'.jumps → c'.fn y < sleLambda (16 / κ) := by
    intro y hy hyJ
    rw [fn_cfWordOf κ hc hyJ, GW3Word.counterflowData_of_neg hκ c.fn hy, hΛ]
    rw [jumps_cfWordOf κ hc] at hyJ
    have hx : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have := hR (-y⁻¹) hx (negInv_notMem_of_notMem_returnExcept hyJ)
    linarith
  exact GW0.ae_lifetime_eq_top_of_neg_two_lt hF
    (fun j _ => GW3Word.neg_two_lt_sum_flowLineRhoL_of_forall hκ' hpc' hdL j)
    (fun j _ => GW3Word.neg_two_lt_sum_flowLineRhoR_of_forall hκ' hpc' hdR j) hcoup.1

end Canonical

end InteractingSLE.Theorem14.GW1Laws
