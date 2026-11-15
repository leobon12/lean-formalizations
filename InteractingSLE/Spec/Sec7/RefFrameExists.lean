/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RefFrame
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Sec7.StripSysBorel

/-!
# Aux. lemma 130's strip word admits a strip system

Packet PROVE-REFFRAME. With the frame fixed (`aux130Frame`, `RefFrame`), Theorem 1.2's remaining Figure 5.1 identity
`hRefWord` asks the pocket word's strip system to have Aux. lemma 130's strip word (`Frame.word`). This file checks that
this choice is available to whoever constructs the strip system:

* **`aux130Frame_counterflowData_of_neg`, `…_of_pos`**: the counterflow word of Aux. lemma 130's strip word is
  `−λ − 3πχ/2` on `(−∞, 0)` and `λ + 3πχ/2` on `(0, ∞)` (off `±1`);
* **`isNonhitCounterflowWord_aux130Frame`**: it is a non-hit counterflow word (both sides' group-end sums at least
  some `c > −2`);
* **`exists_isStripSystem_aux130Frame`**: hence `StripSysBorel.exists_isStripSystem` builds a strip system with this
  word from Theorem 1.4's construction input (`Theorem14.StagedHistoryConstructionStatement`). This existence lemma is
  a consistency check of the frontier, not a step of Theorem 1.2's proof.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Sec7.StripMarks

open StripSysField Sec4 Sec5

variable {κ : ℝ}

/-- The counterflow word of a strip word, read from the strip word at `−1/y` (`inverseData`). -/
theorem counterflowData_eq_of_neg (hκ : 0 < κ) (b : ℝ → ℝ) {y : ℝ} (hy : y < 0) :
    counterflowData κ b y = -b (-y⁻¹) - π * chiC κ := by
  have hl : liftBoundary y = -(2 * π) := ite_eq_left hy
  rw [counterflowData, inverseData, returnData, hl, cfOffset, cfCoeff, Sec4.chiC_sixteen_div hκ]
  ring

theorem counterflowData_eq_of_pos (hκ : 0 < κ) (b : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    counterflowData κ b y = -b (-y⁻¹) + π * chiC κ := by
  have hl : liftBoundary y = 0 := ite_eq_right (not_lt.2 hy.le)
  rw [counterflowData, inverseData, returnData, hl, cfOffset, cfCoeff, Sec4.chiC_sixteen_div hκ]
  ring

/-- **The counterflow word of Aux. lemma 130's strip word on `(−∞, 0)`** is `−λ − 3πχ/2` off `−1`. -/
theorem aux130Frame_counterflowData_of_neg (hκ : 0 < κ) {y : ℝ} (hy : y < 0) (hy1 : y ≠ -1) :
    counterflowData κ ((aux130Frame κ).word κ) y = -sleLambda κ - 3 * π * chiC κ / 2 := by
  have hpos : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero'.2 hy)
  have hne : -y⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have : y⁻¹ = -1 := by linarith
    rw [← inv_inv y, this, inv_neg, inv_one]
  rw [counterflowData_eq_of_neg hκ _ hy, aux130Frame_word_of_pos hpos hne]
  ring

/-- **The counterflow word of Aux. lemma 130's strip word on `(0, ∞)`** is `λ + 3πχ/2` off `1`. -/
theorem aux130Frame_counterflowData_of_pos (hκ : 0 < κ) {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    counterflowData κ ((aux130Frame κ).word κ) y = sleLambda κ + 3 * π * chiC κ / 2 := by
  have hneg : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
  have hne : -y⁻¹ ≠ -1 := by
    intro h
    apply hy1
    have : y⁻¹ = 1 := by linarith
    rw [← inv_inv y, this, inv_one]
  rw [counterflowData_eq_of_pos hκ _ hy, aux130Frame_word_of_neg hκ hneg hne]
  ring

theorem neg_one_mem_counterflowJumps_aux130 : (-1 : ℝ) ∈ counterflowJumps ({-1, 0, 1} : Finset ℝ) :=
  Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨1, by simp, by norm_num⟩)

theorem one_mem_counterflowJumps_aux130 : (1 : ℝ) ∈ counterflowJumps ({-1, 0, 1} : Finset ℝ) :=
  Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-1, by simp, by norm_num⟩)

/-- **Aux. lemma 130's strip word is a non-hit counterflow word**: the counterflow word is `−λ − 3πχ/2 < λ'` on the
left and `λ + 3πχ/2 > −λ'` on the right, so both sides of its angle-`0` flow-line word (parameter `16/κ`) have
group-end sums above some `c > −2` (`GW1Conn.exists_hasGroupEndSums_flowLineL/R`; the smaller of the two constants). -/
theorem isNonhitCounterflowWord_aux130Frame (hκ : 0 < κ) (hκ4 : κ < 4) :
    IsNonhitCounterflowWord κ ((aux130Frame κ).word κ) {-1, 0, 1} := by
  have hl := Sec4.sleLambda_pos hκ
  have hl' := Sec4.sleLambda_sixteen_div_pos hκ
  have hπχ : 0 < π * chiC κ := mul_pos Real.pi_pos (Sec4.chiC_pos hκ hκ4)
  have hk : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hb := isPiecewiseConstant_counterflowData κ (aux130Frame_isPiecewiseConstantBoundaryData hκ)
  obtain ⟨cL, hcL, hL⟩ := Theorem14.GW1Conn.exists_hasGroupEndSums_flowLineL hk hb (θ := 0) (fun y hy hyJ => by
    rw [aux130Frame_counterflowData_of_neg hκ hy (fun h => hyJ (h ▸ neg_one_mem_counterflowJumps_aux130)),
      zero_mul, add_zero]
    linarith)
  obtain ⟨cR, hcR, hR⟩ := Theorem14.GW1Conn.exists_hasGroupEndSums_flowLineR hk hb (θ := 0) (fun y hy hyJ => by
    rw [aux130Frame_counterflowData_of_pos hκ hy (fun h => hyJ (h ▸ one_mem_counterflowJumps_aux130)),
      zero_mul, add_zero]
    linarith)
  exact ⟨min cL cR, lt_min hcL hcR, fun j hj => (min_le_left _ _).trans (hL j hj),
    fun j hj => (min_le_right _ _).trans (hR j hj)⟩

/-- **A strip system with Aux. lemma 130's strip word exists** (from Theorem 1.4's construction input, as
`StripSysBorel.exists_isStripSystem`): the choice of `hRefWord`'s frame is compatible with `hWordS`. -/
theorem exists_isStripSystem_aux130Frame (hCon : Theorem14.StagedHistoryConstructionStatement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
      (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      StripSys.IsStripSystem κ ((aux130Frame κ).word κ) {-1, 0, 1} P h W' ζ' E :=
  StripSysBorel.exists_isStripSystem hCon hκ hκ4 (aux130Frame_isPiecewiseConstantBoundaryData hκ)
    (isNonhitCounterflowWord_aux130Frame hκ hκ4)

end InteractingSLE.Sec7.StripMarks
