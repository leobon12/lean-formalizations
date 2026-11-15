/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk6
import InteractingSLE.Spec.Supplement.GW1LawsCanon
import InteractingSLE.Spec.Supplement.BR4aPathField
import InteractingSLE.Spec.Supplement.SB2KZero

/-!
# The complete centred counterflow of the field read from the end of the forced arc

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). SB2(2) at the arc seed is applied in the field read
from `v` (`affField (−v) h = h(· + v)`), whose centred counterflow (from `∞` to `v`) must be complete:

* **`ae_lifetime_top_of_bounds`**: a centred counterflow driver lives forever almost surely under the two-sided
  height bounds (GW0's backward implication on its counterflow word; the argument of
  `GW1Laws.ae_cfDrvOf_snd_eq_top` for any driver);
* **`exists_complete_counterflow_tr`**: on the initial forced arc, the field read from `v` has a complete centred
  counterflow (Theorem 1.2's field-determined driver, `BR4aPath.exists_isCenteredCounterflowDriver_recField`; the
  bounds from GW1's ambient bounds of the original complete counterflow and the low arc).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate Sec7.StripSysField
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **A centred counterflow lives forever under the two-sided height bounds.** -/
theorem ae_lifetime_top_of_bounds {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hL : ∀ y, y < 0 → y ∉ J → b y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ y, 0 < y → y ∉ J → -sleLambda κ < b y + Real.pi / 2 * chiC κ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hκ' : 0 < 16 / κ := by positivity
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  obtain ⟨_, _, hfl⟩ := GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hF := Theorem15.isOrderedForceWord_flowLine (counterflowData κ b) (counterflowJumps J) 0
  have hpc' := isPiecewiseConstant_counterflowData κ hb
  have hdR : ∀ y, 0 < y → y ∉ counterflowJumps J → -sleLambda (16 / κ) < counterflowData κ b y := by
    intro y hy hyJ
    rw [GW3Word.counterflowData_of_pos hκ b hy, hΛ]
    have hx : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
    have := hL (-y⁻¹) hx (negInv_notMem_of_notMem_returnExcept hyJ)
    linarith
  have hdL : ∀ y, y < 0 → y ∉ counterflowJumps J → counterflowData κ b y < sleLambda (16 / κ) := by
    intro y hy hyJ
    rw [GW3Word.counterflowData_of_neg hκ b hy, hΛ]
    have hx : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have := hR (-y⁻¹) hx (negInv_notMem_of_notMem_returnExcept hyJ)
    linarith
  exact GW0.ae_lifetime_eq_top_of_neg_two_lt hF
    (fun j _ => GW3Word.neg_two_lt_sum_flowLineRhoL_of_forall hκ' hpc' hdL j)
    (fun j _ => GW3Word.neg_two_lt_sum_flowLineRhoR_of_forall hκ' hpc' hdR j) hC.1

/-- **The field read from the end of the forced arc has a complete centred counterflow.** -/
theorem exists_complete_counterflow_tr (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {v : ℝ} (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b J, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) :
    ∃ (Wv : ℝ≥0 → Ω → ℝ) (ζv : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P (fun ω => affField (-v) one_pos (h ω)) Wv ζv ∧ ∀ᵐ ω ∂P, ζv ω = ⊤ := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨Wv, ζv, hcfv⟩ := BR4aPath.exists_isCenteredCounterflowDriver_recField h12p h13 hκ hb hh v
  have e : (fun ω => BR4aPath.recField v (h ω)) = fun ω => affField (-v) one_pos (h ω) := by
    funext ω
    exact Lv.flowField_eq_affField v (h ω)
  rw [e] at hcfv
  refine ⟨Wv, ζv, hcfv, ?_⟩
  have hamb := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ'
  have hbB := isPiecewiseConstantBoundaryData_affData one_pos (m := -v) hb
  have hhT := IsGFFWithBoundaryData.affine_finset (m := -v) one_pos hh
  have hdata : ∀ y, affData 1 (-v) b y = b (y + v) := fun y => by
    simp only [affData]; congr 1; ring
  have hJ : ∀ y, y ∉ affJumps 1 (-v) J → y + v ∉ J := fun y hy h' => hy ((mem_affJumps one_ne_zero).2 (by
    rw [show (y - -v) / 1 = y + v by ring]; exact h'))
  refine ae_lifetime_top_of_bounds hκ hbB hhT hcfv (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
  · rw [hdata]
    rcases lt_or_ge (y + v) 0 with h1 | h1
    · exact hamb.1 _ h1 (hJ y hyJ)
    · have hl := Sec4.sleLambda_pos hκ
      rcases h1.lt_or_eq with h2 | h2
      · have := le_of_low_arc hb hlow0 hlow h2 (by linarith) (hJ y hyJ)
        linarith
      · have h0 : (0 : ℝ) ∉ J := h2 ▸ hJ y hyJ
        rw [← h2, ← Exist.StagedLaw.rightLim_eq_of_notMem hb h0]
        linarith
  · rw [hdata]
    exact hamb.2 _ (by linarith) (hJ y hyJ)

end InteractingSLE.Theorem14.SB.Lf
