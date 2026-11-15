/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Prop74
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# Flow lines of the two-height data of Proposition 7.4 are two-seed couplings

Packet PROVE-AUX97-B. Source: Proposition 7.4 (`source/spec/p241-288.md` L56–L64, p. 244) and Proposition 7.3
(L34–L48, pp. 242–243: "The flow lines with constant boundary heights on the two real half-lines are consequently
well-defined path-valued functions of their fields in the original coupling class").

The reference objects of Proposition 7.4 and of Aux. lemma 97 are flow lines from `0` of a GFF with the data
`prop74Data a b` (`−a` on `ℝ₋`, `b` on `ℝ₊`). The two-seed results of the project (Proposition 7.3, Lemma 7.1's trace
reference, the `LP` inputs, the local extension of Aux. lemma 55) are stated for optional hull couplings of the two-seed
word `LP.twoSeedXL`, `LP.twoSeedXR` (one mark at `0⁻`, one at `0⁺`). This file identifies the two:

* `leftLim_prop74Data`, `rightLim_prop74Data`, `filter_lt_jumpSet_prop74Data`, `filter_gt_jumpSet_prop74Data`;
* `flowLineNL_prop74Data`, `flowLineNR_prop74Data`: the flow-line word from `0` has one mark on each side;
* `flowLineXL_prop74Data`, `flowLineXR_prop74Data`, `flowLineRhoL_prop74Data`, `flowLineRhoR_prop74Data`: its
  positions are `0` and its weights are `ρ^L = (a − θχ)/λ − 1`, `ρ^R = (b + θχ)/λ − 1` (the weights named in
  Proposition 7.4's two conditional laws);
* **`isFlowLine_prop74Data_iff`**: `IsFlowLine κ (prop74Data a b) {0} 0 θ P X η ζ` holds iff some translate
  `X + θχ` carries an optional hull coupling of the two-seed word with these weights whose trace is `η`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

theorem leftLim_prop74Data (a b : ℝ) : leftLim (prop74Data a b) 0 = -a :=
  Sec4.leftLim_eq_of_forall (a := -1) (by norm_num) fun t ht => by
    simp only [prop74Data, show t < 0 from ht.2, ↓reduceIte]

theorem rightLim_prop74Data (a b : ℝ) : rightLim (prop74Data a b) 0 = b :=
  Sec4.rightLim_eq_of_forall (a := 1) one_pos fun t ht => by
    simp only [prop74Data, not_lt.2 (le_of_lt (show (0 : ℝ) < t from ht.1)), ↓reduceIte]

/-- The data `prop74Data a b` has no genuine jump left of `0`. -/
theorem filter_lt_jumpSet_prop74Data (a b : ℝ) : (jumpSet (prop74Data a b) {0}).filter (· < 0) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun y hy => ?_
  have hy0 : y = 0 := Finset.mem_singleton.1 (Finset.mem_filter.1 hy).1
  rw [hy0]
  exact lt_irrefl 0

/-- The data `prop74Data a b` has no genuine jump right of `0`. -/
theorem filter_gt_jumpSet_prop74Data (a b : ℝ) : (jumpSet (prop74Data a b) {0}).filter (0 < ·) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun y hy => ?_
  have hy0 : y = 0 := Finset.mem_singleton.1 (Finset.mem_filter.1 hy).1
  rw [hy0]
  exact lt_irrefl 0

/-- The flow-line word of `prop74Data a b` from `0` has one left mark (the seed mark `0⁻`). -/
theorem flowLineNL_prop74Data (a b : ℝ) : flowLineNL (prop74Data a b) {0} 0 = 1 := by
  unfold flowLineNL
  rw [filter_lt_jumpSet_prop74Data, Finset.card_empty]

/-- The flow-line word of `prop74Data a b` from `0` has one right mark (the seed mark `0⁺`). -/
theorem flowLineNR_prop74Data (a b : ℝ) : flowLineNR (prop74Data a b) {0} 0 = 1 := by
  unfold flowLineNR
  rw [filter_gt_jumpSet_prop74Data, Finset.card_empty]

/-- Every index of a `Fin` type of size `1` is a cast of `0`. -/
private theorem eq_cast_zero {n : ℕ} (e : 1 = n) (j : Fin n) : j = Fin.cast e 0 := by
  subst e
  exact Subsingleton.elim _ _

theorem flowLineXL_prop74Data (a b : ℝ) (j : Fin (flowLineNL (prop74Data a b) {0} 0)) :
    flowLineXL (prop74Data a b) {0} 0 j = 0 := by
  rw [eq_cast_zero (flowLineNL_prop74Data a b).symm j]
  rfl

theorem flowLineXR_prop74Data (a b : ℝ) (j : Fin (flowLineNR (prop74Data a b) {0} 0)) :
    flowLineXR (prop74Data a b) {0} 0 j = 0 := by
  rw [eq_cast_zero (flowLineNR_prop74Data a b).symm j]
  rfl

/-- The left seed weight of the angle-`θ` flow line of `prop74Data a b` from `0` is `(a − θχ)/λ − 1`. -/
theorem flowLineRhoL_prop74Data (κ a b θ : ℝ) (j : Fin (flowLineNL (prop74Data a b) {0} 0)) :
    flowLineRhoL κ (prop74Data a b) {0} 0 θ j = (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  rw [eq_cast_zero (flowLineNL_prop74Data a b).symm j]
  show -(leftLim (prop74Data a b) 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 = _
  rw [leftLim_prop74Data, neg_add, neg_neg, ← sub_eq_add_neg]

/-- The right seed weight of the angle-`θ` flow line of `prop74Data a b` from `0` is `(b + θχ)/λ − 1`. -/
theorem flowLineRhoR_prop74Data (κ a b θ : ℝ) (j : Fin (flowLineNR (prop74Data a b) {0} 0)) :
    flowLineRhoR κ (prop74Data a b) {0} 0 θ j = (b + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  rw [eq_cast_zero (flowLineNR_prop74Data a b).symm j]
  show (rightLim (prop74Data a b) 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 = _
  rw [rightLim_prop74Data]

/-- **Flow lines of the two-height data are two-seed couplings.** The angle-`θ` flow line from `0` of a field `X` with
data `prop74Data a b` is exactly the trace of an optional hull coupling of a translate `X + θχ` with the two-seed word
`SLE_κ((a − θχ)/λ − 1; (b + θχ)/λ − 1)`. -/
theorem isFlowLine_prop74Data_iff {κ a b θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} :
    IsFlowLine κ (prop74Data a b) {0} 0 θ P X η ζ ↔
      ∃ (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
        (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
        (∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (X ω) (h' ω)) ∧
        IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR
          (fun _ => (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
          (fun _ => (b + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) P 𝓕 W VL VR B ζ h' ∧
        ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - ((0 : ℝ) : ℂ)) := by
  have eL := flowLineNL_prop74Data a b
  have eR := flowLineNR_prop74Data a b
  constructor
  · rintro ⟨h', 𝓕, W, VL, VR, B, htr, hc, htrace⟩
    have hc' := Supp9.isOptionalHullCoupling_comp_cast eL.symm eR.symm hc
    have e1 : (fun i : Fin 1 => flowLineXL (prop74Data a b) {0} 0 (Fin.cast eL.symm i)) = LP.twoSeedXL :=
      funext fun i => flowLineXL_prop74Data a b _
    have e2 : (fun i : Fin 1 => flowLineXR (prop74Data a b) {0} 0 (Fin.cast eR.symm i)) = LP.twoSeedXR :=
      funext fun i => flowLineXR_prop74Data a b _
    have e3 : (fun i : Fin 1 => flowLineRhoL κ (prop74Data a b) {0} 0 θ (Fin.cast eL.symm i)) =
        fun _ => (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1 :=
      funext fun i => flowLineRhoL_prop74Data κ a b θ _
    have e4 : (fun i : Fin 1 => flowLineRhoR κ (prop74Data a b) {0} 0 θ (Fin.cast eR.symm i)) =
        fun _ => (b + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 :=
      funext fun i => flowLineRhoR_prop74Data κ a b θ _
    rw [e1, e2, e3, e4] at hc'
    exact ⟨h', 𝓕, W, _, _, B, htr, hc', htrace⟩
  · rintro ⟨h', 𝓕, W, VL, VR, B, htr, hc, htrace⟩
    have hc' := Supp9.isOptionalHullCoupling_comp_cast eL eR hc
    have e1 : (fun i : Fin (flowLineNL (prop74Data a b) {0} 0) => LP.twoSeedXL (Fin.cast eL i)) =
        flowLineXL (prop74Data a b) {0} 0 :=
      funext fun i => (flowLineXL_prop74Data a b i).symm
    have e2 : (fun i : Fin (flowLineNR (prop74Data a b) {0} 0) => LP.twoSeedXR (Fin.cast eR i)) =
        flowLineXR (prop74Data a b) {0} 0 :=
      funext fun i => (flowLineXR_prop74Data a b i).symm
    have e3 : (fun _ : Fin (flowLineNL (prop74Data a b) {0} 0) =>
        (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1) = flowLineRhoL κ (prop74Data a b) {0} 0 θ :=
      funext fun i => (flowLineRhoL_prop74Data κ a b θ i).symm
    have e4 : (fun _ : Fin (flowLineNR (prop74Data a b) {0} 0) =>
        (b + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) = flowLineRhoR κ (prop74Data a b) {0} 0 θ :=
      funext fun i => (flowLineRhoR_prop74Data κ a b θ i).symm
    rw [e1, e2, e3, e4] at hc'
    exact ⟨h', 𝓕, W, _, _, B, htr, hc', htrace⟩

end Sec7

end InteractingSLE
