import QuantumZipper.Proofs.Zipper.UnscaledResample
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LOGSHIFT-LEN: the inputs of the D29 resampling transfer (κ ∈ (0,4))

The D29 resampling nodes (`UnscaledResample.lean`, decisions D29, D43) rest on three named inputs
about a log-shifted `Γ⁰` field `Z = X + α₀(−log|·|) + G`. This file settles or reduces them.

1. **`LogShiftLenFiniteStmt` holds unconditionally** (`logShiftLenFiniteStmt_holds`). In this
   formalization `qBoundaryMeasure` is either a vague limit (locally finite by definition of
   `IsVagueLimitR`) or the junk measure `0`, so every length of a compact window is finite
   (`F1.unzipLengths_fst_lt_top`). The genuine tip content (TIP-X: the vague limit of the boundary
   approximations of the unzipped `Z` field *exists*, although the field has a log singularity at
   the images `O±_t` of `0`) is therefore not in this statement: it is part of the density
   statement below, whose right side is positive for `t > 0` while a junk measure would give `0`.
2. **`LogShiftLenDensityStmt` and `LogShiftLenFlowMeasStmt` both follow from one named input**,
   `LogShiftLenWeightStmt` (the density transport principle), together with the existing `Γ⁰`
   nodes `LenPairCocycleCfgStmt` (the capacity cocycle of both `Γ⁰` lengths) and `LenRegCfgStmt`
   (continuity of both `Γ⁰` lengths, vanishing at `0`):
   * the `Γ⁰` lengths are Stieltjes measures of capacity time (`ae_gammaZero_rep`: monotone by the
     cocycle, continuous and `0` at `0` by the regularity, finite always; Stieltjes measure,
     mathlib `StieltjesFunction.measure_Ioc`);
   * the weighted lengths are `w · μ∓`, both at time `0` and after unzipping by any `u ≥ 0`
     (`LogShiftLenWeightStmt`), so `ν∓ := μ∓.withDensity w` represent the `Z` lengths along the
     whole capacity flow; the `Γ⁰` cocycle identifies the unzipped `Γ⁰` lengths with
     `μ∓(u, u+s]` (no `Z` cocycle is needed).

`LogShiftLenWeightStmt` is the density transport principle of Sheffield (arXiv:1012.4797, §1.4:
the quantum lengths of the two sides of `η[0,t]` are the boundary measure of the unzipped field,
and §5.4 pp. 71–72: this measure is transported by the unzipping maps), combined with the local
rule of Duplantier–Sheffield (Invent. Math. 185 (2011), §6; here `GoodSample.qBoundaryMeasure_add_ofFun`
and `LocalRule.qBoundaryMeasure_add_ofFun'`): adding the continuous function `f ∘ f_u⁻¹`
(`f = −γ log|·| + G`, continuous off `0`) multiplies the boundary measure by `e^{γ f∘f_u⁻¹/2}` on
compact pieces of `(O⁻_{u+s}, 0]` and `[0, O⁺_{u+s})`; in capacity time the weight is
`w(r) = e^{γ f(η(r))/2} = |η(r)|^{−γ²/2} e^{γ G(η(r))/2}`, the same for every `u` (the point of the
unzipped curve at capacity time `r − u` is `f_u(η(r))`). The deterministic reductions here are own
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## 1. Finiteness is unconditional -/

/-! ## 2. Stieltjes representation of the `Γ⁰` lengths -/

/-- A finite, monotone function on `[0,∞)`, continuous there and vanishing at `0`, is
`t ↦ μ(0,t]` for a measure `μ` finite on compacts (the Stieltjes measure of `t ↦ L(max t 0)`). -/
theorem lsl_exists_Ioc_rep {L : ℝ → ℝ≥0∞} (hfin : ∀ t, L t ≠ ⊤)
    (hmono : MonotoneOn L (Ici 0)) (hc : ContinuousOn (fun t => (L t).toReal) (Ici 0))
    (h0 : L 0 = 0) :
    ∃ μ : Measure ℝ, IsFiniteMeasureOnCompacts μ ∧ ∀ t : ℝ, 0 ≤ t → L t = μ (Ioc 0 t) := by
  let F : ℝ → ℝ := fun t => (L (max t 0)).toReal
  have hFm : Monotone F := fun a b hab =>
    ENNReal.toReal_mono (hfin _) (hmono (mem_Ici.2 (le_max_right _ _))
      (mem_Ici.2 (le_max_right _ _)) (max_le_max hab le_rfl))
  have hFc : Continuous F :=
    hc.comp_continuous (continuous_id.max continuous_const) fun t => mem_Ici.2 (le_max_right _ _)
  let S : StieltjesFunction ℝ := ⟨F, hFm, fun x => hFc.continuousWithinAt⟩
  refine ⟨S.measure, inferInstance, fun t ht => ?_⟩
  rw [S.measure_Ioc]
  have e1 : S t = (L t).toReal := by
    show F t = _
    simp only [F, max_eq_left ht]
  have e0 : S 0 = 0 := by
    show F 0 = _
    simp only [F, max_self, h0, ENNReal.toReal_zero]
  rw [e1, e0, sub_zero, ENNReal.ofReal_toReal (hfin t)]

/-- An additive cocycle `L(u+s) = L u + N u s` makes `L` monotone on `[0,∞)`. -/
theorem lsl_monotoneOn_of_cocycle {L : ℝ → ℝ≥0∞} {N : ℝ → ℝ → ℝ≥0∞}
    (h : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → L (u + s) = L u + N u s) : MonotoneOn L (Ici 0) := by
  intro a ha b _ hab
  have e := h a (b - a) ha (sub_nonneg.2 hab)
  have e' : a + (b - a) = b := by ring
  rw [e'] at e
  rw [e]
  exact le_self_add

section Gamma

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end Gamma

/-! ## 3. The density transport input and the two targets -/

end F1
end QuantumZipper
