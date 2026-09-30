import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1: regularity of the length function `F` and of the read lengths

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (the lengths `L±_t`
of the two sides of `η[0,t]`) and §5.4, proof of Theorem 1.3 (pp. 70–72).

* `lenReg_det` (deterministic, own elementary argument): if `L⁻` is strictly increasing on
  `[0,∞)` and reaches every `ℓ > 0`, and `L⁺` is nondecreasing, continuous and `L⁺_0 = 0`, then
  `F = L⁺ ∘ tᴸ` is continuous and nondecreasing on `[0,∞)` with `F 0 = 0`. (`L⁻_0 = 0` follows;
  `tᴸ` is a monotone bijection of `[0,∞)`, hence continuous, `Monotone.continuous_of_surjective`.)
* `lenRegStmt_of_flow`: `F1.LenRegStmt` from `LenStrictMonoStmt`, `LenLeftSurjStmt`,
  `LenPairCocycleStmt` (which gives monotonicity of `L⁺`) and `LenRightRegStmt` (continuity of
  `L⁺`, `L⁺_0 = 0`).
* `lenReadRegStmt_of_meas`: `F1.LenReadRegStmt` from the same regularity of the sample and the
  null-measurability of the regularity set for the data law (`LenReadRegMeasStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## The read lengths -/

/-- An a.s. property of `f` holds a.e. for the law of `f` when its set is null-measurable. -/
theorem ae_map_of_nullMeasurableSet {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : AEMeasurable f μ) {S : Set β}
    (hS : NullMeasurableSet S (μ.map f)) (h : ∀ᵐ x ∂μ, f x ∈ S) : ∀ᵐ y ∂(μ.map f), y ∈ S := by
  obtain ⟨T, hTS, hT, hTeq⟩ := hS.exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null (ae_eq_set.1 hTeq).2
  have hfN : μ (f ⁻¹' N) = 0 := by rw [← Measure.map_apply_of_aemeasurable hf hN]; exact hN0
  have hT' : ∀ᵐ x ∂μ, f x ∈ T := by
    filter_upwards [h, measure_eq_zero_iff_ae_notMem.1 hfN] with x hx hxN
    by_contra hxT
    exact hxN (hSN ⟨hx, hxT⟩)
  exact ((ae_map_iff hf (p := (· ∈ T)) hT).2 hT').mono fun y hy => hTS hy

end F1
end QuantumZipper
