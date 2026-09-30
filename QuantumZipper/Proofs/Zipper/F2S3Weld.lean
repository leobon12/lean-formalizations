import QuantumZipper.Proofs.Zipper.F2Step3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F2 step (3): welding invariance `Step3WeldStmt` from the capture-time parametrization

Theorem 1.3, node F2, step (3), input `F2.Step3WeldStmt` (`F2Step3.lean`). Source: Sheffield,
*Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 (pp. 70–72): if the quantum lengths
of the two sides of `η[0,s]` agree for all `s ≤ t`, the welding of the two sides of `η[0,t]`
preserves quantum length, so "the density is the same on both sides".

## Reduction

Fix `t`, write `ν = ν_{x_t}`, `F = F_t = invBdry W t`, `a = O⁻_t`, `b = O⁺_t`. Every point `w` of
`[a, 0]` (resp. `[0, b]`) is sent by `F` to the point `η(φ⁻(w))` (resp. `η(φ⁺(w))`) of the curve,
where `φ^±(w) ∈ [0,t]` is the capture time; and the lengths of the two sides of `η[0,s]` are
`ν{w ∈ [a,0] : φ⁻(w) ≤ s}` and `ν{w ∈ [0,b] : φ⁺(w) ≤ s}` (B5 for the field `x`, at all
`s ≤ t`). These two facts form the input `Step3WeldParamStmt`. Given them, if the lengths agree at
all `s ≤ t`, the image measures `φ⁻_*(ν|[a,0])` and `φ⁺_*(ν|[0,b])` on `ℝ` (finite: `ν` is locally
finite) agree on every `Iic s`, hence are equal (`Measure.ext_of_Iic`), and
`∫_{[a,0]} g∘F dν = ∫ g∘η d(φ⁻_*ν) = ∫ g∘η d(φ⁺_*ν) = ∫_{[0,b]} g∘F dν`
(`step3Weld_of_param`). Own elementary measure-theoretic argument (uniqueness of a finite measure
on `ℝ` from its distribution function); the paper states the welding invariance without proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- On `A`, where `φ ∈ [0,t]`, the sublevel sets of `φ` are empty below `0` and constant above
`t`. -/
theorem inter_preimage_Iic_min {φ : ℝ → ℝ} {A : Set ℝ} {t : ℝ}
    (h : ∀ w ∈ A, φ w ∈ Icc 0 t) (s : ℝ) :
    A ∩ φ ⁻¹' Iic s = A ∩ φ ⁻¹' Iic (min s t) := by
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_Iic, le_min_iff]
  constructor
  · rintro ⟨hw, hs⟩; exact ⟨hw, hs, (h w hw).2⟩
  · rintro ⟨hw, hs, -⟩; exact ⟨hw, hs⟩

theorem inter_preimage_Iic_neg {φ : ℝ → ℝ} {A : Set ℝ} {t : ℝ}
    (h : ∀ w ∈ A, φ w ∈ Icc 0 t) {s : ℝ} (hs : s < 0) : A ∩ φ ⁻¹' Iic s = ∅ := by
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_and,
    not_le]
  exact fun hw => hs.trans_le (h w hw).1

end F2
end QuantumZipper
