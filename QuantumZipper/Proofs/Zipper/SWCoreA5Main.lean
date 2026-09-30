import QuantumZipper.Proofs.Zipper.SWCoreA5Dens
import QuantumZipper.Proofs.Zipper.SWCoreA5Unif
import QuantumZipper.Proofs.Zipper.SWCoreA5Pull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5 (4): uniform area transport for nonnegative test functions

Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4 (pp. 11–13): the change of coordinates
`w = ψ(z)` turns the pushed approximation `∫ f dμ^{x∘ψ+Q log|ψ'|}_k` into the variable-scale
integral `∫ f∘ψ⁻¹(w) μ^x_{2^{-k}|ψ'(ψ⁻¹w)|}(dw)` up to the factor `e^{γ err}` (distortion core),
and the variable-scale integrals converge to `∫ f∘ψ⁻¹ dμ` uniformly over the class
(`unifWin`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {x : FieldSample}

theorem rectC_subset_H {a b c d : ℝ} (hc : 0 < c) : rectC a b c d ⊆ H :=
  fun z hz => lt_of_lt_of_le hc hz.2.1

theorem measurableSet_rectC (a b c d : ℝ) : MeasurableSet (rectC a b c d) :=
  (measurableSet_Icc.preimage Complex.measurable_re).inter
    (measurableSet_Icc.preimage Complex.measurable_im)

/-- **Change of variables** for the pushed density. -/
theorem lintegral_pushDens_eq {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) {f : ℂ → ℝ}
    (hfK : tsupport f ⊆ interior (rectC a b c d)) (k : ℕ) :
    ∫⁻ z in H, ENNReal.ofReal (f z) *
        ENNReal.ofReal (‖deriv ψ z‖ ^ 2 * areaDens γ x (radius k * ‖deriv ψ z‖) (ψ z)) =
      vsInt γ x (pullTest ψ (rectC a b c d) f) (pullScale ψ (rectC a b c d)) k := by
  set K := rectC a b c d with hKdef
  have hKH : K ⊆ H := rectC_subset_H hc
  have hinj : InjOn ψ K := hψ.2.1.mono (self_subset_thickening hρ _)
  have hKm : MeasurableSet K := measurableSet_rectC a b c d
  have hfz : ∀ z, f z ≠ 0 → z ∈ K := fun z h =>
    interior_subset (hfK (subset_tsupport f h))
  have hsupp1 : (support fun z => ENNReal.ofReal (f z) *
      ENNReal.ofReal (‖deriv ψ z‖ ^ 2 * areaDens γ x (radius k * ‖deriv ψ z‖) (ψ z))) ⊆ K := by
    intro z hz
    refine hfz z fun h => hz ?_
    simp [h]
  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (pullTest ψ K f w) *
    ENNReal.ofReal (areaDens γ x (radius k * pullScale ψ K w) w) with hG
  have hsupp2 : support G ⊆ ψ '' K := by
    intro w hw
    by_contra h
    apply hw
    simp [hG, pullTest, h]
  calc _ = ∫⁻ z in K, ENNReal.ofReal (f z) *
        ENNReal.ofReal (‖deriv ψ z‖ ^ 2 * areaDens γ x (radius k * ‖deriv ψ z‖) (ψ z)) := by
        rw [setLIntegral_eq_of_support_subset (hsupp1.trans hKH),
          setLIntegral_eq_of_support_subset hsupp1]
    _ = ∫⁻ z in K, ENNReal.ofReal (‖deriv ψ z‖ ^ 2) * G (ψ z) := by
        refine setLIntegral_congr_fun hKm fun z hz => ?_
        have h1 : Function.invFunOn ψ K (ψ z) = z := swA5_invFunOn_image hρ hψ hz
        have h2 : pullTest ψ K f (ψ z) = f z := swA5_pullTest_image hρ hψ hz f
        have h3 : pullScale ψ K (ψ z) = ‖deriv ψ z‖ := by
          simp only [pullScale, h1]
        simp only [hG, h2, h3]
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        ring
    _ = ∫⁻ w in ψ '' K, G w := lintegral_pull hρ hψ G
    _ = vsInt γ x (pullTest ψ K f) (pullScale ψ K) k := by
        have hψK : ψ '' K ⊆ H := by
          rintro _ ⟨z, hz, rfl⟩
          exact lt_of_lt_of_le hρ (hψ.2.2.1 z (self_subset_thickening hρ _ hz)).2
        rw [vsInt, setLIntegral_eq_of_support_subset hsupp2,
          setLIntegral_eq_of_support_subset (hsupp2.trans hψK)]

end SWCore
end QuantumZipper
