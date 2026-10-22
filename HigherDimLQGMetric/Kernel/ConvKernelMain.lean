import HigherDimLQGMetric.Kernel.ConvKernelFourierDecay
import HigherDimLQGMetric.Kernel.ConvKernelInversion

/-!
# The convolution kernel of [1]

The symbol is integrable with moments and sufficiently many integrable derivatives. Its
inverse transform is smooth, real, radial, integrable, and has unit mass. Integration by parts
gives the stated spatial decay, and Fourier inversion identifies its Fourier transform.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped FourierTransform
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **L1c** ([1] Rem. 1.1, Lemmas 2.9–2.10, the parts used later): `K` is smooth, integrable,
radial, `∫ K = 1`, `K̂ = kernelSymbol`, and `|K(x)| ≤ C (1+|x|)^{-(d+1)}` ([1] claims
`(1+|x|)^{1-2d}`, also true; `d+1` is all that is used). -/
def L1c_convKernel : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ Integrable (convKernel κ) ∧
    (∫ x, convKernel κ x = 1) ∧ (∀ x y : Rd d, ‖x‖ = ‖y‖ → convKernel κ x = convKernel κ y) ∧
    (∃ C : ℝ, ∀ x : Rd d, |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) ∧
    𝓕 (fun x : Rd d => (convKernel κ x : ℂ)) = fun ζ => (kernelSymbol κ ζ : ℂ)

/-- The complete kernel result of packet L1c. -/
theorem l1c_convKernel : L1c_convKernel := by
  intro d hd κ hκ
  have hdp : 0 < d := by omega
  have hK : Integrable (convKernel κ) := integrable_convKernel hd hκ
  exact ⟨convKernel_contDiff hdp hκ, hK,
    convKernel_integral_eq_one hdp hκ hK,
    fun _ _ h => convKernel_radial h,
    convKernel_decay hd hκ,
    convKernel_fourier_eq hdp hκ hK⟩

/-- The exact statement of the frozen sanity anchor, proved for its later seal. -/
theorem convKernel_smooth_integral_proof :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 := by
  intro d hd κ hκ
  have hdp : 0 < d := by omega
  have hK : Integrable (convKernel κ) := integrable_convKernel hd hκ
  exact ⟨convKernel_contDiff hdp hκ, convKernel_integral_eq_one hdp hκ hK⟩

end HigherDimLQGMetric
