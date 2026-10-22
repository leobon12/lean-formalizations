import HigherDimLFPP.Frozen.Rd
import HigherDimLFPP.Frozen.E1
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Frozen definition: `kernelSymbol`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 85–90 ("the explicit convolution kernels in [1, Remark 1.1]"), [1] Remark 1.1 (TeX l. 201–211):
`K̂(ζ) = (2π^{d/2}/Γ(d/2) ∫_{|ζ|}^∞ t^{d-1} |𝔎̂(t)|² dt)^{1/2}`, with `𝔎̂(t) = 𝔎̂(t e₁)` (𝔎 radial),
`2π^{d/2}/Γ(d/2) = |S^{d-1}|`, and mathlib's unitary convention `𝓕 f(ζ) = ∫ e^{-2πi⟨x,ζ⟩} f(x) dx`
(the convention under which `∫ K = K̂(0) = ‖𝔎‖₂ = 1`, as [1] states).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- `K̂(ζ) = (2π^{d/2}/Γ(d/2) ∫_{|ζ|}^∞ t^{d-1} |𝔎̂(t e₁)|² dt)^{1/2}` ([1, Remark 1.1]). -/
def kernelSymbol {d : ℕ} (κ : Rd d → ℝ) (ζ : Rd d) : ℝ :=
  Real.sqrt ((2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
    ∫ t in Ioi ‖ζ‖, t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d)‖ ^ 2)

end HigherDimLQGMetric
