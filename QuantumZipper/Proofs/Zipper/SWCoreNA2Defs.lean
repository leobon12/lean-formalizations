import QuantumZipper.Proofs.Zipper.SWCoreVAImg
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.Thm18.G1RCCircle

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2: finite-parameter families of pushed and image circles (definitions)

Task SWC-NA (`handoff/SW-CORE.md` §5; decision D59, the primed core over all radii in each dyadic
block). A finite-parameter family of maps `F q` (`q ∈ ℝⁿ`, the parameter may contain map
parameters, the centre and the radius factor `a(q) ∈ [1,2]`) gives, at dyadic scale `k`, the
pushed circles `(F q)_* fc(c q, a(q) 2^{-k})` and the image circles
`fc(F q (c q), a(q) 2^{-k} ‖(F q)'(c q)‖)`, both as `circM`-pushforwards of explicit
parametrizations (`swcPhiPush`, `swcPhiRound`), in the form used by the Kolmogorov toolkit
`Thm18Asm.G1RC.FamilyBounds`. Definitions only.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- The pushed circle parametrization: `θ ↦ F q (c q + a(q) 2^{-k} e^{iθ})`. -/
def swcPhiPush {n : ℕ} (F : (Fin n → ℝ) → ℂ → ℂ) (c : (Fin n → ℝ) → ℂ) (a : (Fin n → ℝ) → ℝ)
    (k : ℕ) (q : Fin n → ℝ) (θ : ℝ) : ℂ :=
  F q (circleMap (c q) (a q * radius k) θ)

/-- The image circle parametrization: `θ ↦ F q (c q) + a(q) 2^{-k} ‖(F q)'(c q)‖ e^{iθ}`. -/
def swcPhiRound {n : ℕ} (F : (Fin n → ℝ) → ℂ → ℂ) (c : (Fin n → ℝ) → ℂ) (a : (Fin n → ℝ) → ℝ)
    (k : ℕ) (q : Fin n → ℝ) (θ : ℝ) : ℂ :=
  circleMap (F q (c q)) (a q * radius k * ‖deriv (F q) (c q)‖) θ

end SWCore
end QuantumZipper
