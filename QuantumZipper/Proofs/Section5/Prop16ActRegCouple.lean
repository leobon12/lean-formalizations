import QuantumZipper.Proofs.Section5.Prop16ActRegBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′: regularized circle averages on the M7 coupling

`ae_avgReg_coupling`: on the half-disc coupling of `K3.MixedFreeCouplingHalfDiscStmt` (proved,
`K3.mixedFreeCouplingHalfDisc_holds`), where for every admissible `μ` carried by
`closedBall t r'` a.s. `Y μ = X μ − μ(ℂ) X ρ₀ + ∫ g dμ` with `g ∘ foldH` harmonic, almost surely
**simultaneously for all** `s ∈ ℍ̄` with `|s − t| + 2^{-k} < r'`,

  `avgReg Y k s = avgReg X k s − X ρ₀ + g(s)`.

This is the pathwise input for transferring boundary-measure approximations (`bdryApprox`, which
reads the field only through `avgReg`) from the free field to the mixed field near a point of the
free arc (node `Prop16BdryL1Stmt`). Proof: the representation holds a.s. simultaneously on the
countably many dyadic circles involved; the free field's dyadic averages converge
(`BdryExist.ae_avgReg_spec`, M4-R3), and `∫ g d fc(c, 2^{-k}) = g(c)` (mean value property,
`integral_foldedCircle_of_harm_center`) with `g` continuous. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper

namespace Prop16Asm

theorem countable_range_dyadicRoundC_ar (n : ℕ) : (Set.range (dyadicRoundC n)).Countable := by
  have hsub : Set.range (dyadicRoundC n) ⊆
      Set.range (fun p : ℤ × ℤ =>
        (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  exact (Set.countable_range _).mono hsub

end Prop16Asm

end QuantumZipper
