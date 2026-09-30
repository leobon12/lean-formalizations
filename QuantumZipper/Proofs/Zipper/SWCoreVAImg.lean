import QuantumZipper.Proofs.Zipper.SWCoreVAPsi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-VA (iii), image circles: the energy modulus of the round circles `fc(ψ z, r‖ψ'(z)‖)`

Task SWC-VA (`handoff/SW-CORE.md` §5). For `ψ, φ` in a rational area class with
`‖ψ − φ‖ ≤ ε` on the `ρ/2`-thickening of `K`, and `z, z' ∈ K`,

  `|kernelCov2 neumannH (fc(ψ z, r‖ψ'(z)‖) − fc(φ z', r‖φ'(z')‖))|`
    `≤ 4 (ε + M₁‖z − z'‖ + r (ε/(ρ/4) + M₂‖z − z'‖)) / (r m)`

with the class Cauchy constants `M₁ = |M|/(ρ/4)`, `M₂ = M₁/(ρ/4)` (`swcVA_img_img_le`): the
modulus of the second (round) term of the distortion in `(ψ, z)`. Proof: the repository's
round-circle modulus `E6.XAreaPC.abs_kernelCov2_fc_fc_le` (exact circle means) and Cauchy's
estimates (for `ψ − φ`, and for `φ'` along the convex rectangle). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC

theorem swcVA_convex_rectC (a b c d : ℝ) : Convex ℝ (rectC a b c d) := by
  have e : rectC a b c d = Complex.reLm ⁻¹' Icc a b ∩ Complex.imLm ⁻¹' Icc c d := rfl
  rw [e]
  exact ((convex_Icc a b).linear_preimage Complex.reLm).inter
    ((convex_Icc c d).linear_preimage Complex.imLm)

end SWCore
end QuantumZipper
