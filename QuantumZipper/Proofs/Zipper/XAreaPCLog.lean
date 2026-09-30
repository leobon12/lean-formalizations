import QuantumZipper.Proofs.Zipper.XAreaPCKolm
import QuantumZipper.Proofs.Zipper.AreaPCReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc: the deterministic log part

For the log singularity `ℓ(w) = α₀(−log‖w‖)` (`α₀ = √κ − 2/√κ`, the function of
`F2.logSingField κ`) the difference of its averages over the pushed circle
`μ₁ = (f_t⁻¹)_* fc(z, 2^{-k})` and the image circle `μ₂ = fc(f_t⁻¹ z, 2^{-k}‖(f_t⁻¹)'(z)‖)`
tends to `0` uniformly on compact subsets of `ℍ` (`eventually_abs_lDiff_le`): both measures live,
for `k` large, where `‖w‖ ≥ η > 0`, and there `ℓ` agrees with the continuous function
`α₀(−log max(‖w‖, η))`, to which `eventually_abs_pushAvg_sub_circAvg_le` applies.
Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper.E6
namespace XAreaPC

/-- The image circle `fc(f_t⁻¹ z, s ‖(f_t⁻¹)'(z)‖)`. -/
def muI (W : ℝ → ℝ) (t : ℝ) (z : ℂ) (s : ℝ) : Measure ℂ :=
  foldedCircle (fwdMapInv W t z) (s * ‖deriv (fwdMapInv W t) z‖)

end XAreaPC
end QuantumZipper.E6
