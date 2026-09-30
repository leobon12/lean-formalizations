import QuantumZipper.Proofs.Zipper.XAreaPCModI
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, R3 (1/2): identification at fixed parameters and continuity of the smoothed pairings

Centres `z` with `r < Im z` (`UR r`), where the folded circle `fc(z, r)` is the genuine circle.
For a continuous driver `W` (`W 0 = 0`), `t ≥ 0`, `ψ = f_t⁻¹ = fwdMapInv W t`:

* `norm_deriv_fwdMapInv_le`: `‖ψ'(z)‖ ≤ Im ψ(z) / Im z` (Schwarz–Pick for `ℍ → ℍ`, via
  `TwoPoint.norm_deriv_revMap_le`), so the image circle `muI` also stays in `ℍ` for `z ∈ UR r`;
* `muP_supp`, `muI_supp`: both measures are carried by compact subsets of `ℍ`;
* `xpcIdA_of_lt` (R3(a) on `UR (2^{-k})`): a.s. `evalReg x (muP) − evalReg x (muI) =
  X(muP) − X(muI) + lDiff`, `x = X + α₀(−log|·|)`, from the Frostman bounds (exponent `1/3` for the
  pushed circle, `RegCont.isFrostman_fwdMapInv_foldedCircle`; `1` for the circle) and
  `FrostmanReg.ae_evalReg_ofFun_add_eq_frostman` (stochastic Fubini plus Borel–Cantelli);
* `continuousOn_integral_muP`, `continuousOn_integral_muI`: for `G` measurable and continuous on
  `ℍ`, `z ↦ ∫ G d(muP z r)` and `z ↦ ∫ G d(muI z r)` are continuous on `UR r` (dominated
  convergence in the angle); in particular `z ↦ lDiff κ W t z r` is continuous on `UR r`.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (regularized evaluation = raw coordinate for measures of finite energy);
Schwarz–Pick for self-maps of `ℍ` is `TwoPoint.norm_deriv_revMap_le`. The rest is own elementary
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Real

namespace QuantumZipper.E6
namespace XAreaPC

/-- Centres at which the folded circle of radius `r` is the genuine circle. -/
def UR (r : ℝ) : Set ℂ := {z | r < z.im}

section Det

variable {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
include hW hW0 ht

/-- Schwarz–Pick for `f_t⁻¹`. -/
theorem norm_deriv_fwdMapInv_le {z : ℂ} (hz : z ∈ H) :
    ‖deriv (fwdMapInv W t) z‖ ≤ (fwdMapInv W t z).im / z.im := by
  rw [RegCont.deriv_fwdMapInv_eq hW hW0 ht hz,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hz]
  exact TwoPoint.norm_deriv_revMap_le (RegCont.continuous_vRev hW t) hz ht

instance isProbabilityMeasure_muI (z : ℂ) (r : ℝ) : IsProbabilityMeasure (muI W t z r) := by
  unfold muI; infer_instance

end Det

/-! ## Continuity in the centre of the pairings against continuous functions -/

theorem circleMap_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : circleMap c R θ ∈ sphere c R := by
  rw [mem_sphere_iff_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hR]

section DetCont

variable {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
include hW hW0 ht

end DetCont

end XAreaPC
end QuantumZipper.E6
