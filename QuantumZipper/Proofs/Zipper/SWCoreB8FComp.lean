import QuantumZipper.Proofs.Thm18.G1Rescale
import QuantumZipper.Proofs.Zipper.SWCoreB8Dil

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (3): the pathwise composition rule `rescale (coordChange x ψ Q) c ~ coordChange x (ψ ∘ (c ·)) Q`

For a conformal `ψ` on `ℍ` (differentiable, `ψ' ≠ 0`, measurable) and `c > 0`:

* `avgReg_comp_mul_eq`: at scale `k` and centre `z`, the regularized circle averages of
  `coordChange x (ψ ∘ (c ·)) Q` and of `rescale (coordChange x ψ Q) Q c` agree, provided the
  folded-circle values of `y = coordChange x ψ Q` are its regularized ones on the countably many
  dilated circles `fc(c d, c 2^{-k})`, `d = dyadicRoundC n z` (RC3 at those circles; this is
  where the orchestrator's warning applies: dilation makes the radii non-dyadic, so the
  exactness of `y` there is a genuine input, available a.s. at countably many fixed circles);
* `bdryApprox_comp_mul_eq`, `integral_bdryR_offset_eq_comp`: hence, for `y` regular, the offset
  approximation of `y` at `c 2^{-k}` is the dyadic approximation of `coordChange x (ψ ∘ (c ·)) Q`
  tested against `f(c ·)`, which is the quantity of the offset flow box (`offInt`).

This is the pathwise form of `Thm18Asm.G1.regEq_coordChange_comp_mul` (G1Rescale.lean, which
needs exactness on every circle), restricted to the circles `avgReg` reads; the raw identity is
`Thm18Asm.G1.coordChange_comp_mul_fc`. Coordinate-change rule of Duplantier–Sheffield, Invent.
Math. 185 (2011), (1.3)/(5.1). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- **Composition rule at the circles read by `avgReg`.** -/
theorem avgReg_comp_mul_eq (x : FieldSample) (Q : ℝ) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ)
    (hint : ∀ n : ℕ, Integrable (fun w => Real.log ‖deriv ψ w‖)
      (foldedCircle ((c : ℂ) * dyadicRoundC n z) (c * radius k)))
    (hexact : ∀ n : ℕ,
      evalReg (coordChange x ψ Q) (foldedCircle ((c : ℂ) * dyadicRoundC n z) (c * radius k)) =
        coordChange x ψ Q (foldedCircle ((c : ℂ) * dyadicRoundC n z) (c * radius k))) :
    avgReg (coordChange x (fun w => ψ ((c : ℂ) * w)) Q) k z =
      avgReg (rescale (coordChange x ψ Q) Q c) k z := by
  unfold avgReg
  congr 1
  funext n
  rw [Thm18Asm.G1.coordChange_comp_mul_fc x Q hψd hψ0 hψm hc _ (radius_pos k) (hint n),
    Thm18Asm.G1.rescale_fc_apply _ Q hc, WedgeTK.fc_foldH_eq, hexact n]

/-- The boundary approximations agree (real centres). -/
theorem bdryApprox_comp_mul_eq (γ : ℝ) (x : FieldSample) (Q : ℝ) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hint : ∀ t : ℝ, ∀ n : ℕ, Integrable (fun w => Real.log ‖deriv ψ w‖)
      (foldedCircle ((c : ℂ) * dyadicRoundC n (t : ℂ)) (c * radius k)))
    (hexact : ∀ t : ℝ, ∀ n : ℕ,
      evalReg (coordChange x ψ Q)
          (foldedCircle ((c : ℂ) * dyadicRoundC n (t : ℂ)) (c * radius k)) =
        coordChange x ψ Q (foldedCircle ((c : ℂ) * dyadicRoundC n (t : ℂ)) (c * radius k))) :
    bdryApprox γ (coordChange x (fun w => ψ ((c : ℂ) * w)) Q) k =
      bdryApprox γ (rescale (coordChange x ψ Q) Q c) k := by
  unfold bdryApprox
  congr 1
  funext t
  rw [avgReg_comp_mul_eq x Q hψd hψ0 hψm hc k _ (hint t) (hexact t)]

end SWCore
end QuantumZipper
