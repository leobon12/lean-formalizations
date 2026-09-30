import QuantumZipper.Proofs.Zipper.F2LocalSteps

/-!
# F2 step (4): scale invariance removes the smallness condition

Theorem 1.3, node F2, step (4) (`blueprint/SECTION5_BLUEPRINT.md`, F2: "Scale invariance extends
this to every `B_r`, hence to all of `η`"). Source: Sheffield, arXiv:1012.4797, §5.4 (proof of
Theorem 1.3, pp. 70–72) and §5.1 (pp. 60–62: quantum surfaces are invariant under
`z ↦ a z`, `h ↦ h(a·) + Q log a`; adding a constant `C` multiplies lengths by `e^{γC/2}`).

`step4_of_scale : GammaZeroScaleStmt → Step4Stmt`. The input `GammaZeroScaleStmt` is the scale
covariance of `Γ⁰` on a fixed probability space: for `c > 0` the Brownian-rescaled driver
`√κ c^{-1/2} B(c ·)` (a Brownian motion, `IsBrownianReal.smul`) comes with a free field `X'`
independent of it (in the paper `X' = X(√c ·) + const`, dilation invariance of the free field
modulo constants) such that length agreement for `(h⁰ + X', W_c)` at time `t` gives length
agreement for `(h⁰ + X, W)` at time `c t` (B3(d): `h⁰(√c ·) = h⁰ + const`, both lengths are
multiplied by the same constant, `B3d.unzipLengths_canon`). The exhaustion argument (choose `c`
so large that `η[0,t]` becomes small) is our own bookkeeping.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- Brownian scaling `t ↦ c^{-1/2} B(c t)` (as in `IsBrownianReal.smul`). -/
def bmScale {Ω : Type*} (c : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (√c)⁻¹ * B (c * t) ω

/-- The rescaled driver: `√κ bmScale c B` at time `r ≥ 0` is `c^{-1/2} W(c r)`. -/
theorem drive_bmScale {Ω : Type*} (κ : ℝ) (c : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {r : ℝ}
    (hr : 0 ≤ r) : drive κ (bmScale c B) ω r = (√c)⁻¹ * drive κ B ω (c * r) := by
  have h : c * r.toNNReal = ((c : ℝ) * r).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hr,
      Real.coe_toNNReal _ (mul_nonneg c.coe_nonneg hr)]
  simp only [drive, bmScale, h]
  ring

end F2
end QuantumZipper
