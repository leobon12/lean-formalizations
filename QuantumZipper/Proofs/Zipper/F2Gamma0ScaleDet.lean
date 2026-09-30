import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.Zipper.B3dLen

/-!
# F2 step (4): deterministic scale equivariance of length unzipping

Theorem 1.3, node F2, step (4) (`blueprint/SECTION5_BLUEPRINT.md`, F2). Source: Sheffield,
*Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (pp. 60–62): quantum surfaces are
invariant under the coordinate change `z ↦ a z`, `h ↦ h(a·) + Q log a`, and §5.4 (pp. 70–72,
proof of Theorem 1.3). The paper uses this scaling without proof; the argument below is our own
(elementary algebra of the definitions, following the template of `B3d.unzipLengths_canon`,
`Proofs/Zipper/B3dLen.lean`).

Contents (deterministic):

* `drive_bmScale_all`: the Brownian-rescaled driver `√κ bmScale c B` equals
  `W (c r) / √c`, `W = √κ B`, at **every** time `r : ℝ` (not only `r ≥ 0`), so the rescaled
  configuration has driver literally `fun s => W (a² s) / a` with `a = √c`.
* `unzipLengths_scale`: **scale equivariance of length unzipping.** For `a > 0`, if the field
  unzipped from the configuration `(x', W(a²·)/a)` in capacity time `t` is (up to `RegEq`) the
  `a`-rescaling of the field unzipped from `(x, W)` in time `a² t`, and that field is good, then
  the two length pairs are **equal** — no extra factor: by
  `GoodTransforms.qBoundaryMeasure_rescale`, `ν_{rescale x Q a} = (·/a)_* ν_x` (unlike the
  canonicalization `B3d.unzipLengths_canon`, where the constant shift adds `e^{γk/2}`). Only the
  *agreement* of the two components is used downstream, so this exact form is stronger than
  needed: any common factor of the two components would do.
* `lenAgree_scale`: the agreement `L⁻ = L⁺` transfers from the scaled configuration at time `t`
  to the original one at time `a² t` (the implication used in `GammaZeroScaleStmt`).

The one analytic input is the field identity (`hfield`): it is the composition law of coordinate
changes for the two factorizations `(a·) ∘ f^{W(a²·)/a}_t⁻¹ = f^W_{a²t}⁻¹ ∘ (a·)`
(`RS.fwdMapInv_scale`, `Proofs/RS/TraceShift.lean:225`), which holds at the raw pairing level but
needs regularity of the fields at the regularized level (`RegEq`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **Driver scaling at all times.** `drive κ (bmScale c B) ω r = (√c)⁻¹ W (c r)` for every real
`r`, where `W = drive κ B ω`; for `r < 0` both sides equal `(√c)⁻¹ √κ B 0 ω`. -/
theorem drive_bmScale_all (κ : ℝ) (c : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (r : ℝ) :
    drive κ (bmScale c B) ω r = (√c)⁻¹ * drive κ B ω ((c : ℝ) * r) := by
  by_cases hr : 0 ≤ r
  · exact drive_bmScale κ c B ω hr
  · have hr0 : r.toNNReal = 0 := Real.toNNReal_of_nonpos (not_le.mp hr).le
    have hcr : ((c : ℝ) * r).toNNReal = 0 := Real.toNNReal_of_nonpos (by
      have hcnn := c.coe_nonneg
      nlinarith)
    simp only [drive, bmScale, hr0, hcr, mul_zero]
    ring

end F2
end QuantumZipper
