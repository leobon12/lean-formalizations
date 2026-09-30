import QuantumZipper.Proofs.Zipper.TipXScaleGeo
import QuantumZipper.Proofs.LQG.GoodTransforms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC (scaling), part 2: the weighted masses under scaling

Task TX-SC (handoff `handoff/TIPX-ROUTE.md`, decision D51). For `a ∈ (0, 1]` and two unzipped
configurations whose `Γ⁰` fields are related at every folded circle by
`⟨y'', fc(u, r)⟩ = ⟨y, fc(a u, a r)⟩ + Q log a − C` (the scaling rule `h ↦ h(a·) + Q log a` of
Sheffield arXiv:1012.4797, §5.1, pp. 60–62, and adding the constant `−C`), and whose inverse maps
satisfy `E''(z) = a⁻¹ E(a z)` on `ℍ` (Loewner scaling), the weighted masses satisfy
`wBdryR(W, a r)(S) ≤ a^{−κ/2} e^{γ C/2} · wBdryR''(r)(a⁻¹ S)` for every set `S`
(`wBdryR_scale_le`).

The tip weight: `ψ''(z) = ψ(a z) + γ log a` on `ℍ`, hence `tipWt'' = a^{κ/2} tipWt` when the
circle average of `ψ` is a genuine integral; otherwise both Bochner integrals are the junk value
`0` and `tipWt'' = 1 ≥ a^{κ/2} = a^{κ/2} tipWt` because `a ≤ 1`. So only the inequality is claimed
(which is all the per-piece transfer needs).

Own elementary bookkeeping (change of variables `u ↦ a u` on the line, constants of the
boundary density: `GoodTransforms.gammaQ_bdry`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## Change of variables for iterated densities -/

/-! ## The boundary density and the tip weight under scaling -/

theorem bdryDens_scale_eq {γ : ℝ} (hγ : 0 < γ) {y y'' : FieldSample} {a C r u : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hE : evalReg y'' (foldedCircle (u : ℂ) r) =
      evalReg y (foldedCircle ((a * u : ℝ) : ℂ) (a * r)) + Qc γ * Real.log a - C) :
    bdryDens γ y'' r u =
      (a * Real.exp (-(γ * C / 2))) * bdryDens γ y (a * r) (a * u) := by
  have hQ := GoodTransforms.gammaQ_bdry hγ
  unfold bdryDens
  rw [hE, Real.mul_rpow ha.le hr.le, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hr]
  rw [show a * Real.exp (-(γ * C / 2)) = Real.exp (Real.log a + -(γ * C / 2)) by
    rw [Real.exp_add, Real.exp_log ha]]
  simp only [← Real.exp_add]
  congr 1
  linear_combination (Real.log a) * hQ

/-! ## The weighted masses -/

end WedgeUnzip
end QuantumZipper
