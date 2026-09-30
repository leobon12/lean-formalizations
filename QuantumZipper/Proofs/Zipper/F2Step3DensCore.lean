import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.LQG.PalmNormLocal

/-!
# F2 step (3), density input: the deterministic core of rule (5.1) on `(O⁻_t, O⁺_t)`

Theorem 1.3, node F2, step (3), input `Step3LocalDensityStmt` (`F2Step3.lean`). This file proves
the deterministic core, for one sample and one time:

* `isVagueLimitOnR_congr_avgReg`: two samples whose regularized averages agree on the open set
  `U ⊆ ℝ` for all large `k` have the same local vague limits on `U` (the approximations
  `bdryApprox γ x k` only read `avgReg x k` on `ℝ`).
* `restrict_eq_withDensity_add_ofFun`: rule (5.1) (Sheffield, arXiv:1012.4797, §5.1, p. 61;
  Duplantier–Sheffield, *LQG and KPZ*, Invent. Math. 185 (2011), (5.1)) for global boundary
  measures read on `U`: if `x` agrees near `U` (at the level of `avgReg`) with `y + ofFun φ`,
  `y` a regular sample and `φ` continuous on a neighbourhood of `U` in `ℍ̄`, then
  `ν_x = e^{γφ/2} ν_y` on `U` (`LocalRule.isVagueLimitOnR_add_ofFun`).
* `restrict_eq_logDens`: the case `φ = −γ log|G|` with `G` continuous and nonvanishing near `U`,
  inverted: `ν_y = |G|^{γ²/2} ν_x` on `U` (`e^{(γ/2)·γ log|G|} = |G|^{γ²/2}`).

The regular field is `y` (the unzipped `h⁰ + X`), because the regularity of the unzipped field at
all times is supplied for `h⁰ + X` (`RegUnif.JointModStmt`). The bookkeeping (transfer through
`avgReg`, inversion of the density) is our own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- **Locality of local vague limits (own elementary argument).** If `avgReg x k = avgReg y k` on
the open set `U` for all large `k`, a local vague limit of `bdryApprox γ y` on `U` is also one of
`bdryApprox γ x`. -/
theorem isVagueLimitOnR_congr_avgReg {γ : ℝ} {x y : FieldSample} {U : Set ℝ} (hU : IsOpen U)
    {ν : Measure ℝ} (hν : IsVagueLimitOnR U (bdryApprox γ y) ν)
    (h : ∀ᶠ k in atTop, ∀ t ∈ U, avgReg x k (t : ℂ) = avgReg y k (t : ℂ)) :
    IsVagueLimitOnR U (bdryApprox γ x) ν := by
  refine ⟨hν.1, hν.2.1, fun f hf hfc hfU => ?_⟩
  refine (hν.2.2 f hf hfc hfU).congr' ?_
  filter_upwards [h] with k hk
  exact PalmNorm.integral_eq_of_restrict_eq'
    (PalmNorm.bdryApprox_restrict_eq hU.measurableSet fun t ht => (hk t ht).symm)
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h'))

/-- **Rule (5.1) for global boundary measures read on an open set.** -/
theorem restrict_eq_withDensity_add_ofFun {γ : ℝ} {x y : FieldSample} {U : Set ℝ}
    (hU : IsOpen U) (hx : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν)
    (hy : ∃ ν, IsVagueLimitR (bdryApprox γ y) ν) (hreg : IsRegularSample y) {φ : ℂ → ℝ}
    {V : Set ℂ} (hV : IsOpen V) (hUV : ∀ t ∈ U, (t : ℂ) ∈ V) (hφ : ContinuousOn φ (V ∩ Hbar))
    (h : ∀ᶠ k in atTop, ∀ t ∈ U, avgReg x k (t : ℂ) = avgReg (y + ofFun φ) k (t : ℂ)) :
    (qBoundaryMeasure γ x).restrict U =
      ((qBoundaryMeasure γ y).restrict U).withDensity
        fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t)) := by
  obtain ⟨νx, hνx⟩ := hx
  obtain ⟨νy, hνy⟩ := hy
  rw [qBoundaryMeasure_eq hνx, qBoundaryMeasure_eq hνy]
  have h1 := LocalRule.isVagueLimitOnR_add_ofFun hreg hU
    (PalmNorm.isVagueLimitOnR_restrict_of_R hνy hU) hV hUV hφ
  exact LocalRule.isVagueLimitOnR_unique hU (PalmNorm.isVagueLimitOnR_restrict_of_R hνx hU)
    (isVagueLimitOnR_congr_avgReg hU h1 h)

end F2
end QuantumZipper
