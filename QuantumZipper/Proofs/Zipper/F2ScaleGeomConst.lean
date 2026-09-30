import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleField
import QuantumZipper.Proofs.GFF.CoordRegLog
import QuantumZipper.Proofs.LQG.CoordChangeKernel

/-!
# F2 step (4): the constant `(2/√κ) log a` of the `h⁰` part

Theorem 1.3, node F2, step (4); Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, §5.1 (pp. 60–62). The field of the scaled configuration in the third conjunct of
`F2.ScaleGeomAeStmt` (`F2Gamma0ScaleRed.lean:81`) is

  `ofFun (h0rev κ) + rescale (X ω) (Qc (√κ)) a`,

i.e. the fluctuation `X` is rescaled (`X(√c ·) + Qc log √c`) but the deterministic part
`h0rev κ = (2/√κ) log‖·‖` is **not**. The true `a`-rescaling of the unscaled field
`ofFun (h0rev κ) + X ω` has the field `rescale (ofFun (h0rev κ) + X ω) (Qc (√κ)) a`, which differs
from the stated one by the constant field `(2/√κ) log a` (times the mass), because

* `h0rev κ (a z) = h0rev κ z + (2/√κ) log a` for `a > 0`, `z ≠ 0` — `integral_h0rev_foldedCircle_mul`
  below, the "`h⁰(√c ·) + Q log √c = h⁰ + const`" of the reduction;
* adding a constant `c` to the input field shifts the coordinate change, hence the unzipped
  field, by exactly `c` at every folded circle (`unzippedField_addConst_fc`; the same computation
  as `F2.coordChange_addConst_fc`, `Proofs/Zipper/F2AddConst.lean:111`).

`RegEq` is the comparison of `avgReg` at folded circles, so this constant is *visible*:
`F2.not_regEq_addConst_one` (`F2ScaleGeomRed.lean`) shows that a nonzero constant shift is not a
`RegEq` equality, for the simplest field. Hence the third conjunct of `ScaleGeomAeStmt` cannot
hold for `a ≠ 1`, and the repairs are those of `F2ScaleGeomRed.lean`.

Own elementary proofs (the change of variables for a folded circle and the coordinate-change
computation of a constant).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Folded circles do not charge points**: `foldedCircle d r {c} = 0` for `r > 0`. Own
elementary proof from `CoordChange.circleUnif_singleton'`: `foldH ⁻¹' {c} ⊆ {c, conj c}` and
`circleUnif d r` charges no point. -/
theorem foldedCircle_singleton_zero (d : ℂ) {r : ℝ} (hr : 0 < r) (c : ℂ) :
    foldedCircle d r {c} = 0 := by
  rw [foldedCircle, Measure.map_apply measurable_foldH (measurableSet_singleton c)]
  have hsub : foldH ⁻¹' {c} ⊆ ({c} ∪ {starRingEnd ℂ c} : Set ℂ) := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    unfold foldH at hz
    split_ifs at hz with h
    · exact Or.inl hz
    · exact Or.inr (by simpa using congrArg (starRingEnd ℂ) hz)
  have hnull : (circleUnif d r) ({c} ∪ {starRingEnd ℂ c} : Set ℂ) = 0 :=
    measure_union_null (CoordChange.circleUnif_singleton' d (ne_of_gt hr) c)
      (CoordChange.circleUnif_singleton' d (ne_of_gt hr) _)
  exact measure_mono_null hsub hnull

/-- **The `h⁰` part scales by the constant `(2/√κ) log a`, at folded circles** (the substituted
form of `ofFun_h0rev_map_mul`). -/
theorem integral_h0rev_foldedCircle_mul {κ a r : ℝ} (ha : 0 < a) (hr : 0 < r) (d : ℂ) :
    ∫ z, h0rev κ ((a : ℂ) * z) ∂foldedCircle d r =
      ∫ z, h0rev κ z ∂foldedCircle d r + 2 / Real.sqrt κ * Real.log a := by
  have hne : ∀ᵐ z ∂foldedCircle d r, z ≠ 0 := by
    rw [ae_iff]
    simpa using foldedCircle_singleton_zero d hr 0
  have hpt : ∀ᵐ z ∂foldedCircle d r,
      h0rev κ ((a : ℂ) * z) = h0rev κ z + 2 / Real.sqrt κ * Real.log a := by
    filter_upwards [hne] with z hz
    have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    unfold h0rev
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le,
      Real.log_mul ha.ne' hzn]
    ring
  have hi : Integrable (fun z : ℂ => h0rev κ z) (foldedCircle d r) :=
    (CoordReg.integrable_log_norm_foldedCircle d r).const_mul (2 / Real.sqrt κ)
  calc ∫ z, h0rev κ ((a : ℂ) * z) ∂foldedCircle d r
      = ∫ z, (h0rev κ z + 2 / Real.sqrt κ * Real.log a) ∂foldedCircle d r :=
        integral_congr_ae hpt
    _ = ∫ z, h0rev κ z ∂foldedCircle d r +
          ∫ _ : ℂ, 2 / Real.sqrt κ * Real.log a ∂foldedCircle d r :=
        integral_add hi (integrable_const _)
    _ = ∫ z, h0rev κ z ∂foldedCircle d r + 2 / Real.sqrt κ * Real.log a := by
        rw [integral_const, probReal_univ, one_smul]

/-- **The `h⁰` part at the dilated circle measure**: the same identity as
`integral_h0rev_foldedCircle_mul`, read as the value of the field `ofFun (h0rev κ)` at the pushed
circle `(foldedCircle d r).map (a ·)`. This is where the constant `(2/√κ) log a` enters the
coordinate change of `rescale (ofFun (h0rev κ) + X) (Qc (√κ)) a`: the `h⁰` part of the true
`a`-rescaled field carries an extra `(2/√κ) log a` that the stated field
`ofFun (h0rev κ) + rescale X (Qc (√κ)) a` of `ScaleGeomAeStmt` does not. -/
theorem ofFun_h0rev_map_mul_foldedCircle {κ a r : ℝ} (ha : 0 < a) (hr : 0 < r) (d : ℂ) :
    ofFun (h0rev κ) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) =
      ofFun (h0rev κ) (foldedCircle d r) + 2 / Real.sqrt κ * Real.log a := by
  have hmeas : Measurable (h0rev κ) := by
    unfold h0rev
    exact (Real.measurable_log.comp measurable_norm).const_mul _
  show ∫ z, h0rev κ z ∂((foldedCircle d r).map (fun z => (a : ℂ) * z)) = _
  rw [integral_map (μ := foldedCircle d r) (φ := fun z : ℂ => (a : ℂ) * z)
    (measurable_const_mul (a : ℂ)).aemeasurable hmeas.aestronglyMeasurable]
  exact integral_h0rev_foldedCircle_mul ha hr d

end F2
end QuantumZipper
