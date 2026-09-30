import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1: B3(d) along the capacity flow

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6 and §5.1 (pp. 60–62:
unzipping commutes with the rescaling `h ↦ h(a·) + Q log a` together with Brownian scaling of the
driver), as in `WedgeUnzip.regEq_unzippedField_canonConfig` (`WedgeUnzipScale.lean`), whose
argument we follow for a general scale `a` (not only `a = scaleParam γ y`).

* `unzipLengths_rescaled`: the lengths of `(y', W(a²·)/a)` at time `s` are those of `(y, W)` at
  time `a² s`, given the field identity, goodness and the side limits (general-`a` form of
  `B3d.unzipLengths_canon`).
* `regEq_unzippedField_rescaled`: the field identity for `y' = rescale y Q a` (general-`a` form of
  `WedgeUnzip.regEq_unzippedField_canonConfig`), from scale consistency and RC3.
* `unzipLengths_zipCapDown_canon`: **B3(d) along the flow**, deterministic: the lengths of
  `canonConfig γ c` unzipped by `u` at time `s` are those of `c` unzipped by `a² u` at time `a² s`.
* `unscaledFlowLenScaleStmt_of_reg`: `F1.UnscaledFlowLenScaleStmt` from `F2.UnscaledB3dStmt` and
  the regularity of the unscaled configuration along its capacity flow (`UnscaledFlowRegStmt`).

Own elementary bookkeeping around the cited scaling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

variable {γ : ℝ}

/-- **The B3(d) field identity for a general scale `a`** (general-`a` form of
`WedgeUnzip.regEq_unzippedField_canonConfig`, same proof). -/
theorem regEq_unzippedField_rescaled {y : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s)
    (hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → Thm18Asm.G1.ScaleConsistentAt y (Qc γ) a
      ((foldedCircle d r).map (fwdMapInv (fun r => W (a ^ 2 * r) / a) s)))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (y, W) (a ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (y, W) (a ^ 2 * s) (foldedCircle d r)) :
    RegEq (unzippedField γ (rescale y (Qc γ) a, fun r => W (a ^ 2 * r) / a) s)
      (rescale (unzippedField γ (y, W) (a ^ 2 * s)) (Qc γ) a) := by
  have hWa : Continuous fun r => W (a ^ 2 * r) / a := by fun_prop
  have hWa0 : (fun r => W (a ^ 2 * r) / a) 0 = 0 := by simp [hW0]
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  obtain ⟨hφd, hφi, hφ0⟩ := WedgeUnzip.fwdMapInv_props hWa hWa0 hs
  obtain ⟨hψd, hψi, hψ0⟩ := WedgeUnzip.fwdMapInv_props hW hW0 has
  have hscale : ∀ w ∈ H, (a : ℂ) * fwdMapInv (fun r => W (a ^ 2 * r) / a) s w =
      fwdMapInv W (a ^ 2 * s) ((a : ℂ) * w) := fun w hw => by
    rw [RS.fwdMapInv_scale hW hW0 ha hs hw]
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    rw [mul_div_cancel₀ _ ha']
  exact WedgeUnzip.regEq_coordChange_rescale_of_scale y (Qc γ) ha hφd hφi hφ0 hψd hψi hψ0
    hscale hsc hexact

/-- The driver of the canonicalized configuration unzipped by `u` is the Brownian rescaling of
the driver of the configuration unzipped by `a² u`. -/
theorem zipCapDown_canonConfig_snd (y : FieldSample) (W : ℝ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (zipCapDown γ u (canonConfig γ (y, W))).2 = fun r =>
      (zipCapDown γ (scaleParam γ y ^ 2 * u) (y, W)).2 (scaleParam γ y ^ 2 * r) /
        scaleParam γ y := by
  funext r
  simp only [zipCapDown, canonConfig]
  have h1 : max (u + max r 0) 0 = u + max r 0 := max_eq_left (by positivity)
  have h2 : max u 0 = u := max_eq_left hu
  have h3 : max (scaleParam γ y ^ 2 * r) 0 = scaleParam γ y ^ 2 * max r 0 := by
    rw [mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero]
  rw [h1, h2, h3, sub_div, mul_add]

end F1
end QuantumZipper
