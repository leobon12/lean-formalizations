import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale

/-!
# F2 step (4): the field identity of the scaling

Theorem 1.3, node F2, step (4); Sheffield, arXiv:1012.4797, §5.1 (pp. 60–62) and §5.4
(pp. 70–72). The deterministic field identity behind `F2.unzipLengths_scale`
(`F2Gamma0ScaleDet.lean`): with `Φ = (a ·)`, `G = fwdMapInv (W(a²·)/a) t` and
`F = fwdMapInv W (a²t)` (related by the Loewner scaling `Φ ∘ G = F ∘ Φ` on `ℍ`,
`RS.fwdMapInv_scale`), the field unzipped from the scaled configuration

  `(rescale x (Qc γ) a, W(a²·)/a)`   at capacity time `t`

is (`RegEq`) the `a`-rescaling of the field unzipped from `(x, W)` at capacity time `a² t`:

  `regEq_unzippedField_scale`.

This is the `hfield` hypothesis of `F2.unzipLengths_scale`, so together with it the length pair
unzipped from the scaled configuration at time `t` equals (exactly, no constant factor — the
`Q log a` term of the rescaling is absorbed by `GoodTransforms.qBoundaryMeasure_rescale`) the pair
unzipped from the original at time `a² t`.

The work is done by the existing abstract statement
`WedgeUnzip.regEq_coordChange_rescale_of_scale` (`Proofs/Zipper/WedgeUnzipScale.lean:123`), the
general form of the coordinate-change cocycle at the regularized level (it already contains the
chain rule for the two factorizations and the `Measure.map` bookkeeping for folded circles); here
we only instantiate it at the two Loewner inverse maps and discharge its analytic hypotheses with
`WedgeUnzip.fwdMapInv_props` (holomorphy, injectivity, nonvanishing derivative on `ℍ`, whence the
`log‖deriv‖`-integrability over folded circles by Koebe distortion).  The two inputs left are the
regularity statements of the D29 interface (`handoff/WEDGE-UNZIP.md`):
`hsc` — scale consistency `G1.ScaleConsistentAt` of the regularization of `x` at the images of
folded circles under `G` (the `B3(a)`/continuum-limit input), and `hexact` — `RC3` for the
unzipped field at time `a² t`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- **Field identity of the scaling** (the `hfield` hypothesis of `F2.unzipLengths_scale`): the
field unzipped from `(rescale x (Qc γ) a, W(a²·)/a)` in capacity time `t` is (`RegEq`) the
`a`-rescaling of the field unzipped from `(x, W)` in capacity time `a² t`. -/
theorem regEq_unzippedField_scale {x : FieldSample} {W : ℝ → ℝ} {γ a t : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hW : Continuous W) (hW0 : W 0 = 0)
    (hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → Thm18Asm.G1.ScaleConsistentAt x (Qc γ) a
      ((foldedCircle d r).map (fwdMapInv (fun s => W (a ^ 2 * s) / a) t)))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (x, W) (a ^ 2 * t)) (foldedCircle d r) =
        unzippedField γ (x, W) (a ^ 2 * t) (foldedCircle d r)) :
    RegEq (unzippedField γ (rescale x (Qc γ) a, fun s => W (a ^ 2 * s) / a) t)
      (rescale (unzippedField γ (x, W) (a ^ 2 * t)) (Qc γ) a) := by
  have hWa : Continuous fun s : ℝ => W (a ^ 2 * s) / a := by fun_prop
  have hWa0 : (fun s : ℝ => W (a ^ 2 * s) / a) 0 = 0 := by simp [hW0]
  have ha2t : (0 : ℝ) ≤ a ^ 2 * t := mul_nonneg (by positivity) ht
  obtain ⟨hφd, hφi, hφ0⟩ := WedgeUnzip.fwdMapInv_props hWa hWa0 ht
  obtain ⟨hψd, hψi, hψ0⟩ := WedgeUnzip.fwdMapInv_props hW hW0 ha2t
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hscale : ∀ w ∈ H, (a : ℂ) * fwdMapInv (fun r => W (a ^ 2 * r) / a) t w =
      fwdMapInv W (a ^ 2 * t) ((a : ℂ) * w) := fun w hw => by
    rw [RS.fwdMapInv_scale hW hW0 ha ht hw, mul_div_cancel₀ _ ha']
  exact WedgeUnzip.regEq_coordChange_rescale_of_scale x (Qc γ) ha hφd hφi hφ0 hψd hψi hψ0
    hscale hsc hexact

end F2
end QuantumZipper
