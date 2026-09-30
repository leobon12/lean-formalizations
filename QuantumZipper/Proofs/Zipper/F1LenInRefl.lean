import QuantumZipper.Proofs.Zipper.F1LenInScale
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.UnifUOPlus
import QuantumZipper.Proofs.Zipper.JointModAssembly
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.Proofs.Zipper.F1Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1: the `L⁺` cocycle by reflection (`Γ⁰` picture)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 p. 72 ("by
symmetry"): the reflection `z ↦ −z̄` exchanges the two sides of the curve. We follow the raw
reflection route of `UnifUOPlusRefl.lean` (decision D26): for a `Γ⁰` pair `(B, X)` the reflected
pair `(−B, X ∘ refl)` is again a `Γ⁰` pair (`RegUnif.isFreeGFFModConstH_reflRaw`,
`RegUnif.indepFun_neg_reflRaw`), and its configuration is the raw reflection of the original
(`RegUnif.reflRaw_add_ofFun_h0rev`, `RegUnif.drive_negB`).

* `qBoundaryMeasure_of_avgReg_neg`: if the regularized averages of `x'` at real `t` are those of
  `x` at `−t`, and `bdryApprox γ x` has a vague limit, then `ν_{x'} = (−·)_* ν_x` (uniqueness of
  vague limits, `isVagueLimitR_unique`).
* `unzipLengths_reflRaw`: the lengths of `(reflRaw x, −W)` are the swapped lengths of `(x, W)`.
* `lenRightCocycleCfgStmt_of_refl`: the `L⁺` cocycle for `(B, X)` from the `L⁻` cocycle for the
  reflected pair, the field cocycle (`RegUnif.capCocycleRegAllStmt_holds`, D33, proved) and the
  regularity input `CfgFlowRegStmt` (regularity and boundary vague limit of the unzipped field
  at all times, side limits along the flow).

The identifications are own elementary arguments (the paper only says "by symmetry").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- **Boundary measure of a reflected field** (general form: only the regularized averages at
real points are used). -/
theorem qBoundaryMeasure_of_avgReg_neg {γ : ℝ} {x x' : FieldSample}
    (havg : ∀ (k : ℕ) (t : ℝ), avgReg x' k (t : ℂ) = avgReg x k ((-t : ℝ) : ℂ))
    (hx : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν) :
    qBoundaryMeasure γ x' = (qBoundaryMeasure γ x).map fun t : ℝ => -t := by
  obtain ⟨hloc, htend⟩ := E1.M4.isVagueLimitR_qBoundaryMeasure hx
  set ν := qBoundaryMeasure γ x
  have hlim : IsVagueLimitR (bdryApprox γ x') (ν.map fun t : ℝ => -t) := by
    have hfc : IsFiniteMeasureOnCompacts (ν.map fun t : ℝ => -t) := ⟨fun K hK => by
      rw [Measure.map_apply measurable_neg hK.measurableSet]
      exact ((Homeomorph.neg ℝ).isCompact_preimage.2 hK).measure_lt_top⟩
    refine ⟨inferInstance, fun f hf hfc' => ?_⟩
    have h := htend (fun t => f (-t)) (hf.comp continuous_neg)
      (hfc'.comp_homeomorph (Homeomorph.neg ℝ))
    rw [integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
    refine h.congr' (Eventually.of_forall fun k => ?_)
    have h' : ∀ t : ℝ, avgReg x k (t : ℂ) = avgReg x' k ((-t : ℝ) : ℂ) := fun t => by
      rw [havg k (-t), neg_neg]
    exact (RegUnif.integral_bdryApprox_neg k h' f hf).symm
  rw [qBoundaryMeasure, dif_pos (⟨_, hlim⟩ : ∃ ν, IsVagueLimitR (bdryApprox γ x') ν)]
  exact isVagueLimitR_unique (Exists.choose_spec (p := fun ν => IsVagueLimitR (bdryApprox γ x') ν)
    ⟨_, hlim⟩) hlim

/-! ## The `Γ⁰` statement -/

end F1
end QuantumZipper
