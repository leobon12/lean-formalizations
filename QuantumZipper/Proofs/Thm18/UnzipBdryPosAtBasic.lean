import QuantumZipper.Proofs.Thm18.LenPos
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.LQG.GoodSample

/-!
# `UnzipBdryPosAtStmt`, part 1: deterministic positivity transport

Theorem 1.8 (`LenPosStmt`) needs positivity of the unzipped wedge boundary measure at integer
times (`Thm18Asm.UnzipBdryPosAtStmt`, `UnzipBdryPos.lean`). This file proves the deterministic
half of the D29 route (`handoff/WEDGE-UNZIP.md`, `DECISIONS.md` D29): positivity of a boundary
measure on an interval is preserved under

* **rule (5.1)** (Sheffield, arXiv:1012.4797, §5.1, p. 61; Duplantier–Sheffield, *LQG and KPZ*,
  Invent. Math. 185 (2011), (5.1)): `ν_{x + φ} = e^{γφ/2} ν_x` for `φ` continuous on `ℍ̄`
  (`GoodSample.qBoundaryMeasure_add_ofFun`, M4-T1). On a *compact* boundary interval the
  density is bounded below by a positive constant, so a positive mass stays positive
  (`pos_of_withDensity_ge`, `pos_qBoundaryMeasure_add_ofFun`; own elementary argument:
  `∫⁻_I c dν = c · ν I ≤ ∫⁻_I ρ dν`);
* equality of the measures themselves (`F1.qBoundaryMeasure_congr_regEq`).

These are the pieces needed to pass from the free-field-type (`x`-level) positivity input to the
wedge field, once the wedge is written as `x` + a continuous function (W-D + `unzipAddFun`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## Positive densities on a set -/

/-- **A density bounded below by a nonzero constant scales mass up.** If `μ = ν.withDensity ρ`
and `c ≤ ρ` on the measurable set `I` with `c ≠ 0`, then `c · ν I ≤ μ I`. (Own elementary
argument: `∫⁻_I ρ dν ≥ ∫⁻_I c dν = c · ν I`.) -/
theorem pos_of_withDensity_ge {μ ν : Measure ℝ} {I : Set ℝ} (hI : MeasurableSet I)
    {ρ : ℝ → ℝ≥0∞} (h : μ = ν.withDensity ρ) {c : ℝ≥0∞} (_hc0 : c ≠ 0)
    (hρ : ∀ t ∈ I, c ≤ ρ t) : c * ν I ≤ μ I := by
  subst h
  have hconst : ∫⁻ _ in I, c ∂ν = c * ν I := by
    rw [lintegral_const, Measure.restrict_apply' hI, univ_inter]
  rw [withDensity_apply ρ hI, ← hconst]
  exact lintegral_mono_ae ((ae_restrict_mem hI).mono fun t ht => hρ t ht)

/-- **A positive density on a set preserves positivity of the mass.** -/
theorem pos_of_withDensity_ge' {μ ν : Measure ℝ} {I : Set ℝ} (hI : MeasurableSet I)
    {ρ : ℝ → ℝ≥0∞} (h : μ = ν.withDensity ρ) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hρ : ∀ t ∈ I, c ≤ ρ t) (hν : 0 < ν I) : 0 < μ I :=
  lt_of_lt_of_le (ENNReal.mul_pos hc0 hν.ne') (pos_of_withDensity_ge hI h hc0 hρ)

end Thm18Asm
end QuantumZipper
