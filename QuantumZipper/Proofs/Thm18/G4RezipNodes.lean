import QuantumZipper.Proofs.Thm18.G4RezipDet

/-!
# Theorem 1.8, node G4: the rezip cores from regularity at pushed circles

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). The rezip
conjuncts of `G4RoundDownRezipCoreStmt` and `RoundUpRezipCoreData` follow deterministically
(`G4RezipDet`) from regularity of the intermediate fields at the images of the countably many
dyadic folded circles `σ_i` under the (random, field-dependent) zipping/unzipping maps, and, for
the unzip-then-zip direction, from `σ_i` not charging the rezipped hull. This is the Theorem 1.8
analogue of the fixed-time Corollary 1.5 reduction `Cor15Group.cor15RezipFieldStmt_of`
(nodes `Cor15HullNullStmt`, `Cor15RezipRegStmt`). **Own elementary argument.**

* `regEq_rezipDown_zip`, `regEq_rezipUp_cfg`: deterministic `RegEq` forms at a configuration.
* `G4DownScaleTimeStmt`, `G4DownZipPushRegStmt` ⟹ `G4RoundDownRezipCoreStmt`
  (`g4RoundDownRezipCoreStmt_of`).
* `G4UpWeldCoreStmt`, `G4UpZipPushRegStmt` ⟹ `G4RoundUpRezipCoreStmt`
  (`g4RoundUpRezipCoreStmt_of`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The `i`-th dyadic folded circle. -/
abbrev fcI (i : ℕ) : Measure ℂ := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2

/-! ## Zip-then-unzip -/

/-! ## Unzip-then-zip -/

/-- On `[0, τ/a²]` the rescaled reversed driver `revDrv W τ a` is `vrev W τ (a² ·)/a`. -/
theorem revDrv_eqOn_vrev (W : ℝ → ℝ) {τ a : ℝ} (hτ : 0 ≤ τ) (ha : 0 < a) :
    EqOn (revDrv W τ a).2 (fun s => B2.vrev W τ (a ^ 2 * s) / a) (Icc 0 (revDrv W τ a).1) := by
  intro s hs
  have hs2 : a ^ 2 * s ≤ τ := by
    have := hs.2
    simp only [revDrv] at this
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  simp only [revDrv, B2.vrev, max_eq_left (mul_nonneg (sq_nonneg a) hs.1), min_eq_left hs2]

end Thm18Asm
end QuantumZipper
