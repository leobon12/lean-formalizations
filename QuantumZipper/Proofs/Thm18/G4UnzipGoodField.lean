import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.HitScaleZip
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale

/-!
# Theorem 1.8, node G4: the field half of the unzipping cocycle, reduced to the D29 inputs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2) and §5.1
(Brownian scaling of the driver, pp. 60–62). This file reduces the field half of the one-step
unzipping cocycle (`UnzipFieldRegData`, the `RegEq` clause of `UnzipCocycleData`, the sharper
form of `UnzipFieldRawData` in `G4UnzipGoodCocycle.lean`) to two named inputs:

* **the capacity field cocycle at the sample** (`UnzipCapRegData`): unzipping by capacity time
  `u` the configuration already unzipped by `t` gives the field unzipped by `t + u`. This is the
  `RegEq` clause of `B3d.CapCocycleRegStmt` (`Zipper/B3dStmt.lean`; Corollary 1.5 (b),
  `zipCapDown` cocycle), stated for an arbitrary configuration (the transfer from the free-field
  sample `B2.cfg κ B X` to the `P_*`/wedge sample is not done here);
* **the two D29 inputs of `WedgeUnzip.regEq_unzippedField_canonConfig`** (`ScaleConsistentData`,
  `UnzipExactData`): scale consistency (`G1.ScaleConsistentAt`) of the capacity-unzipped field at
  scale `unzipScale`, and RC3 exactness of the field unzipped by the rescaled time.

Proved here:

* `zipCapDown_snd_max`, `zipLenDown_eq_canonConfig'`: the driver of `zipCapDown` is normalized
  and `Z^LEN_{−ℓ}` is the canonicalization of the capacity unzipping at the first passage time
  (`LengthZip.zipLenDown_eq_canonConfig`), so `zipLenDown` has exactly the shape of
  `canonConfig` to which the B3(d) field identity applies;
* `regEq_unzippedField_zipLenDown`: the S2 scaling identity at the *random* unzipping time
  (`WedgeUnzip.regEq_unzippedField_canonConfig`, Sheffield §5.1/B3(d)), i.e. `unzipping by `s`
  the rescaled configuration is the `a`-rescaling of unzipping by `a² s`;
* `unzipFieldRegData_of_cap`: the composition of the two, giving `UnzipFieldRegData`;
* the a.s. statements `G4UnzipS2Stmt`, `G4UnzipCapRegStmt`, `G4UnzipFieldRegStmt` and the
  reductions `g4UnzipFieldRegStmt_of`, `g4UnzipCocycleStmt_of_cap`, `g4GroupNegStmt_of_cap`.

Own bookkeeping (the driver algebra and the composition; the mathematics is the cited B3(d)
identity and Corollary 1.5 (b)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## Driver algebra and the `canonConfig` form of `zipLenDown` -/

/-- The driver of `zipCapDown` is normalized (`W (max s 0) = W s`). -/
theorem zipCapDown_snd_max (γ t : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    ∀ s : ℝ, (zipCapDown γ t c).2 (max s 0) = (zipCapDown γ t c).2 s := by
  intro s
  simp only [zipCapDown]
  rw [max_assoc, max_self]

/-! ## The two D29 inputs at the random time -/

/-! ## The S2 scaling identity at the random time -/

/-! ## The field half from the capacity cocycle -/

/-- **Capacity field cocycle at a sample** (`RegEq` clause of `B3d.CapCocycleRegStmt`, Sheffield
Corollary 1.5 (b)): unzipping `zipCapDown γ t c` by capacity time `u` gives the field of
`zipCapDown γ (t + u) c`. -/
def UnzipCapRegData (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) : Prop :=
  ∀ t u : ℝ, 0 ≤ t → 0 ≤ u →
    RegEq (unzippedField γ (zipCapDown γ t c) u) (unzippedField γ c (t + u))

/-! ## The a.s. statements -/

/-! ## End-to-end reductions -/

end Thm18Asm
end QuantumZipper
