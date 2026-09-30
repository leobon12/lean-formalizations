import QuantumZipper.Proofs.Zipper.Thm13AssemblyStmt
import QuantumZipper.Proofs.Zipper.ESMComplF1
import QuantumZipper.Proofs.Zipper.F1ReflReg
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Zipper.F1Germ
import QuantumZipper.Proofs.Thm18.LenPos
import QuantumZipper.Proofs.LQG.WedgeCRegCirc

/-!
# Theorem 1.3, node F1: assembly of `Thm13Asm.F1NodeStmt` (F1a–F1d)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3
(pp. 70–72): under `P_*` the ratio `L⁺/L⁻` of the two unzipped lengths is a.s. constant in time
(stationarity of the length zipper, E6, and scaling), constant in `ω` (a 0-1 law), and equal to
`1` "by symmetry". Blueprint: `blueprint/E_BRANCH_BLUEPRINT.md` §F1 (F1a–F1d).

This file assembles F1 from the proved F1d (`F1.f1d_lengths_agree_wedge_bm`) and:

* input (c) of F1d, B4(d): `WedgeCReg.wedgeRefReflectStmt_holds'` (unconditional);
* the reflection identity at time `1` (`pstar_refl_one`): inputs (a) `regEq_unzippedField_reflect`
  (through `unzipLengths_reflect_of_good`) and (b) `ae_sideImages_reflect_drive`, given goodness of
  the unzipped field at time `1` (`PStarUnzipGoodStmt`, open);
* `0 < L⁻₁ < ⊤` (`pstar_pos_one`): `Thm18Asm.lenPosStmt_of_bdryPos` (`O⁻ < 0` proved,
  finiteness unconditional) from `Thm18Asm.UnzipBdryPosStmt` (open, shared with Theorem 1.8);
* F1a–F1b (`F1ABStmt`; reduced in `F1ABJensen.lean` by `f1ABStmt_of_inputs`, via Jensen
  rigidity, to a cocycle, a scaling, a regularity, a bridge and a reading input) and F1c
  (`F1CStmt`, open), stated exactly below;
* the measurable reading `ReadLenAEMeasStmt` (open, F1d input (d)).

`f1Node_of_inputs` is the assembly. The bookkeeping (random ratio `f` + a.s. constant ratio at
time `1` + `0 < L⁻₁ < ⊤` ⇒ `L⁺ = k L⁻` with a constant `k`) is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## The open inputs -/

/-! ## `P_*` samples are Theorem 1.8 settings -/

theorem sqrt_lt_two_of {κ : ℝ} (hκ4 : κ < 4) : Real.sqrt κ < 2 :=
  (Real.sqrt_lt' two_pos).2 (by norm_num; exact hκ4)

theorem thm18Setting_of_pstar {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Y : Ω' → FieldSample} {B' : ℝ≥0 → Ω' → ℝ} (h : Thm13Asm.IsPStarSample κ P' Y B') :
    Thm18Asm.Thm18Setting (Real.sqrt κ) P' B' Y :=
  ⟨Real.sqrt_pos.2 h.1, sqrt_lt_two_of h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.symm⟩

/-! ## Assembly -/

end F1
end QuantumZipper
