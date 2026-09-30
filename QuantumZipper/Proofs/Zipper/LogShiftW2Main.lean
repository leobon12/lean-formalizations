import QuantumZipper.Proofs.Zipper.LogShiftW2Transport
import QuantumZipper.Proofs.Zipper.LogShiftWRed
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.Section5.Prop17Field
import QuantumZipper.Proofs.Field.Factorization
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.F2Step2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-W2 (2): `LogShiftLenWeightStmt` without the stage-geometry and shifted-density nodes

Task LSL-W2. `logShiftLenWeightStmt_of_w2` proves `F1.LogShiftLenWeightStmt` from

* the existing `Γ⁰` nodes `LenPairCocycleCfgStmt` (capacity cocycle of both lengths) and
  `LenRegCfgStmt` (continuity of both lengths), which the consumers
  `logShiftLenDensityStmt_of_weight`, `logShiftLenFlowMeasStmt_of_weight` require anyway;
* the proved field cocycle of the `Γ⁰` configuration at all times
  (`RegUnif.capCocycleRegAllStmt_holds`, D33): the field unzipped by `r` and then by `T − r` is
  `avgReg`-equal to the field unzipped by `T`, so the `Γ⁰` length of the new piece `η[r, T]` is the
  `Γ⁰` boundary measure, **at stage `T`**, of `[a_T(r), 0]` and `[0, b_T(r)]`, where
  `(a_T(r), b_T(r)) = lswPos W T r` are the side images of the driver restarted at `r`;
* the stage density `LogShiftWDens0Stmt` (proved from the wedge nodes, `logShiftWDens0Stmt_of_x`);
* two new leaves, both strictly smaller than the nodes they replace (`LogShiftWArcsStmt`,
  `LogShiftWDensShiftStmt`):
  - **`LswPosStmt`** (deterministic Loewner facts for the simple SLE trace, `κ < 4`): `r ↦ a_T(r)`
    is continuous and strictly increasing on `[0, T]`, `r ↦ b_T(r)` continuous and strictly
    decreasing, and the boundary extension `E_T` of `f_T⁻¹` sends `a_T(r)`, `b_T(r)` to the trace
    point `η(r)` (the TX-COV item (i) of `handoff/TIPX-ROUTE.md`; Lawler 2005 §4.1, Rohde–Schramm
    2005 Thm 5.1);
  - **`LswZCocycleRegStmt`**: the field cocycle `avgReg`-identity for the log-shifted configuration
    `(Z, W)` (the analogue of the proved `Γ⁰` field cocycle D33).

With these, every length of the target is read at one stage `T` through the global density
`ν_Z = e^{γφ(E_T ·)/2} ν_Γ` off the tips (no nested tips are needed), and transported to capacity
time by `lsw2_stage`. The representing measures have no atoms (`lsw2_atom_zero`, from
`LenRegCfgStmt`). Own bookkeeping; sources as in `LogShiftWRed.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- Side images at stage `T` of the curve point of capacity time `r`: the side images at time
`T − r` of the driver restarted at `r`. -/
def lswPos (W : ℝ → ℝ) (T r : ℝ) : ℝ × ℝ := sideImages (fun v => W (r + max v 0) - W r) (T - r)

theorem lswPos_self (W : ℝ → ℝ) (T : ℝ) : lswPos W T T = (0, 0) := by
  unfold lswPos
  rw [sub_self]
  exact Prod.ext (B5.sideImages_fst_zero_time (by simp)) (F2.sideImages_snd_zero_time (by simp))

theorem lswPos_zero_drive {κ : ℝ} {Ω : Type} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (h0 : B 0 ω = 0)
    (T : ℝ) : lswPos (drive κ B ω) T 0 = sideImages (drive κ B ω) T := by
  unfold lswPos
  rw [sub_zero]
  congr 1
  funext v
  have hd0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  rw [zero_add, hd0, sub_zero]
  rcases le_total v 0 with hv | hv
  · rw [max_eq_right hv, hd0]
    simp [drive, Real.toNNReal_of_nonpos hv, h0]
  · rw [max_eq_left hv]

theorem lsw2_cancel {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (h : a + b = a + c) : b = c := by
  have := congrArg (fun x => x - a) h
  simpa [ENNReal.add_sub_cancel_left ha] using this

theorem lsw2_alg_shift {Lu Lr LT Nr MuT Mur MrT : ℝ≥0∞} (hr : Lr ≠ ⊤) (h1 : LT = Lr + Nr)
    (h2 : LT = Lu + MuT) (h3 : Lr = Lu + Mur) (h4 : MuT = Mur + MrT) : Nr = MrT := by
  apply lsw2_cancel hr
  rw [← h1, h2, h4, h3, add_assoc]

theorem lsw2_alg_zero {Lr LT Nr M0T M0r MrT : ℝ≥0∞} (hr : Lr ≠ ⊤) (h1 : LT = Lr + Nr)
    (h2 : LT = M0T) (h3 : Lr = M0r) (h4 : M0T = M0r + MrT) : Nr = MrT := by
  apply lsw2_cancel hr
  rw [← h1, h2, h4, h3]

theorem lsw2_Ioc_split (μ : Measure ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    μ (Ioc a c) = μ (Ioc a b) + μ (Ioc b c) := by
  rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
    Ioc_union_Ioc_eq_Ioc hab hbc]

/-- **Loewner boundary correspondence at every stage** (new leaf). -/
def LswPosStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T →
      ContinuousOn (fun r => (lswPos (drive κ B ω) T r).1) (Icc 0 T) ∧
      ContinuousOn (fun r => (lswPos (drive κ B ω) T r).2) (Icc 0 T) ∧
      StrictMonoOn (fun r => (lswPos (drive κ B ω) T r).1) (Icc 0 T) ∧
      StrictAntiOn (fun r => (lswPos (drive κ B ω) T r).2) (Icc 0 T) ∧
      ∀ r ∈ Ioc 0 T,
        F2.extInv (drive κ B ω) T ((lswPos (drive κ B ω) T r).1 : ℂ) = trace (drive κ B ω) r ∧
        F2.extInv (drive κ B ω) T ((lswPos (drive κ B ω) T r).2 : ℂ) = trace (drive κ B ω) r

/-- **Field cocycle of the log-shifted configuration** (new leaf; the analogue of the proved
`Γ⁰` field cocycle `RegUnif.capCocycleRegAllStmt_holds`). -/
def LswZCocycleRegStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (G : Ω → ℂ → ℝ) (Z : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    (∀ᵐ ω ∂P, Continuous (G ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z ω (foldedCircle d r) = (X ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r)) →
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      RegEq (unzippedField (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (Z ω, drive κ B ω)) s)
        (unzippedField (Real.sqrt κ) (Z ω, drive κ B ω) (u + s))

end F1
end QuantumZipper
