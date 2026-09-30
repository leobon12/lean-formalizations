import QuantumZipper.Proofs.Thm18.ASepD84Wire
import QuantumZipper.Proofs.Thm18.R18RTLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-RT (1/2): RT1, the first D82 round trip and clause (3) from the `τ' = 0` leaf

D84 rewiring of the D82 consumers of the A-sep leaf (task ASEP): verbatim copies of the R18RT*
theorems named below with `G4Core.G4SepRepStmt` replaced by the weaker `τ' = 0` leaf
`ASep.G4SepRep0Stmt` (A-sep enters only through `g4RoundDownA_of` and `g4ZipRegAStmt_of_X1`, i.e. at
`τ' = 0`; replaced by `ASep.g4RoundDownA0_of`, `ASep.g4ZipRegA0_of`). Sources as in the originals
(Sheffield, arXiv:1012.4797, Theorem 1.8, p. 26). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core R18

/-- RT1 from the `τ' = 0` leaf (copy of `R18.ae_πd_offData_roundDown`). -/
theorem ae_πd_offData_roundDown0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y)
    (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, πd (offData (zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).toPair) =
      πd (offData (wedgeAConfig γ B Y ω).toPair) := by
  classical
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  have hA : G4DriverPushSep0Stmt := g4DriverPushSep0Stmt_of_rep0 hSep0
  have hD := g4RoundDownA0_of hA (g4UpWeldCoreAStmt_of_X1 hX1) γ P B Y hS hIn hE6 hEq ℓ hℓ
  obtain ⟨hco, -⟩ := g4ZipRegA0_of (g4DriverPushSep0Stmt_of_rep0 hSep0) (g4UpWeldCoreAStmt_of_X1 hX1) γ P B Y hS hIn hE6 hEq ℓ hℓ
  obtain ⟨hw, -⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  filter_upwards [hco, hw, hD] with ω h1 h2 h3
  obtain ⟨hreg, hdrv⟩ := h3
  set Z := zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)) with hZ
  have hcur : curveOf Z.drv = curveOf (drive (γ ^ 2) B ω) := curveOf_congr hdrv
  have hreg' : RegEqOff (curveOf (drive (γ ^ 2) B ω)) Z.fld (Y ω) := hreg
  refine Prod.ext ?_ ?_
  · funext i
    show (if CircleOff (curveOf Z.drv) _ _ then CoordsFull.coordsFull Z.fld i else 0) =
      (if CircleOff (curveOf (drive (γ ^ 2) B ω)) _ _ then CoordsFull.coordsFull (Y ω) i else 0)
    rw [hcur]
    split_ifs with hc
    · have hr := (UnzipFull.fullIndex_radius_pos i).le
      have e1 := h1 i (by rw [hcur]; exact hc)
      show Z.fld _ = Y ω _
      rw [← e1, evalReg_foldedCircle_congr_of_regEqOff hreg' hr hc]
      exact h2.1 i
    · rfl
  · funext u
    exact hdrv u u.2

/-- Clause (3) for the D82 zipper from the `τ' = 0` leaf (copy of `R18.lawMA_of`). -/
theorem lawMA_of0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hM : MaskExactFullAStmt) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (t : ℝ) :
    configLawOff (fun ω => (zipLenMA γ t (wedgeAConfig γ B Y ω)).toPair) P =
      configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P := by
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  have hA : G4DriverPushSep0Stmt := g4DriverPushSep0Stmt_of_rep0 hSep0
  have hD := g4RoundDownA0_of hA (g4UpWeldCoreAStmt_of_X1 hX1)
  rw [configLawOff_wedgeAConfig]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [zipLenMA_of_neg ht]
    have e := hM γ P B Y hS hIn (-t) (neg_pos.2 ht)
    rw [configLawOff_eq_map_offData, Measure.map_congr e, ← configLawOff_eq_map_offData]
    exact hE6 (-t) (neg_pos.2 ht)
  · subst ht
    rw [zipLenMA_of_nonneg le_rfl, ← zipLenA_of_nonneg le_rfl]
    exact g4ZeroAStmt_holds γ P B Y hS hIn
  · rw [zipLenMA_of_nonneg ht.le, ← zipLenA_of_nonneg ht.le]
    exact g4PosLawAStmt_of_down hX1
      (g4RoundRawAStmt_of_down (g4ZipRegA0_of (g4DriverPushSep0Stmt_of_rep0 hSep0) (g4UpWeldCoreAStmt_of_X1 hX1)) hD) hD γ P B Y hS hIn hE6 hEq
      t ht

end ASep
end QuantumZipper
