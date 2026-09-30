import QuantumZipper.Proofs.Thm18.R18PosLaw
import QuantumZipper.Proofs.Thm18.R18E6A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T9: the measurability part of the reading node

The reading node `R18.G4ZipReadAStmt` (clause (3) of the paper-form Theorem 1.8 for `t > 0`,
`R18PosLaw.lean`) contains two a.e.-measurability conjuncts. Both are proved here: the masked data
is the measurable mask `D74.maskSel` of the full data; the full data of the wedge configuration is
a.e.-measurable (`aemeasurable_cfgData_wedgeConfig`), and a.s. the area-carrying unzipped
configuration is the open-arc one (proof of `R18.e6AStmt_of_X1`), whose full data is
a.e.-measurable (`LocLen.UnzipMeasArcStmt`, from X1). What remains is the factorization
`G4ZipFactorAStmt`. Wiring and own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- A.s. the area-carrying unzipping map is the open-arc field-normalized one (T3, T4). -/
theorem ae_toPair_zipLenDownA_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair =
      LocLen.zipLenDownArc γ ℓ (wedgeConfig γ B Y ω) := by
  filter_upwards [unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS] with ω hA hω
  refine toPair_zipLenDownA (areaScale_zipCapDownA_eq hω.1 hω.2
    (lenTimeOpen_nonneg _ _ _) fun S hSm hSH => ?_)
  exact hA _ (lenTimeOpen_nonneg _ _ _) S hSm hSH

/-- `LocLen.UnzipMeasArcStmt` from X1 (the chain of `R18.e6StmtArc_of_X1`). -/
theorem unzipMeasArcStmt_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : LocLen.UnzipMeasArcStmt := by
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  exact R5c.unzipMeasArc_of_hitScaleZip
    (R5c.hitScaleZipArcStmt_of_nodes hsm hF (pStarAreaAll_of_yMergeOffTip hYO))

theorem aemeasurable_offData_wedgeAConfig {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    AEMeasurable (fun ω => offData (wedgeAConfig γ B Y ω).toPair) P := by
  refine (D74.measurable_maskSel.comp_aemeasurable
    (aemeasurable_cfgData_wedgeConfig hS hIn)).congr ?_
  filter_upwards [D74.ae_wedgeConfig_snd_good hS] with ω hω
  exact D74.maskSel_cfgData hω.1 hω.2

end R18
end QuantumZipper
