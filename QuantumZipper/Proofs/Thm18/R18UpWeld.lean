import QuantumZipper.Proofs.Thm18.R18UpWeldDet
import QuantumZipper.Proofs.Thm18.R18G1ArcLenDet
import QuantumZipper.Proofs.Thm18.R18G1ArcWire
import QuantumZipper.Proofs.Thm18.G1ZA1cMain
import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Thm18.R18RoundDownWire
import QuantumZipper.Proofs.Thm18.G4BSidePos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T7c: `R18.G4UpWeldCoreAStmt` from X1

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
the inverse of `Z^LEN_{−ℓ}` is given by conformal welding by quantum length. Open-arc copy of
`Thm18Asm.g4UpWeldCoreStmt_of_unzip` (G4Rezip2Hom.lean:204) under the substitution rule of
`handoff/FOLLOW-PAPER-13.md` §1, through the deterministic `R18.weldCoreA_det`
(R18UpWeldDet.lean). Inputs, all from X1 (as in `R18.g1RerootLenArcStmt_of`, R18G1ArcLen.lean):
* `t' > 0`, `a > 0`: `R5c.HitScaleZipArc`; no overshoot: `leftTimeArc_of_eq` from strict
  monotonicity and surjectivity of the open-arc left length;
* goodness of the unzipped field off `{O⁻_{t'}, 0, O⁺_{t'}}`: `PStarGoodOffAllStmt`;
* the open-arc pair cocycle, finiteness, capacity field cocycle (`pStarCapRegOff_of_yMergeOffTip`);
* global goodness, no atoms and positivity (`BReg`) of the NEW field `(Z_{−ℓ} c).1`, transferred
  from the wedge by E6 (`e6Arc_thm18`), exactly as in `R18.g1RerootLenArcStmt_of`;
* the area scale equals the field's own scale (`areaScale_zipCapDownA_eq`, `unzipArea_holds`) and
  a.s. `(Z_{−ℓ} c).toPair = zipLenDownArc` (`ae_toPair_zipLenDownA_eq`).
Wiring and own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G1ZA1c LocLen D3Plus

/-- **T7c: the welding core of `Z_ℓ ∘ Z_{−ℓ}`, area-carrying/open-arc form, from X1.** -/
theorem g4UpWeldCoreAStmt_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : G4UpWeldCoreAStmt := by
  intro γ Ω _ P _ B Y hS hIn _ hEq ℓ hℓ
  have hγ : 0 < γ := hS.1
  have hE6 := e6StmtArc_of_X1 hX1
  have hum := unzipMeasArc_of_X1 hX1
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  have hI : R5c.PStarLenInfArcStmt :=
    R5c.pStarLenInfArc_of (F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds)
      (pStarZipLenInputsLoc_of_yMergeOffTip hYO) R5c.lenReadTimeArc_holds hsm
      (pStarGoodOffAll_of_yMergeOffTip hYO) (unzipBdryPosArc_of_yMergeOffTip hYO) hF
  have hsurj : LenLeftSurjArcStmt :=
    lenLeftSurjArc_of_reg (lenLeftRegArc_of_yMergeOffTip hYO hC hF)
      (lenLeftUnbddArc_of_pStarLenInf hI) hC hF
  have hSZ := R5c.hitScaleZipArcStmt_of_nodes hsm hF (pStarAreaAll_of_yMergeOffTip hYO)
  have hP := isPStarSample_of_setting hS
  have hsm' := hsm (γ ^ 2) P Y B hP
  have hsurj' := hsurj (γ ^ 2) P Y B hP
  have hSZ' := hSZ (γ ^ 2) P Y B hP ℓ hℓ
  have hGO := pStarGoodOffAll_of_yMergeOffTip hYO (γ ^ 2) P Y B hP
  have hC' := hC (γ ^ 2) P Y B hP
  have hfin' := ae_unzipLengthsArc_lt_top_all hC hF (γ ^ 2) P Y B hP
  have hcap' := pStarCapRegOff_of_yMergeOffTip hYO (γ ^ 2) P Y B hP
  rw [Real.sqrt_sq hγ.le] at hsm' hsurj' hSZ' hGO hC' hfin' hcap'
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => zipLenDownArc γ ℓ (c ω) with hc'
  -- global regularity of the new field, transferred from the wedge by E6 (as in A1c)
  have hpath : AEMeasurable (fun ω => fun t : ℝ≥0 => (c ω).2 t) P := by
    have hm : Measurable fun a : ℝ≥0 → ℝ => fun t : ℝ≥0 =>
        Real.sqrt (γ ^ 2) * a ((t : ℝ).toNNReal) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _
    exact hm.comp_aemeasurable (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1)
  have hmc : AEMeasurable (fun ω => g1zCfgData (c ω)) P := hIn.2.1.prodMk hpath
  have hmc' : AEMeasurable (fun ω => g1zCfgData (c' ω)) P :=
    aemeasurable_cfgData_zipLenDownArc hum hS hℓ
  have hlaw : P.map (fun ω => g1zCfgData (c' ω)) = P.map (fun ω => g1zCfgData (c ω)) :=
    e6Arc_thm18 hE6 hS ℓ hℓ
  have hBY : ∀ᵐ ω ∂P, WedgeBdry.BReg γ (Y ω) := by
    filter_upwards [hIn.1, ae_atomless_pos_wedge hS hIn] with ω h1 h2
    exact WedgeBdry.bReg_of h1.1 h2.1 h2.2
  have hflaw : fieldLawFull H (fun ω => (c' ω).1) P = fieldLawFull H Y P := by
    have e1 : fieldLawFull H (fun ω => (c' ω).1) P =
        (P.map fun ω => g1zCfgData (c' ω)).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hmc').symm
    have e2 : fieldLawFull H Y P = (P.map fun ω => g1zCfgData (c ω)).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hmc).symm
    rw [e1, e2, hlaw]
  have hB' : ∀ᵐ ω ∂P, WedgeBdry.BReg γ (c' ω).1 :=
    WedgeBdry.ae_of_fieldLawFull_eq hflaw hmc'.fst hIn.2.1 (WedgeBdry.BReg γ)
      (WedgeBdry.measurableSet_bReg γ) (WedgeBdry.bReg_reconstruct γ) hBY
  filter_upwards [hSZ', hsm', hsurj', hGO, hEq, hB', hC', hfin', hcap',
    ae_pstar_zeroMinus_facts hP, G4Core.ae_zeroPlus_facts hS, G4Core.ae_sideImages_zipCapDown hS,
    ae_toPair_zipLenDownA_eq hS ℓ, unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS,
    hIn.2.2] with ω hz hm hsu hgo heq hBω hcoc hf hcp hzm hzp hsi htp hA hω hin
  have ht : 0 < lenTimeArc γ ℓ (c ω) := hz.pos
  have ha : 0 < scaleParam γ (unzippedField γ (c ω) (lenTimeArc γ ℓ (c ω))) := hz.scale
  obtain ⟨t, ht0, htl⟩ := hsu ℓ hℓ
  have hpass : (unzipLengthsArc γ (c ω) (lenTimeArc γ ℓ (c ω))).1 = ENNReal.ofReal ℓ := by
    have e : lenTimeArc γ ℓ (c ω) = t := leftTimeArc_of_eq (c := c ω) hm ht0 htl
    rw [e]; exact htl
  obtain ⟨hxr, ⟨ν', hν'⟩, -⟩ := hgo _ ht.le
  obtain ⟨-, hanti, -, hO, -⟩ := hzm _ ht
  obtain ⟨-, hmono, -, hOp⟩ := hzp _ ht
  have hsc : areaScale (zipCapDownA γ (lenTimeOpen γ ℓ (wedgeAConfig γ B Y ω).toPair)
      (wedgeAConfig γ B Y ω)).area =
      scaleParam γ (unzippedField γ (c ω) (lenTimeArc γ ℓ (c ω))) :=
    areaScale_zipCapDownA_eq hω.1 hω.2 (lenTimeOpen_nonneg _ _ _) fun S hSm hSH =>
      hA _ (lenTimeOpen_nonneg _ _ _) S hSm hSH
  have hfld : (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld = (c' ω).1 :=
    congrArg Prod.fst htp
  have hK : IsSimpleCurveHull (revHull
      (revDrv (c ω).2 (lenTimeArc γ ℓ (c ω))
        (scaleParam γ (unzippedField γ (c ω) (lenTimeArc γ ℓ (c ω))))).2
      (revDrv (c ω).2 (lenTimeArc γ ℓ (c ω))
        (scaleParam γ (unzippedField γ (c ω) (lenTimeArc γ ℓ (c ω))))).1) :=
    isSimpleCurveHull_revDrv hω.1 hω.2 ht ha hin.1 (hin.2.1 _ ht.le)
  have hdet := weldCoreA_det (ℓ := ℓ) hγ ht ha hω.1 hω.2 hK hxr hν' hBω hpass hcoc
    (fun s hs => (hf s hs).1) heq hcp hanti hO hmono hOp fun r hr => hsi _ r hr
  unfold RoundUpWeldCoreAData upDrvA
  rw [hsc, hfld]
  exact ⟨ha, ht, hdet.1, hdet.2⟩

end R18
end QuantumZipper
