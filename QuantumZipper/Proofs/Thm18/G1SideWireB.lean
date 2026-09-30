import QuantumZipper.Proofs.Thm18.G1SideWireA
import QuantumZipper.Proofs.Thm18.R18G1ArcWire
import QuantumZipper.Proofs.Thm18.R18G1ArcReg
import QuantumZipper.Proofs.Thm18.R18G1ArcLenDet
import QuantumZipper.Proofs.Thm18.G1ZA1cMain
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1Z2MeasRep
import QuantumZipper.Proofs.Thm18.G1Z5Id
import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.G1ZZ1Main
import QuantumZipper.Proofs.Thm18.G1ZoomNodes
import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.JordanChordA1a
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3
import QuantumZipper.Proofs.Thm18.R18G1ArcWire
import QuantumZipper.Proofs.Thm18.R18G1ArcReg
import QuantumZipper.Proofs.Thm18.R18G1ArcLenDet
import QuantumZipper.Proofs.Thm18.G1ZA1cMain
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1Z2MeasRep
import QuantumZipper.Proofs.Thm18.G1Z5Id
import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.G1ZZ1Main
import QuantumZipper.Proofs.Thm18.G1ZoomNodes
import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.JordanChordA1a
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3
import QuantumZipper.Proofs.Thm18.R18E6A
import QuantumZipper.Proofs.Thm18.R18Zero
import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Thm18.R18RoundRaw
import QuantumZipper.Proofs.Zipper.Thm13FromFieldLawler
import QuantumZipper.Proofs.Thm18.R18RoundUpDet
import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Wire4
import QuantumZipper.Proofs.Zipper.WedgeLawReg
import QuantumZipper.Proofs.Zipper.AreaWinTransfer
import QuantumZipper.Proofs.Thm18.R18UpWeld
import QuantumZipper.Proofs.Thm18.G4ASepLog
import QuantumZipper.Proofs.Thm18.G4ASepBackLog
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G4ASepDefs
import QuantumZipper.Proofs.Thm18.G4WeldUniq
import QuantumZipper.Proofs.Thm18.G4WeldRem
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.Thm18.R18DownTime
import QuantumZipper.Proofs.Thm18.R18T4bWeld
import QuantumZipper.Proofs.Thm18.R18ZipReg
import QuantumZipper.Proofs.Thm18.R18ZipFacMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE wiring (D83), part B: the Theorem 1.8 headline from `G1Z4SideLimSelStmt`

Copies (suffix `_sel`) of `R18.g1RerootLenArcStmt_of` (R18G1ArcLen.lean) and `R18.g1Stmt_of_arc`
(R18G1Arc.lean), and `R18.theorem1_8Paper_of_frontier7`, which is
`R18.theorem1_8Paper_of_frontier6` (R18ZipFacHead.lean) with the side-limit node at the selected
side maps (`Thm18Asm.G1Z4SideLimSelStmt`, decision D83) in place of `G1Z4SideLimPathStmt`, all
other hypotheses identical. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G1ZA1c LocLen D3Plus

/-- **A1c with open arcs** from X1 and the per-path side-limit node `G1Z4SideLimSelStmt`. -/
theorem g1RerootLenArcStmt_of_sel (hX1 : BaseFin.BaseFiniteStmt) (hN : G1Z4SideLimSelStmt) :
    G1RerootLenArcStmt := by
  intro γ Ω _ P _ B Y hS hIn hEq ℓ hℓ left
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
  rw [Real.sqrt_sq hγ.le] at hsm' hsurj' hSZ' hGO
  obtain ⟨E, hEm, hEg, hEae⟩ :=
    g1zA1c_ae_mem_sel hN G1RC.g1RegRepRC2Stmt_holds g1RegRepRestStmt_holds hS hIn
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => zipLenDownArc γ ℓ (c ω) with hc'
  set F := cfgPath γ ⁻¹' E with hF
  have hFm : MeasurableSet F := measurable_cfgPath γ hEm
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
  have hFc : ∀ᵐ ω ∂P, g1zCfgData (c ω) ∈ F := by
    filter_upwards [hEae] with ω h
    show cfgPath γ (g1zCfgData (c ω)) ∈ E
    convert h using 2
    funext t
    simp only [cfgPath, g1zCfgData, hc, wedgeConfig, drive, pathOf, Real.toNNReal_coe,
      Real.sqrt_sq hγ.le]
    field_simp
    rfl
  have hFc' : ∀ᵐ ω ∂P, g1zCfgData (c' ω) ∈ F := by
    have h : ∀ᵐ p ∂(P.map fun ω => g1zCfgData (c ω)), p ∈ F := (ae_map_iff hmc hFm).2 hFc
    rw [← hlaw] at h
    exact (ae_map_iff hmc' hFm).1 h
  -- boundary regularity of the new field, transferred from the wedge by E6
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
  filter_upwards [hSZ', hsm', hsurj', hGO, hEq, hFc', hB', ae_g1zDrvGood hS hIn]
    with ω hz hm hsu hgo heq hFω hBω hW
  have ht : 0 < lenTimeArc γ ℓ (c ω) := hz.pos
  have ha : 0 < unzipScaleArc γ ℓ (c ω) := hz.scale
  refine ⟨ht, ha, fun β hβ hlim => ?_⟩
  have hW' : G1zDrvGood (c' ω).2 :=
    (G1ZA1a.g1RerootAffineStmt_holds _ hW _ _ ht ha left).1
  have hdrv : pathDrive (γ ^ 2) (cfgPath γ (g1zCfgData (c' ω))).1 = (c' ω).2 :=
    pathDrive_cfgPath hγ hW'.2.2.1 _
  have hcont : Continuous (cfgPath γ (g1zCfgData (c' ω))).1 :=
    show Continuous (fun t : ℝ≥0 => (c' ω).2 t / γ) from
      (hW'.1.comp NNReal.continuous_coe).div_const γ
  have hsimple : IsSimpleChord (pathTrace (γ ^ 2) (cfgPath γ (g1zCfgData (c' ω))).1) := by
    show IsSimpleChord (trace (pathDrive (γ ^ 2) (cfgPath γ (g1zCfgData (c' ω))).1))
    rw [hdrv]; exact hW'.2.2.2.1
  obtain ⟨Φ, hR, hν⟩ := hEg _ hFω hcont hsimple (c' ω).1 rfl left
  rw [hdrv] at hR hν
  have hsf : g1CfgSideField γ left (c' ω) = g1CfgSideField γ left ((c' ω).1, (c' ω).2) := rfl
  rw [hsf, hν]
  refine ⟨?_, fun u v huv hsub => g1zA1c_pos (fun u v h => hBω.pos h) hR.1 huv hsub⟩
  -- no overshoot at the first passage (strict monotonicity + surjectivity)
  obtain ⟨t, ht0, htl⟩ := hsu ℓ hℓ
  have hpass : (unzipLengthsArc γ (c ω) (lenTimeArc γ ℓ (c ω))).1 = ENNReal.ofReal ℓ := by
    have e : lenTimeArc γ ℓ (c ω) = t := leftTimeArc_of_eq (c := c ω) hm ht0 htl
    rw [e]; exact htl
  -- goodness of the unzipped field off `{O⁻_{t'}, 0, O⁺_{t'}}`
  obtain ⟨hxr, ⟨ν', hν'⟩, -⟩ := hgo _ ht.le
  have hs1 := sideImages_fst_nonpos_of_cont hW.1 hW.2.1 ht.le
  have hs2 := sideImages_snd_nonneg_of_cont hW.1 hW.2.1 ht.le
  have heq' := heq _ ht.le
  rw [unzipLengthsOpen_eq] at heq'
  cases left
  · have hU : (if false = true then Ioo (g1zSideImage false (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (c ω))) 0 else Ioo 0 (g1zSideImage false (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (c ω)))) ⊆ (LocLen.offSet (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (c ω)))ᶜ :=
      fun u hu hmem => Set.disjoint_left.1 (Ioo_right_disjoint_offSet _ _ hs1) hu hmem
    have hseg := g1zA1cArc_seg (x := unzippedField γ (c ω) (lenTimeArc γ ℓ (c ω))) hγ hxr hν'
      ha hBω.1 (fun t => hBω.noAtom t) hR hβ hlim hU
    refine hseg.trans ?_
    show (unzipLengthsArc γ (c ω) (lenTimeArc γ ℓ (c ω))).2 = _
    rw [← heq', hpass]
  · have hU : (if true = true then Ioo (g1zSideImage true (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (c ω))) 0 else Ioo 0 (g1zSideImage true (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (c ω)))) ⊆ (LocLen.offSet (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (c ω)))ᶜ :=
      fun u hu hmem => Set.disjoint_left.1 (Ioo_left_disjoint_offSet _ _ hs2) hu hmem
    have hseg := g1zA1cArc_seg (x := unzippedField γ (c ω) (lenTimeArc γ ℓ (c ω))) hγ hxr hν'
      ha hBω.1 (fun t => hBω.noAtom t) hR hβ hlim hU
    refine hseg.trans ?_
    show (unzipLengthsArc γ (c ω) (lenTimeArc γ ℓ (c ω))).1 = _
    exact hpass

end R18
end QuantumZipper
