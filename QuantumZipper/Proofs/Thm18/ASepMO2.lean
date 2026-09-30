import QuantumZipper.Proofs.Thm18.ASepMO1
import QuantumZipper.Proofs.Thm18.ASepRT1
import QuantumZipper.Proofs.Thm18.RT6MOGroup
import QuantumZipper.Proofs.Thm18.RT6NegEx
import QuantumZipper.Proofs.Thm18.RT6MOTrans
import QuantumZipper.Proofs.Thm18.RT6MOTrans3
import QuantumZipper.Proofs.Thm18.R18RTLaw
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
import QuantumZipper.Proofs.Thm18.R18RTMeasDrv
import QuantumZipper.Proofs.Thm18.R18RTMask
import QuantumZipper.Proofs.Thm18.R18RTCore
import QuantumZipper.Proofs.Thm18.RTBeurMain
import QuantumZipper.Proofs.Thm18.RTHmpMain
import QuantumZipper.Proofs.Thm18.RT6bGroup
import QuantumZipper.Proofs.Thm18.RT6bGrowth
import QuantumZipper.Proofs.Thm18.RTMeas2Area
import QuantumZipper.Proofs.Thm18.RTMeas2Len
import QuantumZipper.Proofs.Thm18.RT6MOTrans4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-MO (2): the D87 line (`theorem1_8PaperMO_of_frontier12/13`) on the `τ' = 0` A-sep leaf

Every consumer of `G4Core.G4SepRepStmt` on the D87 line (RT6MOTrans, RT6MOTrans3, RT6MOTrans4,
RT6MOHead, RT6bHead) uses it only through `rt5FarPullStmt_holds`, `ae_πd_offData_roundDown`,
`lawMA_of`, `g4RoundDownOMStmt_holds`, i.e. at `τ' = 0`. Verbatim copies with these replaced by
their `τ' = 0` versions (`ASep.*0`, ASepMO1/ASepRT1) and `hSepRep` by `G4SepRep0Stmt`; names get a
suffix `0`. Headlines: **`theorem1_8PaperMO_of_frontier120`**, **`theorem1_8PaperMO_of_frontier130`**.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core R18

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}

/-- **RT4 with its exact conclusion**: unzipping the pieces of `Z^A_ℓ c₀` gives back the masked
coordinates and driver of `c₀` (the proof of `g4RoundUpDownMAStmt_of`, Sheffield p. 26). -/
theorem rt6_ae_πd_roundUpDownA0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hMF : MaskExactFullAStmt) (hDM : DownDataMeasCStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, πd (offData (zipLenDownMA γ ℓ (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω))).toPair) =
      πd (offData (wedgeAConfig γ B Y ω).toPair) := by
  classical
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  obtain ⟨Φ, hΦm, hΦ0, hΦ1⟩ := g4ZipFactorFullAStmt_of_X1 hX1 γ P B Y hS hIn hE6 hEq ℓ hℓ
  obtain ⟨G, Dm, hGm, hDmm, hDmEq, hG0⟩ := hDM γ P B Y hS hIn ℓ hℓ
  obtain ⟨hM1, -⟩ := maskExactAStmt_of_full hMF γ P B Y hS hIn ℓ hℓ
  have hraw := ae_πd_offData_roundDown0 hX1 hSep0 hS hIn hℓ
  have hA := measurableSet_rtEvent hΦm hGm hDmm
  set c₀ := fun ω => wedgeAConfig γ B Y ω with hc₀
  have h1 : ∀ᵐ ω ∂P, cfgData (zipLenDownA γ ℓ (c₀ ω)).toPair ∈ RTEvent Φ G Dm := by
    filter_upwards [hΦ1, hraw, hG0, hM1, D74.ae_wedgeConfig_snd_good hS] with ω e1 e2 e3 e4 hg
    have hc1 := zipLenDownA_drv_good (γ := γ) (ℓ := ℓ) (c := c₀ ω) hg.1
    have hmask := D74.maskSel_cfgData (x := (zipLenDownA γ ℓ (c₀ ω)).toPair) hc1.1 hc1.2
    have hZ : πd (Φ (cfgData (zipLenDownA γ ℓ (c₀ ω)).toPair)) = πd (offData (c₀ ω).toPair) := by
      rw [← e1]; exact e2
    have hD : Dm (πd (Φ (cfgData (zipLenDownA γ ℓ (c₀ ω)).toPair))) =
        πd (offData (zipLenDownA γ ℓ (c₀ ω)).toPair) := by
      rw [hZ, hDmEq _ e3 (hg.1.comp continuous_subtype_val)]
      exact e4
    refine ⟨hZ ▸ e3, fun i => ?_, fun r => ?_⟩
    · rw [hD, hmask]; rfl
    · rw [hD]; rfl
  have hX0 : AEMeasurable (fun ω => cfgData (c₀ ω).toPair) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hX1' : AEMeasurable (fun ω => cfgData (zipLenDownA γ ℓ (c₀ ω)).toPair) P :=
    aemeasurable_cfgData_zipLenDownA hX1 hS hℓ
  have hlaw := map_cfgData_zipLenDownA hX1 hS hℓ (B := B) (Y := Y)
  have h0 : ∀ᵐ ω ∂P, cfgData (c₀ ω).toPair ∈ RTEvent Φ G Dm := by
    have h' : ∀ᵐ z ∂(P.map fun ω => cfgData (zipLenDownA γ ℓ (c₀ ω)).toPair),
        z ∈ RTEvent Φ G Dm := (ae_map_iff hX1' hA).2 h1
    rw [hlaw] at h'
    exact (ae_map_iff hX0 hA).1 h'
  have hW := g4WeldAStmt_holds hX1 γ P B Y hS hIn hE6 hEq ℓ hℓ
  filter_upwards [h0, hΦ0, hW, D74.ae_wedgeConfig_snd_good hS] with ω hev e0 hex hg
  obtain ⟨hGZ, hco, hdr⟩ := hev
  rw [e0.symm, zipLenA_of_nonneg hℓ.le] at hGZ hco hdr
  set Z := zipLenUpA γ ℓ (c₀ ω) with hZdef
  set R := zipLenDownMA γ ℓ Z with hRdef
  have hZc : Continuous Z.drv :=
    continuous_zipLenUpA_drv hg.1 hg.2 (lenWeldDriver_spec hex.1)
  have hDZ : Dm (πd (offData Z.toPair)) = πd (offData R.toPair) :=
    hDmEq _ hGZ (hZc.comp continuous_subtype_val)
  rw [hDZ] at hco hdr
  have hmask0 := D74.maskSel_cfgData (x := (c₀ ω).toPair) hg.1 hg.2
  rw [hmask0] at hco
  have hRc : Continuous R.drv :=
    (zipLenDownA_drv_good (γ := γ) (ℓ := ℓ) (c := configOfData γ (offData Z.toPair))
      (continuous_drvOfData_offData (x := Z.toPair) hZc)).1
  have hdrv : ∀ u : ℝ, 0 ≤ u → R.drv u = (c₀ ω).drv u :=
    eq_of_rat_max hRc hg.1 fun r => hdr r
  refine Prod.ext (funext fun i => hco i) (funext fun u => hdrv u u.2)

/-- **Deliverable 1: `Z_{−ℓ} ∘ Z_ℓ = id` for the zipper on the pieces** (D87), masked coordinates
and driver (Sheffield arXiv:1012.4797 p. 26). -/
theorem rt6_ae_roundUpDownMO0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hMF : MaskExactFullAStmt) (hDM : DownDataMeasCStmt) (hZO : ZipOffExactAStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, πd (offData (zipLenMO γ (-ℓ) (zipLenMO γ ℓ (wedgeAConfig γ B Y ω))).toPair) =
      πd (offData (wedgeAConfig γ B Y ω).toPair) := by
  filter_upwards [rt6_ae_πd_roundUpDownA0 hX1 hSep0 hMF hDM hS hIn hℓ,
    hZO γ P B Y hS hIn ℓ hℓ.le] with ω h1 h2
  rw [zipLenMO_of_neg (neg_lt_zero.2 hℓ), neg_neg, zipLenMO_of_nonneg hℓ.le, Function.comp_apply,
    zipLenDownMA_congr_offData h2]
  exact h1

/-- **Deliverable 2: `Z_ℓ ∘ Z_{−ℓ} = id` for the zipper on the pieces** (D87), masked coordinates
and driver (Sheffield arXiv:1012.4797 p. 26). -/
theorem rt6_ae_roundDownUpMO0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hMF : MaskExactFullAStmt) (hZU : ZipOffExactUnzAStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, πd (offData (zipLenMO γ ℓ (zipLenMO γ (-ℓ) (wedgeAConfig γ B Y ω))).toPair) =
      πd (offData (wedgeAConfig γ B Y ω).toPair) := by
  filter_upwards [hMF γ P B Y hS hIn ℓ hℓ, hZU γ P B Y hS hIn ℓ hℓ,
    ae_πd_offData_roundDown0 hX1 hSep0 hS hIn hℓ] with ω h1 h2 h3
  rw [zipLenMO_of_neg (neg_lt_zero.2 hℓ), neg_neg, zipLenMO_of_nonneg hℓ.le, Function.comp_apply]
  have e : offConfig γ (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)) =
      offConfig γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)) := by
    unfold offConfig; rw [h1]
  rw [e, h2, ← zipLenA_of_nonneg hℓ.le]
  exact h3

/-- **Deliverable 5: clause (3) for the zipper on the pieces** (D87). -/
theorem lawMO_of0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hMF : MaskExactFullAStmt) (hZO : ZipOffExactAStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (t : ℝ) :
    configLawOff (fun ω => (zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair) P =
      configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P := by
  by_cases ht : 0 ≤ t
  · have hA : ∀ᵐ ω ∂P, offData (zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair =
        offData (zipLenMA γ t (wedgeAConfig γ B Y ω)).toPair := by
      filter_upwards [hZO γ P B Y hS hIn t ht] with ω h
      rw [zipLenMO_of_nonneg ht, zipLenMA_of_nonneg ht, Function.comp_apply]
      exact h
    have e : configLawOff (fun ω => (zipLenMO γ t (wedgeAConfig γ B Y ω)).toPair) P =
        configLawOff (fun ω => (zipLenMA γ t (wedgeAConfig γ B Y ω)).toPair) P := by
      rw [configLawOff_eq_map_offData, configLawOff_eq_map_offData]
      exact Measure.map_congr hA
    rw [e]
    exact lawMA_of0 hX1 hSep0 hMF hS hIn t
  · have e : zipLenMO γ t = zipLenMA γ t := by
      rw [zipLenMO_of_neg (not_le.1 ht), zipLenMA_of_neg (not_le.1 ht)]
    rw [e]
    exact lawMA_of0 hX1 hSep0 hMF hS hIn t

/-- **Clause (1), D87 form, with the second round trip from RT5** (`g4RoundDownOMStmt_holds0`, D86 +
D87) instead of N2 (Sheffield arXiv:1012.4797 Theorem 1.8 (1), p. 26). -/
theorem rt6_clause1MO_core0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hCore : MaskPullCoreStmt) (hDM : DownDataMeasCStmt) (hZO : ZipOffExactAStmt)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
      (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
      qBoundaryMeasure γ (Y ω) (Set.Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ ∧
      (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
        p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s) ∧
      ConfigEqOff (zipLenDownMA γ ℓ (zipLenMO γ ℓ (wedgeAConfig γ B Y ω))).toPair
        (wedgeAConfig γ B Y ω).toPair ∧
      ConfigEqOff (zipLenMO γ ℓ (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω))).toPair
        (wedgeAConfig γ B Y ω).toPair := by
  intro ℓ hℓ
  have hMF := maskExactFull_of_pullCore hCore
  have hE := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  have e : zipLenDownMA γ ℓ = zipLenMO γ (-ℓ) := by
    rw [zipLenMO_of_neg (neg_lt_zero.2 hℓ), neg_neg]
  filter_upwards [g4WeldAStmt_holds hX1 γ P B Y hS hIn hE hEq ℓ hℓ,
    ae_lenWeldPoint_measure Wire4.wedgeLeftInfStmt hS hIn hℓ,
    rt6_ae_roundUpDownMO0 hX1 hSep0 hMF hDM hZO hS hIn hℓ,
    g4RoundDownOMStmt_holds0 hX1 hSep0 hCore γ P B Y hS hIn ℓ hℓ] with ω h1 h2 h3 h4
  refine ⟨h1.1, h2, h1.2, ?_, ?_⟩
  · rw [e]; exact rt6_configEqOff_of_πd h3
  · rw [zipLenMO_of_nonneg hℓ.le, Function.comp_apply]; exact h4

/-- **N2 proved**: at `c₁ = Z^A_{−ℓ} c₀`, zipping up the pieces and zipping up `c₁` give the same
masked coordinates and driver (Sheffield arXiv:1012.4797 p. 26). -/
theorem zipOffExactUnzAStmt_holds0 (hX1 : BaseFin.BaseFiniteStmt)
    (hSep0 : G4SepRep0Stmt) : ZipOffExactUnzAStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  filter_upwards [ae_lenWeldDriverO_offConfig_zipLenDownA hX1 hS hIn hℓ,
    ae_zipLenDownA_area_eq_and_good hS hIn ℓ, rt5FarPullStmt_holds0 hX1 hSep0 γ P B Y hS hIn ℓ hℓ,
    rt5_ae_zipScale_pos hX1 hS hIn hℓ, D74.ae_wedgeConfig_snd_good hS] with ω hp ha hgeo hpos hg
  have hd := zipLenDownA_drv_good (γ := γ) (ℓ := ℓ) (c := wedgeAConfig γ B Y ω) hg.1
  exact rt6_πd_zipLenUpOA_offConfig hd.1 hd.2 (hp ℓ) ha.1.symm ⟨hpos, hgeo⟩

/-- Law invariance, a.e.-measurability and continuity for `zipLenMO` from the D82 results and N1. -/
theorem moLawContStmt_of0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hMF : MaskExactFullAStmt) (hZO : ZipOffExactAStmt) : MOLawContStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ
  refine ⟨fun hℓ0 => ?_, lawMO_of0 hX1 hSep0 hMF hZO hS hIn ℓ,
    rt6_ae_contMO hX1 hZO hS hIn ℓ⟩
  rcases lt_or_gt_of_ne hℓ0 with hℓ | hℓ
  · have hℓ' : 0 < -ℓ := neg_pos.2 hℓ
    refine (D74.measurable_maskSel.comp_aemeasurable
      (aemeasurable_cfgData_zipLenDownA hX1 hS hℓ')).congr ?_
    filter_upwards [hMF γ P B Y hS hIn (-ℓ) hℓ', D74.ae_wedgeConfig_snd_good hS] with ω h hg
    have hc1 := zipLenDownA_drv_good (γ := γ) (ℓ := -ℓ) (c := wedgeAConfig γ B Y ω) hg.1
    show D74.maskSel (cfgData (zipLenDownA γ (-ℓ) (wedgeAConfig γ B Y ω)).toPair) =
      offData (zipLenMO γ ℓ (wedgeAConfig γ B Y ω)).toPair
    rw [zipLenMO_of_neg hℓ, h, D74.maskSel_cfgData hc1.1 hc1.2]
    rfl
  · have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
    have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
    obtain ⟨Φ, hΦm, hΦ0, -⟩ := g4ZipFactorFullAStmt_of_X1 hX1 γ P B Y hS hIn hE6 hEq ℓ hℓ
    refine (hΦm.comp_aemeasurable (aemeasurable_cfgData_wedgeConfig hS hIn)).congr ?_
    filter_upwards [hΦ0, hZO γ P B Y hS hIn ℓ hℓ.le] with ω e0 e1
    show Φ (cfgData (wedgeAConfig γ B Y ω).toPair) = _
    rw [zipLenMO_of_nonneg hℓ.le, Function.comp_apply, e1, ← zipLenA_of_nonneg hℓ.le, e0]

/-- The exact inverse identities and `Z_0 = id` for `zipLenMO` from the D82 results, N1 and N2. -/
theorem moInverseExactStmt_of0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hMF : MaskExactFullAStmt) (hDM : DownDataMeasCStmt) (hZO : ZipOffExactAStmt)
    (hZU : ZipOffExactUnzAStmt) : MOInverseExactStmt := by
  intro γ Ω _ P _ B Y hS hIn
  exact ⟨rt6_ae_zeroMO hZO hS hIn, fun ℓ hℓ =>
    ⟨rt6_ae_roundUpDownMO0 hX1 hSep0 hMF hDM hZO hS hIn hℓ,
      rt6_ae_roundDownUpMO0 hX1 hSep0 hMF hZU hS hIn hℓ⟩⟩

end ASep
end QuantumZipper
