import QuantumZipper.Proofs.Thm18.ASepD84Wire
import QuantumZipper.Proofs.Thm18.RT5OMain
import QuantumZipper.Proofs.Thm18.RT5FarGeo
import QuantumZipper.Proofs.Thm18.R18RTZipMain
import QuantumZipper.Proofs.Thm18.R18RTMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-MO: RT5 (D86 + D87 form) from the `τ' = 0` A-sep leaf

Verbatim copies of `R18.rt5FarPullStmt_holds` (RT5FarMain.lean), `R18.g4RoundDownOMStmt_of_far`
(RT5OMain.lean) and `R18.g4RoundDownOMStmt_holds` (RT5OFinal.lean) with `G4Core.G4SepRepStmt`
replaced by the weaker `ASep.G4SepRep0Stmt` (D84): A-sep enters only through `g4RoundDownA_of`,
i.e. at `τ' = 0` (`ASep.g4RoundDownA0_of`). Result: **`g4RoundDownOMStmt_holds0`**. Sources as in
the originals (Sheffield, arXiv:1012.4797, Theorem 1.8 (1), p. 26). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core Thm18Asm.G1ZA1c LocLen D3Plus R18

/-- FarPull from the `τ' = 0` leaf. -/
theorem rt5FarPullStmt_holds0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt) :
    Rt5FarPullStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  have hA : G4DriverPushSep0Stmt := g4DriverPushSep0Stmt_of_rep0 hSep0
  have hU := g4UpWeldCoreAStmt_of_X1 hX1
  have hD := g4RoundDownA0_of hA hU γ P B Y hS hIn hE6 hEq ℓ hℓ
  have hκ : 0 < γ ^ 2 := by have := hS.1; positivity
  have hκ4 : γ ^ 2 < 4 := by have := hS.1; have := hS.2.1; nlinarith
  filter_upwards [hD, hU γ P B Y hS hIn hE6 hEq ℓ hℓ, hIn.2.2,
    RS.ae_radialGood_drive hS.2.2.1 hκ (by linarith), D74.ae_wedgeConfig_snd_good hS,
    rt5_ae_zipScale_pos hX1 hS hIn hℓ] with ω hD hu hin hRG hgood hpos
  set c := wedgeAConfig γ B Y ω with hcdef
  set t := lenTimeOpen γ ℓ c.toPair with htdef
  set b := areaScale (zipCapDownA γ t c).area with hbdef
  obtain ⟨hb, ht, hz, hwe⟩ := hu
  have hc : Continuous c.drv := hgood.1
  have hc0 : c.drv 0 = 0 := hgood.2
  have hq : IsLenWeldingDriver γ (zipLenDownA γ ℓ c).fld ℓ (revDrv c.drv t b) := by
    refine ⟨by simp only [revDrv]; positivity, by simp only [revDrv]; fun_prop,
      by simp [revDrv], Or.inr ?_, hz, hwe⟩
    exact isSimpleCurveHull_revDrv hc hc0 ht hb hin.1 (hin.2.1 _ ht.le)
  have hspec := lenWeldDriver_spec ⟨_, hq⟩
  set A' := zipLenDownA γ ℓ c with hA'def
  set p := lenWeldDriver γ A'.fld ℓ with hpdef
  have hzA : zipLenA γ ℓ = zipLenUpA γ ℓ := by simp [zipLenA, hℓ.le]
  rw [hzA] at hD
  obtain ⟨-, hDdrv⟩ := hD
  intro d k hoff
  exact rt5far_geo (W := c.drv) (W' := p.2) (T := p.1) (s := t) (b := b) hRG hin.1.2.2.1
    hin.1.2.2.2.1 hin.2.1 ht.le hb hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 hpos
    (fun u hu => hDdrv u hu) d k hoff

/-- RT5 (D86 + D87 form) from the `τ' = 0` leaf and FarPull. -/
theorem g4RoundDownOMStmt_of_far0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hCore : MaskPullCoreStmt) (hFar : Rt5FarPullStmt) : G4RoundDownOMStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  have hA : G4DriverPushSep0Stmt := g4DriverPushSep0Stmt_of_rep0 hSep0
  have hD := g4RoundDownA0_of hA (g4UpWeldCoreAStmt_of_X1 hX1) γ P B Y hS hIn hE6 hEq ℓ hℓ
  filter_upwards [hD, maskExactFull_of_pullCore hCore γ P B Y hS hIn ℓ hℓ,
    hFar γ P B Y hS hIn ℓ hℓ, rt5_ae_zipScale_pos hX1 hS hIn hℓ,
    ae_lenWeldDriverO_offConfig_zipLenDownA hX1 hS hIn hℓ, ae_zipLenDownA_area_eq hS hIn ℓ,
    D74.ae_wedgeConfig_snd_good hS] with ω hD hoff hfarG hpos hpO harea hω
  set c₀ := wedgeAConfig γ B Y ω with hc₀
  set A' := zipLenDownA γ ℓ c₀ with hA'def
  -- the pieces of `Z_{−ℓ}^{pieces} c₀` are those of `Z_{−ℓ} c₀` (RT2)
  have hpc : offConfig γ (zipLenDownMA γ ℓ c₀) = offConfig γ A' := by
    unfold offConfig
    rw [hoff]
  rw [hpc]
  have hzA : zipLenA γ ℓ = zipLenUpA γ ℓ := by simp [zipLenA, hℓ.le]
  rw [hzA] at hD
  obtain ⟨hDreg, hDdrv⟩ := hD
  have hd := zipLenDownA_drv_good (γ := γ) (ℓ := ℓ) (c := c₀) hω.1
  have hdrv : (offConfig γ A').drv = A'.drv := offConfig_drv_canon γ _
  have har : (offConfig γ A').area = A'.area := harea.symm
  obtain ⟨hfld, hdrvU⟩ := rt5o_zipLenUpOA_congr (hpO ℓ) hdrv har
    (regEqOff_offConfig γ hd.1 hd.2) ⟨hpos, hfarG⟩
  have hcur : curveOf (zipLenUpA γ ℓ A').drv = curveOf c₀.drv := curveOf_congr hDdrv
  refine ⟨?_, fun u hu => ?_⟩
  · show RegEqOff (curveOf c₀.drv) (zipLenUpOA γ ℓ (offConfig γ A')).fld c₀.fld
    rw [← hcur]
    refine rt5_regEqOff_trans hfld ?_
    rw [hcur]
    exact hDreg
  · show (zipLenUpOA γ ℓ (offConfig γ A')).drv u = c₀.drv u
    rw [hdrvU]
    exact hDdrv u hu

/-- **RT5, D86 + D87 form, from the `τ' = 0` A-sep leaf** (copy of `R18.g4RoundDownOMStmt_holds`). -/
theorem g4RoundDownOMStmt_holds0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : G4SepRep0Stmt)
    (hCore : MaskPullCoreStmt) : G4RoundDownOMStmt :=
  g4RoundDownOMStmt_of_far0 hX1 hSep0 hCore (rt5FarPullStmt_holds0 hX1 hSep0)

end ASep
end QuantumZipper
