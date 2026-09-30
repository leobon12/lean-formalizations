import QuantumZipper.Proofs.Thm18.Top18
import QuantumZipper.Proofs.Thm18.ASepMO2
import QuantumZipper.Proofs.Thm18.ASepD84Wire
import QuantumZipper.Proofs.Thm18.ASepTr1
import QuantumZipper.Proofs.Thm18.DrvGoodMain
import QuantumZipper.Proofs.Thm18.A1RNodes
import QuantumZipper.Proofs.Thm18.A1RMass
import QuantumZipper.Proofs.Thm18.G1SSR2UC
import QuantumZipper.Proofs.Thm18.G1TopMain
import QuantumZipper.Proofs.Thm18.G1Side3Top
import QuantumZipper.Proofs.Thm18.G1Side3Tr
import QuantumZipper.Proofs.Thm18.RTMeas3Zero
import QuantumZipper.Proofs.Thm18.G3Pl3Pair
import QuantumZipper.Proofs.Section5.Prop17PalmZoomScale
import QuantumZipper.Proofs.Thm18.G3Pl3Fam
import QuantumZipper.Proofs.Thm18.G1SSR2Free
import QuantumZipper.Proofs.Thm18.RT6bPair
import QuantumZipper.Proofs.Thm18.RT6bUnzGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WIRE18: the paper-form Theorem 1.8 from its genuinely open leaves (wiring only)

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26), in the D87 form `R18.theorem1_8PaperMO`
(RT6MODefs.lean). Assembly: the body of `ASep.theorem1_8PaperMO_of_frontier130` (ASepMO2.lean,
`τ' = 0` A-sep leaf) with G1 from `top18_g1Stmt` and G3 as in `top18_g3PaperStmt` (Top18.lean) but with (G-b)
from `g3TWedgePlainStmt_of_unscaledCmp`,
every proved node discharged:

* X1 from `FieldLawler.fieldLawlerReturn_holds`;
* Z2 goodness from the side area (`g1Z2SideGoodStmt_of_area`, `g1Z2SideAreaStmt_of_sel`,
  `g1Z2SideAreaSelStmt_of_top`, `G1Top.g1Z2SideTopSelStmt_holds`); A2 from it
  (`g1RerootFactorStmt_of_good`); D89 shifted regularity (`g1SideShiftRegAStmt_of_good`);
* A1b from the cut-off (`g1A1b2SideTendstoStmt_of_cut a1rMassStmt_holds`,
  `g1ZA1bSideExactArcStmt_of_tendsto`);
* round trip: `zipOffExactAStmt_of_good` with the zipped-driver goodness on the `τ' = 0` leaf
  (`zipGoodStmt_holds0` below: verbatim copy of `zipGoodStmt_holds`, DrvGoodMain.lean, with
  `g4RoundDownA_of` replaced by `ASep.g4RoundDownA0_of`), `unzDriverGoodStmt_of_radial` with
  `unzRadialGoodStmt_holds`, `RTMeas.upPiecesReadStmt_holds`;
* A-sep: `ASep.g4SepRep0Stmt_of_iter hGC (ASep.g4SepIter0Stmt_of_path hP)`.

Open leaves (7) and owners:
* `A1RGrowthStmt`, `A1RFarStmt` (A1b cut-off: log growth near ℝ, smoothing limit; A1R prover),
* `G1WedgePalmZoomStmt` (G1 Palm zoom; G1 prover),
* `G3TCurveStmt` (G3 step 5T (G-a); G3T prover),
* `G3PlPhiUnscaledStmt` (G3 Palm windows, unscaled comparison, G3Pl3Red.lean; G3Pl prover;
  (G-b) by `g3TWedgePlainStmt_of_unscaledCmp`, G3Pl3Free.lean),
* `ASep.G4SepPath0Stmt`, `ASep.GoodCMeasStmt` (A-sep at `τ' = 0`; ASEP prover).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

section ZipGood0

open DrvGood

/-- `ae_goodSet_zipPos` (DrvGoodMain.lean) on the `τ' = 0` A-sep leaf. -/
theorem ae_goodSet_zipPos0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : ASep.G4SepRep0Stmt)
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y)
    (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, (fun t : ℝ≥0 => (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv t) ∈ goodSet := by
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  obtain ⟨Φ, hΦ, hZc, hZy⟩ := g4ZipFactorFullAStmt_of_X1 hX1 γ P B Y hS hIn hE6 hEq ℓ hℓ
  have hD := ASep.g4RoundDownA0_of (ASep.g4DriverPushSep0Stmt_of_rep0 hSep0)
    (g4UpWeldCoreAStmt_of_X1 hX1) γ P B Y hS hIn hE6 hEq ℓ hℓ
  have hA : MeasurableSet {d : E6.FullData | (Φ d).2 ∈ goodSet} :=
    measurableSet_goodSet.preimage (measurable_snd.comp hΦ)
  have hy : ∀ᵐ ω ∂P, cfgData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair ∈
      {d : E6.FullData | (Φ d).2 ∈ goodSet} := by
    filter_upwards [hZy, hD, ae_goodSet_wedge hS] with ω e1 e2 e3
    show (Φ _).2 ∈ goodSet
    rw [← e1]
    have e : (offData (zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).toPair).2 =
        fun t : ℝ≥0 => (wedgeAConfig γ B Y ω).drv t := funext fun t => e2.2 t t.2
    rw [e]; exact e3
  have hc := Cor15Group.ae_mem_of_map_eq (e := fun x : AreaConfig => cfgData x.toPair)
    (c := wedgeAConfig γ B Y) (y := fun ω => zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)) hA
    (aemeasurable_cfgData_wedgeConfig hS hIn) (aemeasurable_cfgData_zipLenDownA hX1 hS hℓ)
    (map_cfgData_zipLenDownA hX1 hS hℓ).symm hy
  filter_upwards [hc, hZc] with ω h1 h2
  have h3 : (Φ (cfgData (wedgeAConfig γ B Y ω).toPair)).2 ∈ goodSet := h1
  rw [← h2, zipLenA_of_nonneg hℓ.le] at h3
  exact h3

/-- `zipGoodStmt_holds` (DrvGoodMain.lean) on the `τ' = 0` A-sep leaf (verbatim copy). -/
theorem zipGoodStmt_holds0 (hX1 : BaseFin.BaseFiniteStmt) (hSep0 : ASep.G4SepRep0Stmt) :
    ZipGoodStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  have hex : ∀ᵐ ω ∂P, ∃ p, IsLenWeldingDriver γ (Y ω) ℓ p := by
    rcases hℓ.lt_or_eq with h | h
    · have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
      have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
      exact (g4WeldAStmt_holds hX1 γ P B Y hS hIn hE6 hEq ℓ h).mono fun ω hw => hw.1
    · subst h
      exact ae_of_all _ fun ω => ⟨_, isLenWeldingDriver_zero_zero γ _⟩
  have hpath : ∀ᵐ ω ∂P,
      (fun t : ℝ≥0 => (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv t) ∈ goodSet := by
    rcases hℓ.lt_or_eq with h | h
    · exact ae_goodSet_zipPos0 hX1 hSep0 hS hIn h
    · subst h; exact ae_goodSet_zipZero hS
  filter_upwards [hex, hpath, D74.ae_wedgeConfig_snd_good hS, ae_areaAll_wedgeA hS]
    with ω hx hg hω hAr
  have hp := lenWeldDriver_spec hx
  have hc := continuous_zipLenUpA_drv (γ := γ) (ℓ := ℓ) (c := wedgeAConfig γ B Y ω) hω.1 hω.2 hp
  have hc0 : (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv 0 = 0 := by
    have hT : ¬ (lenWeldDriver γ (wedgeAConfig γ B Y ω).fld ℓ).1 < 0 := not_lt.2 hp.1
    simp only [zipLenUpA, canonAConfig, zipWeldUpA, AreaConfig.toPair, rt5V_zipWeldUp, rt5V]
    simp [hT]
  have hmax : ∀ r, (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv r =
      (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).drv (max r 0) := fun r => by
    simp only [zipLenUpA, canonAConfig]
    rw [max_eq_left (le_max_right r 0)]
  obtain ⟨hRG, hinj, hH, hhull⟩ := good_spec hc hc0 (by rw [← pW_eq hc hc0 hmax]; exact hg)
  obtain ⟨h1, h2⟩ := areaAll_map_revMap hp.2.1 hp.1 hAr.1 hAr.2
  exact ⟨areaScale_pos_of_area h1 h2, hRG, hinj, hH, hhull⟩

end ZipGood0

end R18
end QuantumZipper
