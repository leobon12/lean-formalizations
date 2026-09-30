import QuantumZipper.Proofs.Thm18.R18RTRound
import QuantumZipper.Proofs.Thm18.R18ZipFacMain
import QuantumZipper.Proofs.Thm18.R18Zero
import QuantumZipper.Proofs.Thm18.R18ReadMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D82 RT7: clause (3) for the zipper acting on the pieces

Sheffield, arXiv:1012.4797, Theorem 1.8 (3), p. 26 (law invariance under `Z^LEN_t`), for the D82
maps `zipLenMA`:

* `t < 0`: unzipping the pieces has the same masked data as unzipping the configuration
  (`MaskExactFullAStmt`, RT2), whose law is the law of the configuration (E6, `e6AStmt_of_X1`);
* `t = 0`: `g4ZeroAStmt_holds`;
* `t > 0`: `zipLenMA t = zipLenUpA t` is the old zip; D81's transfer (`g4PosLawAStmt_of_full`)
  only uses the round trip `Z_ℓ ∘ Z_{−ℓ} = id` (T7b), so the round-trip node `G4RoundAStmt` is not
  needed (`g4PosLawAStmt_of_down`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-- **RT2, full form**: a.s. unzipping the pieces and unzipping the configuration give the same
masked data (all test functions at once). -/
def MaskExactFullAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
      offData (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)).toPair =
        offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair

theorem maskExactAStmt_of_full (h : MaskExactFullAStmt) : MaskExactAStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  have h' := h γ P B Y hS hIn ℓ hℓ
  refine ⟨?_, fun ρ => ?_⟩
  · filter_upwards [h'] with ω e
    rw [e]
  · filter_upwards [h'] with ω e
    rw [e]

/-- The raw masked round trip `Z_ℓ ∘ Z_{−ℓ}` from `G4ZipRegAStmt` and the second round trip only
(copy of `g4RoundRawAStmt_of_reg`, which uses only that conjunct of `G4RoundAStmt`). -/
theorem g4RoundRawAStmt_of_down (hZr : G4ZipRegAStmt) (hD : G4RoundDownAStmt) :
    G4RoundRawAStmt := by
  classical
  intro γ Ω _ P _ B Y hS hIn hE6 hEq t ht
  obtain ⟨hco, hpr⟩ := hZr γ P B Y hS hIn hE6 hEq t ht
  obtain ⟨hw, hwp⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  have hrt := hD γ P B Y hS hIn hE6 hEq t ht
  refine ⟨?_, fun ρ => ?_⟩
  · filter_upwards [hco, hw, hrt] with ω h1 h2 h3
    obtain ⟨hreg, hdrv⟩ := h3
    set Z := zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω)) with hZ
    have hcur : curveOf Z.drv = curveOf (drive (γ ^ 2) B ω) := curveOf_congr hdrv
    have hreg' : RegEqOff (curveOf (drive (γ ^ 2) B ω)) Z.fld (Y ω) := hreg
    funext i
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
  · filter_upwards [hpr ρ, hwp ρ, hrt] with ω h1 h2 h3
    obtain ⟨hreg, hdrv⟩ := h3
    set Z := zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω)) with hZ
    have hcur : curveOf Z.drv = curveOf (drive (γ ^ 2) B ω) := curveOf_congr hdrv
    have hreg' : RegEqOff (curveOf (drive (γ ^ 2) B ω)) Z.fld (Y ω) := hreg
    show (if Disjoint (tsupport ρ.1) (curveOf Z.drv) then pairRaw Z.fld ρ.1 else 0) =
      (if Disjoint (tsupport ρ.1) (curveOf (drive (γ ^ 2) B ω)) then pairRaw (Y ω) ρ.1 else 0)
    rw [hcur]
    split_ifs with hd
    · rw [← h1 (by rw [hcur]; exact hd),
        pairTest_congr_of_regEqOff (D74.isClosed_curveOf _) hreg' ρ hd]
      exact h2
    · rfl

/-- **Clause (3), `t > 0`**, from X1, the raw round trip and the second round trip only (copy of
`g4PosLawAStmt_of_full`, D81, which uses only the driver part of that round trip). -/
theorem g4PosLawAStmt_of_down (hX1 : BaseFin.BaseFiniteStmt) (hRaw : G4RoundRawAStmt)
    (hD : G4RoundDownAStmt) : G4PosLawAStmt := by
  intro γ Ω _ P _ B Y hS hIn hE6 hEq t ht
  obtain ⟨Φ, hΦ, hZc, hZy⟩ := g4ZipFactorFullAStmt_of_X1 hX1 γ P B Y hS hIn hE6 hEq t ht
  obtain ⟨hco, hpr⟩ := hRaw γ P B Y hS hIn hE6 hEq t ht
  have hmc : AEMeasurable (fun ω => cfgData (wedgeAConfig γ B Y ω).toPair) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hmy := aemeasurable_cfgData_zipLenDownA hX1 hS ht
  have key := Cor15Group.map_comp_eq_of_factor (e := fun x : AreaConfig => cfgData x.toPair)
    (m := fun x : AreaConfig => offData x.toPair) (Z := zipLenA γ t)
    (c := wedgeAConfig γ B Y) (y := fun ω => zipLenDownA γ t (wedgeAConfig γ B Y ω))
    hΦ hmc hmy (map_cfgData_zipLenDownA hX1 hS ht).symm hZc hZy
  rw [configLawOff_eq_map_offData, configLawOff_eq_map_offData]
  refine key.trans ?_
  have hZm : AEMeasurable
      (fun ω => offData (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).toPair) P := by
    refine ((hΦ.comp_aemeasurable hmy)).congr ?_
    filter_upwards [hZy] with ω hω
    exact hω.symm
  refine E6.map_eq_of_coord_ae P _ _ hZm (aemeasurable_offData_wedgeAConfig hS hIn) hco hpr ?_
  filter_upwards [hD γ P B Y hS hIn hE6 hEq t ht] with ω hω
  funext s
  exact hω.2 s s.2

end R18
end QuantumZipper
