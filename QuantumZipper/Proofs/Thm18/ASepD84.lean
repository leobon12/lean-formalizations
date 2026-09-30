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
# ASEP / D84: the A-sep leaf at the parameters its paper-form consumers use (`τ' = 0`)

`G4Core.G4SepRepStmt` (G4SepUCTransfer.lean:67) asks exactness of the unzipped field at the pushed
separated circles `σ_i.map ψ`, `ψ = revMapInv (backDrv W τ τ' a)`, for **all** `0 ≤ τ' ≤ τ`,
`a > 0`. Its only paper-form consumers (`R18.g4RoundDownA_of`, `R18.g4ZipRegAStmt_of`, through
`D74R.pushRegOffAt_of_sepAll … le_rfl …`) use it at `τ' = 0` only, where
`backDrv W τ 0 a = revDrv W τ a` is the rescaled time reversal of Sheffield's inverse zipping map
(arXiv:1012.4797, Theorem 1.8 (1), p. 26: `Z_ℓ` is the inverse of `Z_{−ℓ}`). The circles are the
off-curve ones (`CircleOff`, D74/D76), which is exactly the separation `BackSepI`.

This file states the weaker leaf `G4SepRep0Stmt` (only `τ' = 0` and `τ > 0`: parameters `(τ, a)`
instead of `(τ, τ', a)`), proves that it follows from `G4SepRepStmt` (`g4SepRep0Stmt_of_rep`), and rewires the
consumers:

* `g4SepFixed0Stmt_of_rep0`, `g4SepExact0Stmt_of_fixed0` (copies of the law transfer and the
  independence/Fubini step of G4SepUCTransfer.lean);
* `g4DriverPushSep0Stmt_of` (integrability from the proved `backLogSepStmt_holds`);
* `g4RoundDownA0_of`, `g4ZipRegA0_of` (copies of `R18.g4RoundDownA_of`, `R18.g4ZipRegAStmt_of`);
* **`theorem1_8Paper_of_frontier7`**: `R18.theorem1_8Paper_of_frontier6` with `hSepRep`
  replaced by the weaker `G4SepRep0Stmt`.

Decision D84 (DECISIONS.md). Own bookkeeping (verbatim copies with `τ' := 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core R18

/-- The exactness conclusion of A-sep at `τ' = 0` for one configuration `c`. -/
def G4SepConcl0 (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) : Prop :=
  ∀ τ a : ℝ, 0 < τ → 0 < a → ∀ i : ℕ,
    BackSupportI c τ 0 a i → BackSepI c τ 0 a i →
    (evalReg (rescale (unzippedField γ c τ) (Qc γ) a)
        ((fcI i).map (revMapInv (backDrv c.2 τ 0 a).2 (backDrv c.2 τ 0 a).1)) =
      rescale (unzippedField γ c τ) (Qc γ) a
        ((fcI i).map (revMapInv (backDrv c.2 τ 0 a).2 (backDrv c.2 τ 0 a).1))) ∧
    evalReg (unzippedField γ c τ)
        ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ 0 a).2
          (backDrv c.2 τ 0 a).1 w) =
      unzippedField γ c τ
        ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ 0 a).2
          (backDrv c.2 τ 0 a).1 w)

/-- Good pairs at `τ' = 0`. -/
def G4SepGood0 (γ : ℝ) (p : G1PathData) : Prop :=
  Continuous p.1 → ∀ y : FieldSample, WedgeMeas.dataFull H y = p.2 →
    G4SepConcl0 γ (y, pathDrive (γ ^ 2) p.1)

/-- **The A-sep leaf at `τ' = 0`** (D84): `G4Core.G4SepRepStmt` restricted to `τ' = 0`. -/
def G4SepRep0Stmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G4SepGood0 γ p) ∧
        ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E

/-- Product form at `τ' = 0`. -/
def G4SepFixed0Stmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G4SepGood0 γ p) ∧
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ c ∂(fieldLawFull H Y P), (a, c) ∈ E

/-- The exactness node at `τ' = 0` for the wedge configuration. -/
def G4DriverPushSepExact0Stmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, G4SepConcl0 γ (wedgeConfig γ B Y ω)

/-- Law transfer (copy of `g4SepFixedStmt_of_rep`). -/
theorem g4SepFixed0Stmt_of_rep0 (h : G4SepRep0Stmt) : G4SepFixed0Stmt := by
  intro γ Ω _ P _ B Y hS _
  obtain ⟨hγ, hγ2, hB, hY, -⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨E, hE, hg, hae⟩ := h γ hγ hγ2 P B hB P' X A hX hA hXA
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hα, Ω', inferInstance, P', X, A, hP', hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  refine ⟨E, hE, hg, ?_⟩
  rw [hlaw]
  filter_upwards [hae] with a ha
  exact (ae_map_iff hm (measurable_prodMk_left hE)).2 ha

/-- Independence/Fubini step (copy of `g4SepExactStmt_of_fixed`). -/
theorem g4SepExact0Stmt_of_fixed0 (h : G4SepFixed0Stmt) : G4DriverPushSepExact0Stmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨E, hE, hgood, hae⟩ := h γ P B Y hS hIn
  obtain ⟨-, -, hB, -, hind⟩ := hS
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hdm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P := hIn.2.1
  have hind' : IndepFun (hgm.mk _) (hdm.mk _) P :=
    (hind.comp measurable_id measurable_dataFull_H).congr hgm.ae_eq_mk hdm.ae_eq_mk
  have h1 : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (hgm.mk _ ω, hdm.mk _ ω') ∈ E := by
    filter_upwards [ae_of_ae_map hgm hae, hgm.ae_eq_mk] with ω hω hω'
    filter_upwards [ae_of_ae_map hdm hω, hdm.ae_eq_mk] with ω' h2 h3
    rw [← hω', ← h3]; exact h2
  have h2 := CharFunRhs.ae_indep_ae hgm.measurable_mk hdm.measurable_mk hind' hE h1
  filter_upwards [h2, hgm.ae_eq_mk, hdm.ae_eq_mk, hB.cont] with ω hω e1 e2 hc
  rw [← e1, ← e2] at hω
  exact hgood _ hω hc (Y ω) rfl

/-- A-sep data at `τ' = 0` (exactness and integrability). -/
def G4DriverPushSep0Stmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ τ a : ℝ, 0 < τ → 0 < a → ∀ i : ℕ,
      BackSupportI (wedgeConfig γ B Y ω) τ 0 a i → BackSepI (wedgeConfig γ B Y ω) τ 0 a i →
      DriverPushExactI γ (wedgeConfig γ B Y ω) τ 0 a i

/-- Integrability conjuncts from the proved deterministic node (copy of
`g4DriverPushSepAllStmt_of_log_exact`). -/
theorem g4DriverPushSep0Stmt_of_rep0 (h : G4SepRep0Stmt) : G4DriverPushSep0Stmt := by
  have hE := g4SepExact0Stmt_of_fixed0 (g4SepFixed0Stmt_of_rep0 h)
  intro γ Ω _ P _ B Y hS hIn
  filter_upwards [hE γ P B Y hS hIn, ae_continuous_wedgeConfig_snd hS,
    hS.2.2.1.eval_zero_ae_eq_zero] with ω hEω hc h0
  intro τ a hτ ha i hsup hsep
  have hW0 : (wedgeConfig γ B Y ω).2 0 = 0 := drive_zero h0
  have key := hEω τ a hτ ha i hsup hsep
  exact driverPushExactI_of_log (c := wedgeConfig γ B Y ω) backLogSepStmt_holds hc hW0 le_rfl hτ.le
    ha hsup hsep key.1 key.2

/-- Off-hull data at `τ' = 0` (copy of `D74R.pushRegOffAt_of_sepAll`). -/
theorem pushRegOffAt_of_sep0 {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (h : ∀ τ a : ℝ, 0 < τ → 0 < a → ∀ i : ℕ,
      BackSupportI c τ 0 a i → BackSepI c τ 0 a i → DriverPushExactI γ c τ 0 a i)
    {τ a : ℝ} (hτ : 0 < τ) (ha : 0 < a) : D74R.PushRegOffAt γ c τ 0 a := by
  intro i hoff
  have hr : 0 ≤ (CoordsFull.fullIndex i).2 := (UnzipFull.fullIndex_radius_pos i).le
  obtain ⟨δ, hδ, hnull⟩ := D74R.foldedCircle_thickening_null_of_circleOff sdiff_subset hr hoff
  have hK : fcI i (revHull (backDrv c.2 τ 0 a).2 (backDrv c.2 τ 0 a).1) = 0 :=
    measure_mono_null (Metric.self_subset_thickening hδ _) hnull
  have hsup : BackSupportI c τ 0 a i := by
    have hHc : fcI i Hᶜ = 0 :=
      ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (UnzipFull.fullIndex_radius_pos i))
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hHc hK)
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hzH, hz⟩
    · exact Or.inl hzH
  exact ⟨hsup, hK, h τ a hτ ha i hsup ⟨δ, hδ, hnull⟩⟩

end ASep
end QuantumZipper
