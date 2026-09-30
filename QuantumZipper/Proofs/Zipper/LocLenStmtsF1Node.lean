import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.LocLenStmtsRead
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.F1LenRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e: statements of the F1 node with open arcs

Open-arc copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1: `unzipLengths ↦
unzipLengthsArc`, `zipLenDown ↦ zipLenDownArc`, `lenF/leftTime ↦ lenFArc/leftTimeArc`) of the
statements of the old F1 chain (Sheffield arXiv:1012.4797 §5.4 pp. 70–72):

* `F1ABArcStmt`, `HLinAllArcStmt` (F1ABJensen.lean / F1NodeC.lean: `F1ABStmt`, `HLinAllStmt`);
* `LenScaleArcStmt`, `LenReadArcStmt`, `LenBridgeArcStmt` (F1ABJensen.lean:225–253);
* `LenReadTimeArcStmt`, `LenReadRegArcStmt` (F1LenRead.lean:160, :169);
* `F1EmbedArcStmt` (F1NodeC.lean:57).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- Open-arc copy of `F1.HLinAllStmt`: `L⁺ = f L⁻` at all times for every `P_*` sample. -/
def HLinAllArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∃ f : Ω' → ℝ≥0∞, ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).2 =
        f ω * (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1

/-- Open-arc copy of `F1.F1ABStmt` (F1a–F1b, Sheffield p. 71). -/
def F1ABArcStmt : Prop := E6StmtArc → HLinAllArcStmt

/-- Open-arc copy of `F1.LenScaleStmt` (F1b scaling). -/
def LenScaleArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ n : ℕ, 1 ≤ n → ∃ c' : Ω' → FieldSample × (ℝ → ℝ),
      configLawFull c' P' = configLawFull (F1.pcfg κ Y B') P' ∧
      AEMeasurable (fun ω => cfgData (c' ω)) P' ∧
      (∀ᵐ ω ∂P', Continuous (c' ω).2 ∧ ∀ s, (c' ω).2 s = (c' ω).2 (s.toNNReal : ℝ)) ∧
      ∀ᵐ ω ∂P', ∀ s, 0 ≤ s →
        lenFArc (Real.sqrt κ) (c' ω) s = lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) (n * s) / n

/-- Open-arc copy of `F1.LenReadStmt`. -/
def LenReadArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ s : ℝ, AEMeasurable (fun d => lenFArc (Real.sqrt κ) (F1.readCfg d) s)
      (configLawFull (F1.pcfg κ Y B') P')

/-- Open-arc copy of `F1.LenBridgeStmt`. -/
def LenBridgeArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1 < ⊤ ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).2 = ENNReal.ofReal
        (lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω)
          ((unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1.toReal))

/-- Open-arc copy of `F1.LenReadTimeStmt` (fixed-time reading). -/
def LenReadTimeArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ t : ℝ, 0 ≤ t → AEMeasurable (fun d => unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t)
      (configLawFull (F1.pcfg κ Y B') P')

/-- Open-arc copy of `F1.LenReadRegStmt` (regularity in time of the read lengths). -/
def LenReadRegArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ d ∂(configLawFull (F1.pcfg κ Y B') P'),
      MonotoneOn (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t).1) (Ici 0) ∧
      ContinuousOn (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t).2.toReal) (Ici 0)

/-- Open-arc copy of `F1.F1EmbedStmt` (the embedding step of F1c, Sheffield p. 71). -/
def F1EmbedArcStmt : Prop :=
  HLinAllArcStmt →
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    AEMeasurable (fun ω => lenRatio (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1)) P' ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample)
      (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0∞),
      IsProbabilityMeasure P ∧ IsFreeGFFModConstH X P ∧
      IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P ∧
      IsBrownianReal B P ∧ (∀ t, Measurable (A t)) ∧ (∀ t, Measurable (B t)) ∧
      iIndep (srcSigma X A B) P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
        (unzipLengthsArc (Real.sqrt κ) (unscaledConfig (Real.sqrt κ) κ X A B ω) t).2 =
          g ω * (unzipLengthsArc (Real.sqrt κ) (unscaledConfig (Real.sqrt κ) κ X A B ω) t).1) ∧
      (∀ᵐ ω ∂P, ∀ m, 0 < (unzipLengthsArc (Real.sqrt κ)
          (unscaledConfig (Real.sqrt κ) κ X A B ω) (GermZeroOne.epsSeq m : ℝ)).1 ∧
        (unzipLengthsArc (Real.sqrt κ) (unscaledConfig (Real.sqrt κ) κ X A B ω)
          (GermZeroOne.epsSeq m : ℝ)).1 < ⊤) ∧
      P'.map (fun ω => lenRatio (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1)) = P.map g

end LocLen
end QuantumZipper
