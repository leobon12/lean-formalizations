import QuantumZipper.Proofs.Zipper.LocLenBridge
import QuantumZipper.Proofs.Zipper.WedgeXGoodBasic
import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.Thm13Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): the local node statements of the Theorem 1.3 proof

The targets of the campaign tasks R3–R9 (`handoff/FOLLOW-PAPER-13.md`). Each statement is the
verbatim copy of the old node named in its docstring, with the substitutions of D75:

* `unzipLengths` ↦ `LocLen.unzipLengthsArc` (open arcs), `zipLenDown` ↦ `LocLen.zipLenDownArc`,
  `F1.leftTime`/`F1.lenF` ↦ `leftTimeArc`/`lenFArc`;
* `IsLQGGood γ (unzipped Γ⁰ field at t)` ↦ `IsLQGGoodOff γ _ {0}` (tip excluded);
  `IsLQGGood γ (unzipped wedge / P_* / x field at t)` ↦ `IsLQGGoodOff γ _ (offSet W t)` (tip and
  the two root images `O^±_t` excluded);
* global limits `∃ ν, IsVagueLimitR (bdryApprox …) ν` ↦ local limits on the same complement.

The top of the chain (`theorem1_3_of_F1Arc`, `e6UpRichArc_of_meas`) is proved here: Theorem 1.3
follows from `F1StmtArc` and `F2NodeArcStmt` exactly as from the old `F1Stmt`/`F2NodeStmt`.

Paper: Sheffield arXiv:1012.4797 §5.4 pp. 69–72 (F(s) read through one measure along `η`);
Berestycki–Powell arXiv:2404.16642 Def 6.41 p. 229, Def 8.12 p. 281, Thm 8.16 p. 283,
Claim 8.17 pp. 284–285.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2

/-! ## Γ⁰ layer (samples `(𝔥₀ + X, √κ B)`) -/

/-- Local copy of `WedgeUnzip.YGoodAllStmt` (WedgeXGoodBasic.lean:111): the unzipped `Γ⁰`
fields `y_t` are good off the tip, for all `t ≥ 0`. -/
def YGoodOffAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → IsLQGGoodOff (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t) {0}

/-- Local copy of `WedgeUnzip.XGoodAllStmt` (WedgeUnzipCore.lean:66): the fields
`x_t = unzX` are good off the tip and the root images `O^±_t`, for all `t ≥ 0`. -/
def XGoodOffAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsLQGGoodOff (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t) (offSet (drive κ B ω) t)

/-- Replaces `RegUnif.UnifGlobalStmt` + `RegUnif.UnifAtomlessStmt` (UnifClAnchor.lean:62,
UnifClB5.lean:59): a.s., for all `s ∈ [0,T]`, `h⁰_s` has an atomless local limit off the tip
(glue of the UO windows, `RegUnif.UnifOffTipStmt`). -/
def UnifLocalStmt (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ∃ ν : Measure ℝ,
    IsVagueLimitOnR ({0}ᶜ) (bdryApprox (Real.sqrt κ) (h0f κ s B X ω)) ν ∧ ∀ x, ν {x} = 0

/-- Open-arc copy of `F2.B5UniformStmt` (F2Weld.lean:56): the open-arc lengths of the two sides
of `η[0,s]` are the `ν_{h⁰_T}`-masses of their open preimage arcs in the fixed chart `T`
(Sheffield p. 56; B-P Def 8.12 p. 281, footnote 22 p. 287). -/
def B5UniformArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) T,
      (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) s).1 =
          qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
            (Ioo (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - s))) ∧
        (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) s).2 =
          qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
            (Ioo (zeroPlus (B2.Vr κ T B ω) (T - s)) (zeroPlus (B2.Vr κ T B ω) T))

/-! ## Wedge / `P_*` layer -/

/-- Local copy of `WedgeUnzip.WedgeGoodAllStmt` (WedgeUnzipB3d.lean:50). -/
def WedgeGoodOffAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → IsLQGGoodOff (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)
      (offSet (drive κ B'' ω) t)

/-- Local copy of `WedgeUnzip.PStarGoodAllStmt` (WedgeUnzipPStar.lean:32). -/
def PStarGoodOffAllStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t →
      IsLQGGoodOff (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t)
        (offSet (drive κ B' ω) t)

/-! ## F1 layer: Sheffield's `F(s)` with open-arc lengths -/

/-- Copy of `F1.leftTime` (F1ABJensen.lean:73) with open-arc lengths (`= lenTimeArc`). -/
def leftTimeArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (s : ℝ) : ℝ := lenTimeArc γ s c

/-- Copy of `F1.lenF` (F1ABJensen.lean:77): `F_c(s) = L⁺(tᴸ_c(s))` with open-arc lengths
(Sheffield p. 70 ¶2). -/
def lenFArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (s : ℝ) : ℝ :=
  ((unzipLengthsArc γ c (leftTimeArc γ c s)).2).toReal

/-- Open-arc copy of `Thm13Asm.F1Stmt` (lengths agree under `P_*`). -/
def F1StmtArc : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω' ∂P', ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (Y ω', drive κ B' ω') t).1 =
        (unzipLengthsArc (Real.sqrt κ) (Y ω', drive κ B' ω') t).2

/-- Open-arc copy of `F1.LenCocycleStmt` (F1ABJensen.lean:214). -/
def LenCocycleArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ ℓ s : ℝ, 0 < ℓ → 0 ≤ s →
      lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) (ℓ + s) - lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) ℓ =
        lenFArc (Real.sqrt κ) (zipLenDownArc (Real.sqrt κ) ℓ (F1.pcfg κ Y B' ω)) s

/-- Open-arc copy of `F1.LenRegStmt` (F1ABJensen.lean:244). -/
def LenRegArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ContinuousOn (lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω)) (Ici 0) ∧
      MonotoneOn (lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω)) (Ici 0) ∧
      lenFArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) 0 = 0

/-- Open-arc copy of `F1.LenStrictMonoStmt` (F1LenBridge.lean:72). -/
def LenStrictMonoArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', StrictMonoOn (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1) (Ici 0)

/-- Open-arc copy of `F1.LenLeftSurjStmt` (F1LenFlow.lean:183). -/
def LenLeftSurjArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ ℓ : ℝ, 0 < ℓ → ∃ t : ℝ, 0 ≤ t ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1 = ENNReal.ofReal ℓ

/-- Open-arc copy of `F1.LenPairCocycleStmt` (F1LenFlow.lean:192): additivity of the lengths
along the capacity flow (the open arcs of `η(0,u)` and of `η(u,u+s)` tile the arc of
`η(0,u+s)` up to the atomless point `η(u)`). -/
def LenPairCocycleArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) (u + s)).1 =
          (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) u).1 +
            (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (F1.pcfg κ Y B' ω)) s).1 ∧
        (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) (u + s)).2 =
          (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) u).2 +
            (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (F1.pcfg κ Y B' ω)) s).2

/-! ## E6 layer and the backbone -/

/-- Open-arc copy of `Thm13Asm.E6Stmt`: `Z^LEN_{−ℓ}` (open-arc lengths) preserves the law of
`P_*` (Sheffield Thm 1.8 (3) specialised; B-P Prop 8.20). -/
def E6StmtArc : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ →
      configLawFull (fun ω' => zipLenDownArc (Real.sqrt κ) ℓ₁ (Y ω', drive κ B' ω')) P' =
        configLawFull (fun ω' => (Y ω', drive κ B' ω')) P'

/-- Open-arc copy of `E6.E6LocStmtRich` (LocRichBasic.lean:267). -/
def E6LocStmtRichArc : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ →
    ∀ R : ℕ, ∀ Γ : E6.FullData → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω', Γ (D3Plus.locRich R (zipLenDownArc (Real.sqrt κ) ℓ₁ (Y ω', drive κ B' ω'))) ∂P' =
        ∫⁻ ω', Γ (D3Plus.locRich R (Y ω', drive κ B' ω')) ∂P'

/-- Open-arc copy of `E6.E6NodeStmtRich` (LocRichE6.lean:223). -/
def E6NodeStmtRichArc : Prop := E6.E5StmtRich → E6LocStmtRichArc

/-- Open-arc copy of `E6.UnzipMeasStmt` (LocRichBasic.lean:279). -/
def UnzipMeasArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ →
      AEMeasurable (E6.dataFull fun ω' => zipLenDownArc (Real.sqrt κ) ℓ₁ (Y ω', drive κ B' ω')) P'

/-- Open-arc copy of `Thm13Asm.F1NodeStmt`. -/
def F1NodeArcStmt : Prop := E6StmtArc → F1StmtArc

/-- Open-arc copy of `Thm13Asm.F2NodeStmt` (its conclusion `Thm13LenStmt` is clause 2 of
Theorem 1.3 verbatim, unchanged). -/
def F2NodeArcStmt : Prop := F1StmtArc → Thm13Asm.Thm13LenStmt

/-! ## The top of the chain (proved) -/

/-- **E6-UP with open arcs** (copy of `E6.e6UpRich_of_meas`, pure π-λ). -/
theorem e6UpRichArc_of_meas (hmeas : UnzipMeasArcStmt) (hloc : E6LocStmtRichArc) : E6StmtArc := by
  intro κ Ω' _ P' _ Y B' hP ℓ₁ hℓ
  exact E6.configLawFull_eq_of_locRich P' _ _ (hmeas κ P' Y B' hP ℓ₁ hℓ)
    (E6.aemeasurable_dataFull_pstar hP) (hloc κ P' Y B' hP ℓ₁ hℓ)

/-- **Theorem 1.3 from the open-arc F1 and F2 nodes** (copy of `Thm13Asm.theorem1_3_of_F1`). -/
theorem theorem1_3_of_F1Arc (hF1 : F1StmtArc) (hF2 : F2NodeArcStmt) : theorem1_3 := by
  intro κ hκ0 hκ4 T hT Ω _ P _ B X hB hX hind
  filter_upwards [Thm13Asm.ae_clause1 hκ0 hκ4 hT P B hB, hF2 hF1 κ hκ0 hκ4 T hT P B X hB hX hind,
    RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ0 hκ4 T hT P B X hB hX hind]
    with ω h1 h2 h3
  exact ⟨h1, h2, h3.2.1⟩

/-- **Theorem 1.3 from the open-arc backbone nodes** (copy of `E6.theorem1_3_of_nodes_rich`):
E4 and E5 are the proved/old ones (they read no length). -/
theorem theorem1_3_of_nodes_richArc (h4 : Thm13Asm.E4Stmt) (h5 : Thm13Asm.E4Stmt → E6.E5StmtRich)
    (h6 : E6NodeStmtRichArc) (hmeas : UnzipMeasArcStmt) (hF1 : F1NodeArcStmt)
    (hF2 : F2NodeArcStmt) : theorem1_3 :=
  theorem1_3_of_F1Arc (hF1 (e6UpRichArc_of_meas hmeas (h6 (h5 h4)))) hF2

end LocLen
end QuantumZipper
