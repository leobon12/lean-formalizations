import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.B2Driver
import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.ESMLMeas
import QuantumZipper.Proofs.Zipper.B5VHccMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), R7: the F2 chain with open-arc lengths (statements + wiring)

Open-arc copies (`unzipLengths ↦ LocLen.unzipLengthsArc`) of the intermediate F2 statements of
`F2Reduce.lean`, `F2LocalSteps.lean`, `F2LocalRev.lean` (Sheffield arXiv:1012.4797 §5.4
pp. 70–72: from lengths agreeing under `P_*` to clause 2 of Theorem 1.3), and the proved wiring:

* `f2NodeArc_of_inputs : F2WeldLenArcStmt → F2UnscaledArcStmt → F2LocalArcStmt → F2NodeArcStmt`
  (copy of `F2.f2Node_of_inputs`);
* `f2LocalArc_of_steps : Step2bArcStmt → Step3ArcStmt → Step4ArcStmt → F2LocalArcStmt` (copy of
  `F2.f2Local_of_steps`), with the time reversal `gammaZeroArc_of_fwd` (copy of
  `F2.gammaZero_of_fwd`) proved via `unzipLengthsArc_eq_of_drive_eqOn`.

The open inputs of the F2 node are thus `F2WeldLenArcStmt` (step 1), `F2UnscaledArcStmt`
(step 2a), `Step2bArcStmt`, `Step3ArcStmt`, `Step4ArcStmt` (tasks R7a/R7c of
`handoff/FOLLOW-PAPER-13.md`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-! ## Driver congruence -/

/-- Open-arc lengths at time `t` only read the driver on `[0,t]` (copy of
`ESM.unzipLengths_eq_of_drive_eqOn`). -/
theorem unzipLengthsArc_eq_of_drive_eqOn {γ : ℝ} (x : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ r ∈ Set.Icc (0 : ℝ) t, W r = W' r) :
    unzipLengthsArc γ (x, W) t = unzipLengthsArc γ (x, W') t := by
  have hψ := ESM.fwdMapInv_eqOn_of_drive_eqOn hW hW' hW0 hW0' ht h
  have hco : CoordsFull.coordsFull (unzippedField γ (x, W) t) =
      CoordsFull.coordsFull (unzippedField γ (x, W') t) := by
    funext i
    exact UnzipInvariance.coordChange_congr_of_eqOn hψ
      (ESM.foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i)) x (Qc γ)
  have hq : ∀ U, qBoundaryMeasureOn γ (unzippedField γ (x, W) t) U =
      qBoundaryMeasureOn γ (unzippedField γ (x, W') t) U := fun U =>
    B5.qBoundaryMeasureOn_congr_full hco U
  simp only [unzipLengthsArc, arcLen, hq, ESM.sideImages_congr_drive ht h]

/-! ## Statements -/

/-- Open-arc copy of `F2.SmallTimeAgree`. -/
def SmallTimeAgreeArc (γ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (t₀ M : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → (∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) →
    (unzipLengthsArc γ (x, W) t).1 = (unzipLengthsArc γ (x, W) t).2

/-- Open-arc copy of `F2.LogSingLocLenAgree`. -/
def LogSingLocLenAgreeArc : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ t₀ M : ℝ, 0 < t₀ ∧ 0 < M ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, SmallTimeAgreeArc (Real.sqrt κ) (X ω + F2.logSingField κ) (drive κ B ω) t₀ M

/-- Open-arc copy of `F2.GammaZeroLocLenAgree`. -/
def GammaZeroLocLenAgreeArc : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ t₀ M : ℝ, 0 < t₀ ∧ 0 < M ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, SmallTimeAgreeArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω) (drive κ B ω) t₀ M

/-- Open-arc copy of `F2.GammaZeroFwdLenAgree`. -/
def GammaZeroFwdLenAgreeArc : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t).1 =
        (unzipLengthsArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t).2

/-- Open-arc copy of `F2.UnscaledLenAgree`. -/
def UnscaledLenAgreeArc : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ)
          (wedgeField (lateralPart (X' ω)) (fun t => A t ω) (Qc (Real.sqrt κ)),
            drive κ B'' ω) t).1 =
        (unzipLengthsArc (Real.sqrt κ)
          (wedgeField (lateralPart (X' ω)) (fun t => A t ω) (Qc (Real.sqrt κ)),
            drive κ B'' ω) t).2

/-- Open-arc copy of `F2.LenAgreeOn`. -/
def LenAgreeOnArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (r : ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ r → (unzipLengthsArc γ c s).1 = (unzipLengthsArc γ c s).2

/-- Open-arc copy of `F2.GammaZeroLenAgree`. -/
def GammaZeroLenAgreeArc : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, LenAgreeOnArc (Real.sqrt κ) (F2.cfgT κ T B X ω) T

/-- Open-arc copy of `F2.F2WeldLenStmt` (step (1); the chart-`T` readings of `couplingFieldRev`
stay global: fixed time). -/
def F2WeldLenArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P,
      (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) T).1 ≠ ⊤ ∧
      ∀ xm xp : ℝ, xm < 0 → 0 < xp →
        revMapBdry (drive κ B ω) T xm = revMapBdry (drive κ B ω) T xp →
        revMapBdry (drive κ B ω) T xm ∈ insert 0 (revHull (drive κ B ω) T) →
        ∃ r ∈ Icc (0 : ℝ) T,
          qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
              (Icc xm 0) + (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) r).1 =
            (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) T).1 ∧
          qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
              (Icc 0 xp) + (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) r).2 =
            (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) T).2

/-- Open-arc copy of `F2.F2UnscaledStmt` (step (2a)). -/
def F2UnscaledArcStmt : Prop := F1StmtArc → UnscaledLenAgreeArc

/-- Open-arc copy of `F2.F2LocalStmt` (steps (2b)–(4)). -/
def F2LocalArcStmt : Prop := UnscaledLenAgreeArc → GammaZeroLenAgreeArc

/-- Open-arc copy of `F2.Step2bStmt`. -/
def Step2bArcStmt : Prop := UnscaledLenAgreeArc → LogSingLocLenAgreeArc

/-- Open-arc copy of `F2.Step3Stmt`. -/
def Step3ArcStmt : Prop := LogSingLocLenAgreeArc → GammaZeroLocLenAgreeArc

/-- Open-arc copy of `F2.Step4Stmt`. -/
def Step4ArcStmt : Prop := GammaZeroLocLenAgreeArc → GammaZeroFwdLenAgreeArc

/-! ## Wiring (proved) -/

/-- **Time reversal** (copy of `F2.gammaZero_of_fwd`). -/
theorem gammaZeroArc_of_fwd (hF : GammaZeroFwdLenAgreeArc) : GammaZeroLenAgreeArc := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind
  obtain ⟨B'', hB'', -, hc'', hind'', hV⟩ := B2.exists_revDriver (κ := κ) hB hind hT.le
  filter_upwards [hF κ hκ hκ4 P B'' X hB'' hX hind'', hV, hB.cont,
    hB''.eval_zero_ae_eq_zero] with ω hω hVω hcω h0''ω
  intro s hs hsT
  have hW : Continuous (drive κ B ω) := continuous_const.mul (hcω.comp continuous_real_toNNReal)
  have hW'' : Continuous (drive κ B'' ω) :=
    continuous_const.mul ((hc'' ω).comp continuous_real_toNNReal)
  have hW0'' : drive κ B'' ω 0 = 0 := by simp [drive, h0''ω]
  have hcfg : F2.cfgT κ T B X ω = (ofFun (h0rev κ) + X ω, B2.vrev (drive κ B ω) T) := rfl
  have heq : unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) s =
      unzipLengthsArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B'' ω) s := by
    rw [hcfg]
    exact unzipLengthsArc_eq_of_drive_eqOn _ (B2.continuous_vrev hW T) hW''
      (B2.vrev_zero hT.le) hW0'' hs (fun r hr => hVω r ⟨hr.1, hr.2.trans hsT⟩)
  rw [heq]
  exact hω s hs

/-- **F2 steps (2b)–(4)** (copy of `F2.f2Local_of_steps`). -/
theorem f2LocalArc_of_steps (h2 : Step2bArcStmt) (h3 : Step3ArcStmt) (h4 : Step4ArcStmt) :
    F2LocalArcStmt :=
  fun hU => gammaZeroArc_of_fwd (h4 (h3 (h2 hU)))

/-- Step (1) + the `Γ⁰` statement give clause 2 of Theorem 1.3 (copy of
`F2.thm13Len_of_gammaZero`). -/
theorem thm13Len_of_gammaZeroArc (h1 : F2WeldLenArcStmt) (hG : GammaZeroLenAgreeArc) :
    Thm13Asm.Thm13LenStmt := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind
  filter_upwards [h1 κ hκ hκ4 T hT P B X hB hX hind, hG κ hκ hκ4 T hT P B X hB hX hind]
    with ω hw hla
  obtain ⟨hfin, hw⟩ := hw
  intro xm xp hxm hxp heq hmem
  obtain ⟨r, hr, e1, e2⟩ := hw xm xp hxm hxp heq hmem
  exact F2.len_eq_of_add_eq hfin (hla r hr.1 hr.2) (hla T hT.le le_rfl) e1 e2

/-- **F2 node with open arcs** from its three inputs (copy of `F2.f2Node_of_inputs`). -/
theorem f2NodeArc_of_inputs (h1 : F2WeldLenArcStmt) (h2 : F2UnscaledArcStmt)
    (h3 : F2LocalArcStmt) : F2NodeArcStmt := fun hF1 =>
  thm13Len_of_gammaZeroArc h1 (h3 (h2 hF1))

end LocLen
end QuantumZipper
