/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JiTop
import InteractingSLE.Spec.Supplement.SB2LjSplit
import InteractingSLE.Spec.Supplement.SB2JiData2

/-!
# SB2(2): the concrete rule's piece lifts from natural per-stage geometry (finite and infinite pieces, stage `0`)

Packet PROVE-SB2-LIFTSET (round 13). A refinement of `SB2LjSplit`: the per-stage geometry no longer mentions the
inverse clock (`liftRel_concrete_driven`, `liftRel_concrete_top`), infinite actual pieces are handled like finite ones,
zero-lifetime pieces are excluded by the actual positivity (`nz₁`), and the piece start's stage `0` (`lift₀`) is
included. The data clause is the corrected `RelDataClause2` (`SB2JiData2`: the record clause only at a finite start
piece), so the target is `SB2LowerRelDriverData2Statement`.

* `wRun` (the walk run), `UpperChartOK`, **`StageGeomFin`**, **`StageGeomInf`**, `StageFacts`;
  **`liftRel_of_stageFacts`** (a driven stage curve, a driver generating it: the lift relation);
* `StagesGeom` (stage `0` unless a zero root, and the stages `i ≥ 2` of `PiecesLift`), `PiecesLift2` (`PiecesLift` and
  the stage-`0` lift relation, the `lift₀` of `PieceStartData`); **`piecesLift2_of_geom`** (deterministic);
* `GeomAt2`, `PiecesLift2AS`, **`ConcreteSplit2At`**, **`SB2LowerConcreteSplit2Statement`** (named input, for measurable
  families only: the drivenness on the driven events then comes from `StageOK`);
  **`relDriverData2At_of_split2`**, **`sb2LowerRelDriverData2Statement_of_split2`** (`exists_EL_concrete`),
  `sb2LowerRelWalkRangeStatement_of_split2`, `sb2LowerLaunchLiftStatement_of_split2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- The run of the right walk with angle `θ`. -/
abbrev wRun (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (D : ℕ → Drv) (n : ℕ) : ExplState :=
  ExplState.run κ b J (boundaryWalkSpec b J θ true) D n

theorem wRun_zero (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (D : ℕ → Drv) : wRun κ θ b J D 0 = ExplState.init 0 :=
  rfl

/-- The upper chart's facts used by the lift relation. -/
def UpperChartOK (c : Chart) : Prop := ContinuousOn c.2.1 H ∧ (∀ w ∈ H, c.1 (c.2.1 w) = w) ∧ BdryOff c

/-- **The per-stage geometry at a finite actual piece** (the hypotheses of `liftRel_concrete_driven` beyond the upper
chart, the drivenness and the generation). -/
def StageGeomFin (c : Chart) (m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState)
    (e₂ : Drv) : Prop :=
  IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ∧
  {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
    closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H} ∧
  (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 = pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2} ∧
  (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL ∧
  e₂.2 ≠ ⊤ ∧ ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} ∧
  (∃ (α : ℝ≥0 → ℂ) (f : ℂ → ℂ), (∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) ∧
    α 0 = 0 ∧ ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    (∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ)))) ∧
    ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2}) ∧
  ContinuousOn (stChart s₂).2.1 H ∧ (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
  (∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H) ∧
  {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁) ∧
  ∀ t ∈ goodT c s₁ e₁, (t : ℝ≥0∞) = e₁.2 → liftPt c m (pcPt s₁ e₁ t) ∈
    closure ((fun t' => liftPt c m (pcPt s₁ e₁ t')) '' (goodT c s₁ e₁ ∩ {t' | (t' : ℝ≥0∞) < e₁.2}))

/-- **The per-stage geometry at an infinite actual piece** (the hypotheses of `liftRel_concrete_top` beyond the upper
chart, the drivenness and the generation). -/
def StageGeomInf (c : Chart) (m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState)
    (e₂ : Drv) : Prop :=
  IsCompact {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ∧
  {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
    closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H} ∧
  (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 = pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2} ∧
  (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL ∧
  ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} ∧
  (∃ (α : ℝ≥0 → ℂ) (f : ℂ → ℂ), (∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) ∧
    α 0 = 0 ∧ ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    (∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ)))) ∧
    ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    IsClosed ((fun τ => f (α τ)) '' {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2})) ∧
  ContinuousOn (stChart s₂).2.1 H ∧ (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
  (∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H) ∧
  {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)

/-- The per-stage facts: positive actual lifetime (`nz₁`), and the finite or infinite geometry. -/
def StageFacts (c : Chart) (m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState)
    (e₂ : Drv) : Prop :=
  e₁.2 ≠ 0 ∧ (e₁.2 ≠ ⊤ → StageGeomFin c m β₀ tL s₁ e₁ s₂ e₂) ∧ (e₁.2 = ⊤ → StageGeomInf c m β₀ tL s₁ e₁ s₂ e₂)

/-- **The lift relation from the per-stage facts**, for a driven stage curve and a driver generating it. -/
theorem liftRel_of_stageFacts {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₁ s₂ : ExplState}
    {e₁ e₂ : Drv} (hγ : IsTailLiftCurve c R m β₀ tL γ) (hU : UpperChartOK c)
    (hF : StageFacts c m β₀ tL s₁ e₁ s₂ e₂) (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hW0 : e₂.1 0 = 0) : LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  obtain ⟨hcH, hc1, hoff⟩ := hU
  obtain ⟨hpos, hfin, htop⟩ := hF
  by_cases he₁ : e₁.2 = ⊤
  · obtain ⟨hTc, hd₁, htip, htail, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc, hcl⟩, hcH₂, hc1₂, hdom, hgd⟩ := htop he₁
    exact liftRel_concrete_top hγ hcH hc1 hoff hTc hd₁ htip htail he₁ hρ he₂ hgen hW hW0 hαeq hα0 hαc hc hgc hcl
      hcH₂ hc1₂ hdom hgd
  · obtain ⟨hTc, hd₁, htip, htail, hfin₂, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc⟩, hcH₂, hc1₂, hdom, hgd, hend⟩ :=
      hfin he₁
    exact liftRel_concrete_driven hγ hcH hc1 hoff hTc hd₁ htip htail he₁ hpos hρ he₂ hgen hfin₂ hW hW0 hαeq hα0 hαc
      hc hgc hcH₂ hc1₂ hdom hgd hend

/-- **The per-stage geometry along the walks** (one sample): at stage `0` unless the start is a zero root (when the
actual stage `relOff` launches), and at every even stage `i ≥ 2` whose actual stage launches with arc status and an
admissible seed, the stage is driven (`Gi`) and has the per-stage facts. -/
def StagesGeom (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) (Gi : ℕ → Prop) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop :=
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ →
    (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
    Gi 0 ∧ StageFacts c m β₀ tL (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
      (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0)) ∧
  ∀ i, 2 ≤ i → i % 2 = 0 →
    (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
    stStatus (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) = GW1W.stArcM true →
    ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁))))
      (rightLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)))) θ →
    Gi i ∧ StageFacts c m β₀ tL (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₁ (i + relOff κ θ b₁ J₁ R D₁))
      (wRun κ θ b₂ J₂ D₂ i) (D₂ i)

/-- **The piece lifts with the stage-`0` lift** (one sample): `PiecesLift`, and at a start that is not a zero root
the relative stage-`0` piece is the lift of the actual piece at `relOff` (`PieceStartData.lift₀`). -/
def PiecesLift2 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (D₁ D₂ : ℕ → Drv)
    (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop :=
  PiecesLift κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL ∧
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ →
    (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
    LiftRel β₀ tL γ (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
      (newPc (ExplState.init 0) (D₂ 0)))

/-- **The piece lifts from the per-stage geometry** (deterministic): for relative drivers that are regular, generate
the concrete stage curves on the driven, non-zero stages, with the stage curves driven there. -/
theorem piecesLift2_of_geom {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ}
    {c : Chart} {m : ℝ} {D₁ D₂ : ℕ → Drv} {Gi : ℕ → Prop} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R' : ℝ}
    (hU : UpperChartOK c) (hγ : IsTailLiftCurve c R' m β₀ tL γ)
    (hG : StagesGeom κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ Gi β₀ tL) (hreg : ∀ j, IsRegularDriver (D₂ j))
    (hgen : ∀ j, Gi j → ¬ (j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁)) →
      (D₂ j).2 = capLife (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
        (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j)) ∧
      ∀ T < capLife (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
          (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j)),
        IsGeneratingTrace (D₂ j).1 T (capTrace (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
          (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j))))
    (hdrv : ∀ j, Gi j → IsDrivenCurve (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
      (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j))) :
    PiecesLift2 κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL := by
  obtain ⟨h0, hi⟩ := hG
  refine ⟨?_, fun hZ hl => ?_⟩
  · intro i hi2 hl hflow hstat hseed
    have hev : i % 2 = 0 := of_decide_eq_true hflow
    obtain ⟨hGi, hF⟩ := hi i hi2 hev hl hstat hseed
    have hnZ : ¬ (i % 2 = 1 ∨ (i = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁)) := by
      rintro (h | ⟨h, -⟩) <;> omega
    obtain ⟨he₂, hg⟩ := hgen i hGi hnZ
    exact liftRel_of_stageFacts hγ hU hF (hdrv i hGi) he₂ hg (hreg i).2.1
  · obtain ⟨hG0, hF⟩ := h0 hZ hl
    have hnZ : ¬ (0 % 2 = 1 ∨ (0 = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁)) := by
      rintro (h | ⟨-, h⟩)
      · omega
      · exact hZ h
    obtain ⟨he₂, hg⟩ := hgen 0 hG0 hnZ
    have hd := hdrv 0 hG0
    simp only [zero_add] at he₂ hg hd
    exact liftRel_of_stageFacts hγ hU hF hd he₂ hg (hreg 0).2.1

universe u

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- The per-stage geometry, almost surely, for a relative family `EL` and run-read driven events `ΦG`. -/
def GeomAt2 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (ΦG : ℕ → Ω → ExplState → Prop) (EL : ℕ → Ω → Drv) : Prop :=
  UpperChartOK c ∧
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        StagesGeom κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
          (lD₁ b jumps E ω) (fun j => EL j ω) (fun j => ω ∈ lG κ b' J' m ΦG j EL) β₀ tL

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- The piece lifts with the stage-`0` lift, almost surely, for a relative family `EL`. -/
def PiecesLift2AS (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        PiecesLift2 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀)
          (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The concrete rule, split with natural per-stage geometry**: run-read driven events making the concrete rule
admissible, such that every **measurable**, everywhere regular family that is `zeroDrv` on the zero events and
generates the concrete curves on the driven events has the per-stage geometry almost surely and satisfies the v2 data
clause given the piece lifts with the stage-`0` lift. -/
def ConcreteSplit2At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ ΦG : ℕ → Ω → ExplState → Prop,
    (∀ j F, (∀ i < j, Measurable (F i)) →
      StageOK (lρ κ b jumps E u l k ω₀ c b' J' m j F) (lG κ b' J' m ΦG j F) (lZ κ b jumps E u l k ω₀ j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt2 κ b jumps P E u l k ω₀ c b' J' m ΦG EL ∧
      (PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL)

/-- **Named input: SB2(2)'s concrete rule, split with natural per-stage geometry.** -/
def SB2LowerConcreteSplit2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ConcreteSplit2At κ b jumps P E u l k ω₀ c b' J'

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The v2 relative-driver data at one launch from the split concrete rule** (`exists_EL_concrete`; the piece lifts
by `piecesLift2_of_geom`, the drivenness from `StageOK` since `EL` is measurable). -/
theorem relDriverData2At_of_split2 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ}
    (h : ConcreteSplit2At κ b jumps P E u l k ω₀ c b' J') : RelDriverData2At κ b jumps P E u l k ω₀ c b' J' := by
  intro m hm
  obtain ⟨ΦG, hok, hcl⟩ := h m hm
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_concrete κ (-(Real.pi / 2)) b jumps (affData 1 m b')
    (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) ΦG hok
  refine ⟨EL, hmeas, hreg, ?_⟩
  obtain ⟨⟨hU, hae⟩, hrest⟩ := hcl EL hmeas hreg hZ hgen
  refine hrest ?_
  filter_upwards [hae] with ω hω
  intro β₀ hβ hβ0 hβr tL γ hγ
  exact piecesLift2_of_geom hU hγ (hω β₀ hβ hβ0 hβr tL γ hγ) (fun j => hreg j ω)
    (fun j hG hnZ => hgen j ω hG hnZ) (fun j hG => (hok j EL fun i _ => hmeas i).2.2.2 ω hG)

/-- **The v2 head-free relative-driver data from the split concrete rule with natural per-stage geometry.** -/
theorem sb2LowerRelDriverData2Statement_of_split2 (hS : SB2LowerConcreteSplit2Statement.{u}) :
    SB2LowerRelDriverData2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk
  exact relDriverData2At_of_split2 (h₀ c θ hlaunch b' J' h' hb' hT' hG' hk)

/-- **The range identity of SB2(2)'s lifted walk from the split concrete rule** (and Theorems 1.2–1.3 for GW1's chain
facts). -/
theorem sb2LowerRelWalkRangeStatement_of_split2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerConcreteSplit2Statement.{u}) :
    SB2LowerRelWalkRangeStatement.{u} :=
  sb2LowerRelWalkRangeStatement_of_data2 (sb2LowerRelDriverData2Statement_of_split2 hS)
    (sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)

/-- **SB2(2)'s combined target (R104a) from the split concrete rule with natural per-stage geometry.** -/
theorem sb2LowerLaunchLiftStatement_of_split2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerConcreteSplit2Statement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_data2 h12 h13 h12₀ h13₀ (sb2LowerRelDriverData2Statement_of_split2 hS) hcond

end InteractingSLE.Theorem14.SB.Lk
