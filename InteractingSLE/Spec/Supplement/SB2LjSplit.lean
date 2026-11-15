/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LjData
import InteractingSLE.Spec.Supplement.SB2LjLift

/-!
# SB2(2): the concrete rule's piece lifts from per-stage geometry

Packet PROVE-SB2-LIFTSET (round 12). The data clause of the concrete rule splits into the piece lifts (the `piece` field
of `RunInputs`, at offset `relOff`) and the rest. The piece lifts at finite, positive-lifetime actual launches follow
from `liftRel_concrete` and per-stage geometric facts; this file proves that step.

* `PiecesLift`: the relative pieces from relative stage `2` on are the lifts of the actual ones launched at stage
  `i + relOff` (`StepPiece` at every relative stage whose actual stage launches);
* **`StageGeom`**: the per-stage geometric facts of `liftRel_concrete` (upper chart, actual tip set as the image of its
  points, tail position, compactness/density of the good tail times, relative chart's inverse identity on its domain,
  lifted good points in the relative domain, a continuous endpoint extension of the generated trace with its
  boundary map, density/cover of the relative good times);
* **`liftRel_of_stageGeom`**;
* `GeomAt` (almost surely, at each relative stage `i ≥ 2` whose actual stage launches with arc status and an admissible
  seed: the sample is in the driven event, and `StageGeom` at finite positive lifetime, the lift relation itself at
  infinite or zero lifetime), `PiecesLiftAS`;
* **`ConcreteSplitAt`**, **`SB2LowerConcreteSplitStatement`** (named input: run-read driven events making the rule
  admissible, `GeomAt` and "the clause given the piece lifts" for every family generating the concrete curves);
* **`concreteRuleAt_of_split`** (the piece lifts are **proved** from `GeomAt` by `liftRel_concrete`),
  **`sb2LowerRelDriverDataStatement_of_split`**, `sb2LowerLaunchLiftStatement_of_concreteSplit`.
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

/-- **The piece lifts at offset `relOff`**: at every relative stage `i ≥ 2` whose actual stage `i + o` launches, the
relative piece is the lift of the actual one (`StepPiece`). -/
def PiecesLift (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (D₁ D₂ : ℕ → Drv)
    (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop :=
  ∀ i, 2 ≤ i →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
      (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
    StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₂ i)

/-- **The per-stage geometric facts of `liftRel_concrete`** for the actual launch `(s₁, e₁)` and the relative launch
`(s₂, e₂)`. -/
def StageGeom (c : Chart) (m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState)
    (e₂ : Drv) : Prop :=
  ContinuousOn c.2.1 H ∧ (∀ w ∈ H, c.1 (c.2.1 w) = w) ∧ BdryOff c ∧
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
  {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2} ⊆ closure (cGd c m s₁ e₁ s₂ e₂) ∧
  liftPt c m '' (pcPt s₁ e₁ '' goodT c s₁ e₁) ⊆
    closure ((fun τ => liftPt c m (pcPt s₁ e₁ (cTm c m s₁ e₁ s₂ τ))) '' cGd c m s₁ e₁ s₂ e₂)

/-- **The lift relation from the per-stage geometry** (finite actual piece; `liftRel_concrete`). -/
theorem liftRel_of_stageGeom {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) {s₁ s₂ : ExplState} {e₁ e₂ : Drv}
    (hg : StageGeom c m β₀ tL s₁ e₁ s₂ e₂) (he₁ : e₁.2 ≠ ⊤) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hW0 : e₂.1 0 = 0) : LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  obtain ⟨hcH, hc1, hoff, hTc, hd₁, htip, htail, hfin, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc⟩, hcH₂, hc1₂, hdom,
    hd₂, hcov⟩ := hg
  exact liftRel_concrete hγ hcH hc1 hoff hTc hd₁ htip htail he₁ he₂ hgen hfin hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂
    hdom hd₂ hcov

universe u

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The per-stage geometry, almost surely**, for a relative family `EL` and run-read driven events `ΦG`: at every
relative stage `i ≥ 2` (even) whose actual stage `i + o` launches with arc status and an admissible seed, the sample is
in the driven event, `StageGeom` holds at finite positive actual lifetime, and the lift relation holds at infinite or
zero actual lifetime. -/
def GeomAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (ΦG : ℕ → Ω → ExplState → Prop) (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        ∀ i, 2 ≤ i → i % 2 = 0 →
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω)
            (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
            (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
          stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω)
            (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))) =
              GW1W.stArcM true →
          ExplState.IsAdmissibleSeed κ
            (leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (lD₁ b jumps E ω)
              (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))))
            (rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (lD₁ b jumps E ω)
              (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))))
            (-(Real.pi / 2)) →
          ω ∈ lG κ b' J' m ΦG i EL ∧
          ((lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
              (lD₁ b jumps E ω))).2 ≠ ⊤ →
            (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
              (lD₁ b jumps E ω))).2 ≠ 0 →
            StageGeom c m β₀ tL
              (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω)
                (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
                (lD₁ b jumps E ω)))
              (ExplState.run κ (affData 1 m b') (affJumps 1 m J')
                (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) (fun j => EL j ω) i)
              (EL i ω)) ∧
          ((lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
              (lD₁ b jumps E ω))).2 = ⊤ ∨
            (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
              (lD₁ b jumps E ω))).2 = 0 →
            LiftRel β₀ tL γ
              (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω)
                (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
                  (lD₁ b jumps E ω))))
              (newPc (ExplState.run κ (affData 1 m b') (affJumps 1 m J')
                (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) (fun j => EL j ω) i)
                (EL i ω)))

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- The piece lifts, almost surely, for a relative family `EL`. -/
def PiecesLiftAS (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        PiecesLift κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀)
          (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The concrete rule, split**: run-read driven events making the concrete rule admissible, such that every
everywhere regular family that is `zeroDrv` on the zero events and generates the concrete curves on the driven events
has the per-stage geometry almost surely and satisfies the data clause given its piece lifts. -/
def ConcreteSplitAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ ΦG : ℕ → Ω → ExplState → Prop,
    (∀ j F, (∀ i < j, Measurable (F i)) →
      StageOK (lρ κ b jumps E u l k ω₀ c b' J' m j F) (lG κ b' J' m ΦG j F) (lZ κ b jumps E u l k ω₀ j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt κ b jumps P E u l k ω₀ c b' J' m ΦG EL ∧
      (PiecesLiftAS κ b jumps P E u l k ω₀ c b' J' m EL → RelDataClause κ b jumps P E u l k ω₀ c b' J' m EL)

/-- **Named input: SB2(2)'s concrete rule, split into the per-stage geometry and the clause given the piece lifts.** -/
def SB2LowerConcreteSplitStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ConcreteSplitAt κ b jumps P E u l k ω₀ c b' J'

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The piece lifts from the per-stage geometry**: for a regular family generating the concrete curves on the driven
events, `GeomAt` gives the piece lifts almost surely (`liftRel_of_stageGeom` at finite positive lifetime). -/
theorem piecesLiftAS_of_geomAt {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    {ΦG : ℕ → Ω → ExplState → Prop} {EL : ℕ → Ω → Drv} (hreg : ∀ j ω, IsRegularDriver (EL j ω))
    (hgen : ∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ κ b jumps E u l k ω₀ j EL →
      (EL j ω).2 = capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
      ∀ T < capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω),
        IsGeneratingTrace (EL j ω).1 T (capTrace (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω)))
    (hgeom : GeomAt κ b jumps P E u l k ω₀ c b' J' m ΦG EL) :
    PiecesLiftAS κ b jumps P E u l k ω₀ c b' J' m EL := by
  filter_upwards [hgeom] with ω hω
  intro β₀ hβ hβ0 hβr tL γ hγ i hi hl hflow hstat hseed
  have hev : i % 2 = 0 := of_decide_eq_true hflow
  obtain ⟨hG, hfin, hdeg⟩ := hω β₀ hβ hβ0 hβr tL γ hγ i hi hev hl hstat hseed
  by_cases hdg : (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
      (lD₁ b jumps E ω))).2 = ⊤ ∨ (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps
        (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = 0
  · exact hdeg hdg
  · push Not at hdg
    have hnZ : ω ∉ lZ κ b jumps E u l k ω₀ i EL := by
      simp only [lZ, cZ, mem_ofPred_eq, not_or, not_and]
      exact ⟨by omega, fun h => by omega⟩
    obtain ⟨he₂, hg⟩ := hgen i ω hG hnZ
    exact liftRel_of_stageGeom hγ (hfin hdg.1 hdg.2) hdg.1 he₂ hg (hreg i ω).2.1

/-- **The concrete rule from its split form** (the piece lifts by `piecesLiftAS_of_geomAt`). -/
theorem concreteRuleAt_of_split {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ}
    (h : ConcreteSplitAt κ b jumps P E u l k ω₀ c b' J') : ConcreteRuleAt κ b jumps P E u l k ω₀ c b' J' := by
  intro m hm
  obtain ⟨ΦG, hok, hcl⟩ := h m hm
  refine ⟨ΦG, hok, fun EL hreg hZ hgen => ?_⟩
  obtain ⟨hgeom, hrest⟩ := hcl EL hreg hZ hgen
  exact hrest (piecesLiftAS_of_geomAt hreg hgen hgeom)

/-- The split form gives the concrete rule statement. -/
theorem sb2LowerConcreteRuleStatement_of_split (hS : SB2LowerConcreteSplitStatement.{u}) :
    SB2LowerConcreteRuleStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk
  exact concreteRuleAt_of_split (h₀ c θ hlaunch b' J' h' hb' hT' hG' hk)

/-- **The head-free relative-driver data from the split concrete rule.** -/
theorem sb2LowerRelDriverDataStatement_of_split (hS : SB2LowerConcreteSplitStatement.{u}) :
    SB2LowerRelDriverDataStatement.{u} :=
  sb2LowerRelDriverDataStatement_of_concrete (sb2LowerConcreteRuleStatement_of_split hS)

/-- **SB2(2)'s combined target (R104a) from the split concrete rule and the conditional half.** -/
theorem sb2LowerLaunchLiftStatement_of_concreteSplit (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerConcreteSplitStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_concrete h12 h13 h12₀ h13₀ (sb2LowerConcreteRuleStatement_of_split hS) hcond

end InteractingSLE.Theorem14.SB.Lk
