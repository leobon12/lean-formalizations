/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtRule
import InteractingSLE.Spec.Supplement.SB2MoHull
import InteractingSLE.Spec.Supplement.SB4RLift

/-!
# D5's F2a: P-level drivenness of SB2(2)'s stage curves in the canonical chart — the statement

Worker PROVE-R6-CORNER (round 8; F2a moved here from PROVE-SB2-LIFTSET, ruling R121). D5 (`planning/reviews/
DECISIONS-FABLE-2.md`): "almost surely, at each tail stage, the image of B's piece under the canonical relative chart
is a driven curve with continuous, strictly increasing relative capacity" (`Lk.StageOK`'s drivenness read globally,
free of the relative family `EL`).

**The canonical stage curve** (`Dv.canonCurve`): the explored set at relative stage `j` is the upper prefix together
with the lower walk's prefix before its actual stage `j + relOff` (`Dv.stageExpl`, the set of LCMEAN's
`Mq.StageChainAtP`); the canonical chart is the hull chart `Mo.hullChart (fillH X) x₀` (the mapping-out function of the
fill shifted by `x₀`); the actual piece is LIFTSET's v3 point map (`Lk.cΦ3`: the piece launched at `j + relOff`, read
from its visit time of `R` at stage `0`). Its values: the chart image at the good times (point in `ℍ ∖ fill X`), the
limit along the good times elsewhere, read at actual time `u` (infinite lifetime) or `clockOf L u` (finite lifetime
`L`) — LIFTSET's `Lk.stCurvep` with the relative run chart replaced by the canonical chart. Drivenness
(`IsDrivenCurve`) is: continuous from `0`, and on every `[0, S]` the capacity clock is continuous and strictly
increasing and generates the filled prefixes through a continuous driver.

**`Dv.SB2LowerStageDrivenStatement`** (F2a, P-level): in SB2(2)'s setting (`Lf.SB2LowerSetting`'s premises), almost
surely at a launch of the upper schedule at `k`, at every relative stage `j` outside LIFTSET's zero events (`Lk.cZ3`:
odd stages, stage `0` of a zero root, zero shifted lifetime) whose actual piece launches, there is a real offset `x₀`
such that the canonical stage curve is driven.

For the consumers: the relative run chart `stChart s₂` composed with the upper chart is `Mo.physRelChart c (stChart s₂) m`,
which agrees with `Mo.hullChart X x₀'` on `ℍ ∖ X` for some `x₀'` whenever it is a normalized domain chart of `ℍ ∖ X`
(`Mt.physRelChart_eq_hullChart`, given `Mq.StageChainAtP`); on the good times `Lk.stCurvep c m p L s₂` is then
`canonCurve X x₀' p L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Dv

open Lk Lf Lu Lx Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C Sec4
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The canonical stage curve -/

/-- The good times of a piece for an explored set `X`: up to its lifetime, with the point off `fill X` in `ℍ`. -/
def canonGood (X : Set ℂ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) : Set ℝ≥0 :=
  {t | (t : ℝ≥0∞) ≤ L ∧ p t ∈ H \ fillH X}

open Classical in
/-- The canonical stage values: the hull chart's image at the good times, its limit along the good times elsewhere. -/
def canonVal (X : Set ℂ) (x₀ : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (t : ℝ≥0) : ℂ :=
  if t ∈ canonGood X p L then (Mo.hullChart (fillH X) x₀).1 (p t)
  else limUnder (𝓝[canonGood X p L] t) fun t' => (Mo.hullChart (fillH X) x₀).1 (p t')

/-- **The canonical stage curve** on `[0, ∞)`: the canonical values at actual time `u` (infinite lifetime) or
`clockOf L u` (finite lifetime `L`). -/
def canonCurve (X : Set ℂ) (x₀ : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) : ℝ → ℂ :=
  fun u => canonVal X x₀ p L (if L = ⊤ then u else clockOf L.toReal u).toNNReal

/-! ### The stage data of SB2(2)'s lower walk at an upper launch -/

section Stage

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ)

/-- The lower walk's drivers at a sample. -/
abbrev walkD (ω : Ω) : ℕ → Drv := fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω

/-- The relative offset at a sample (the visit point `R = max (A ∩ ℝ)` of the upper prefix). -/
abbrev walkOff (ω : Ω) : ℕ :=
  relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (walkD b jumps E ω)

/-- The lower walk's run state at actual stage `n`. -/
abbrev walkRun (ω : Ω) (n : ℕ) : ExplState :=
  ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkD b jumps E ω) n

/-- **The explored set at relative stage `j`**: the upper prefix and the lower walk's prefix before actual stage
`j + relOff` (LCMEAN's `Mq.StageChainAtP` set). -/
def stageExpl (ω : Ω) (j : ℕ) : Set ℂ :=
  upperPrefix κ b jumps E u l k ω ∪
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkD b jumps E ω)
      (j + walkOff κ b jumps E u l k ω)

/-- **The stage shift** (LIFTSET's `Lk.stageShift` at the launch): the start piece read from its visit time of `R`. -/
abbrev stShift (ω : Ω) (j : ℕ) : ℝ≥0 :=
  stageShift κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun ω => walkD b jumps E ω) j ω

/-- **The actual piece at relative stage `j`** (LIFTSET's v3 point map, `Lk.cΦ3`). -/
def stagePt (ω : Ω) (j : ℕ) : ℝ≥0 → ℂ :=
  fun t => pcPt (walkRun κ b jumps E ω (j + walkOff κ b jumps E u l k ω))
    (walkD b jumps E ω (j + walkOff κ b jumps E u l k ω)) (stShift κ b jumps E u l k ω j + t)

/-- Its (shifted) lifetime. -/
def stageLife (ω : Ω) (j : ℕ) : ℝ≥0∞ :=
  (walkD b jumps E ω (j + walkOff κ b jumps E u l k ω)).2 - stShift κ b jumps E u l k ω j

/-- **The zero stages** (LIFTSET's `Lk.cZ3` at the launch): odd stages, stage `0` of a zero root, zero shifted
lifetime. -/
def ZeroStage (ω : Ω) (j : ℕ) : Prop :=
  j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
    (walkD b jumps E ω)) ∨ stageLife κ b jumps E u l k ω j = 0

end Stage

/-! ### F2a -/

/-- **Named statement (D5's F2a, PROVE-R6-CORNER): P-level drivenness of SB2(2)'s stage curves in the canonical
chart.** In SB2(2)'s setting, almost surely at a launch of the upper schedule at `k`: at every relative stage `j` that
is not a zero stage and whose actual piece launches, for some real offset `x₀` the image of the actual piece under the
canonical chart `Mo.hullChart (fillH (stageExpl …)) x₀` (`canonCurve`) is a driven curve — continuous from `0`, with
continuous strictly increasing relative capacity generated by a continuous driver on every compact time interval. -/
def SB2LowerStageDrivenStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k → ∀ j : ℕ, ¬ ZeroStage κ b jumps E u l k ω j →
        (walkRun κ b jumps E ω (j + walkOff κ b jumps E u l k ω + 1)).2.2.2.1
            (j + walkOff κ b jumps E u l k ω) ≠ none →
        ∃ x₀ : ℝ, IsDrivenCurve (canonCurve (stageExpl κ b jumps E u l k ω j) x₀ (stagePt κ b jumps E u l k ω j)
          (stageLife κ b jumps E u l k ω j))

end InteractingSLE.Theorem14.SB.Dv
