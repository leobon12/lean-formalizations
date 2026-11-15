/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsFinal
import InteractingSLE.Spec.Supplement.GW1PathKernel
import InteractingSLE.Spec.Supplement.BW1

/-!
# BW1 at a walk launch: the restarted first piece and the deterministic inputs

Packet PROVE-BW1. `GW1Laws.TerminalPathStatement` is BW1's identification inside the conditional world of a walk
launch. Its proof (`BW1TermMain`) restarts the launched piece as the first (and only) instruction of a one-instruction
staged history of the conditional field read in the launch chart, applies the source-form Proposition BW1
(`BW1.BW1Statement`) in that world, identifies the conditional kernels, and lifts the result to the original
probability. This file fixes the restarted objects and states the two deterministic inputs.

* `termSpec θ`: the one-instruction program `⟨0, false, [flow θ ⊤]⟩`;
* `termChart D`, `termSet D`: the chart after the first piece (`g_A − W` in the launch coordinate) and the physical set
  of the root and the piece (`run_termSpec_one`, `stateChart_run_termSpec`, `prefixPhysSet_termSpec`);
* `IsTermRelOf U V D`: BW1's pathwise conclusion in the launch coordinate (`U` is the relative counterflow of `V`
  after removing the piece `D`, through a continuous strictly increasing clock onto `[0, T_A)`);
* **`DetTerminalStatement`** (named, deterministic): the relative driver is a Borel function of `(V, D)`, unique among
  continuous drivers when it exists;
* **`TerminalPhysStatement`** (named, deterministic): the relation in the launch coordinate gives the retained clock
  in physical coordinates (boundary extension of the launch chart, injectivity of its boundary fibres off the old
  union, `GW1Z.ChartFiberStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BW1Term

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair

/-! ### The restarted first piece -/

/-- **The one-instruction program of BW1's first piece**: a flow of angle `θ` from the root `0`, run through its
lifetime (the walks run their pieces for own time `⊤`). -/
abbrev termSpec (θ : ℝ) : ExplSpec := ⟨0, false, [Sum.inl (θ, ⊤)]⟩

/-- **The chart after the first piece**, in the coordinate of the launch chart (`g_A − W`). -/
def termChart (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : Chart := (Chart.id.recenter 0).loewner (stopDrv ⊤ D) (stopTime ⊤ D)

/-- **The physical set of the root and the first piece**, in the coordinate of the launch chart. -/
def termSet (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : Set ℂ :=
  {(0 : ℂ)} ∪ (Chart.id.recenter 0).tipSet (retOf ⊤ D).1 (retOf ⊤ D).2.1

/-- **BW1's pathwise conclusion in the launch coordinate**: `U` is the relative counterflow of `V` after removing the
piece driven by `D`: a continuous strictly increasing clock maps `[0, ∞)` onto `[0, T)`, `T` the first time the tip of
`V` lies in the root or the piece, and the tips of `U` read through `termChart D` and the inversion are the tips of `V`
at the clock times. -/
def IsTermRelOf (U V : ℝ≥0 → ℝ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧
    range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart V (termSet D)} ∧
    ∀ (r : ℝ≥0) (z : ℂ), ((termChart D).trans infinitySourceChart).tipAt U r z ↔
      infinitySourceChart.tipAt V (ℓ r) z

/-- The restarted program runs its single instruction from the root. -/
theorem run_termSpec_one (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps (termSpec θ) D 1 = ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤ := rfl

/-- The chart after the restarted piece (finite lifetime). -/
theorem stateChart_run_termSpec (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hfin : (D 0).2 ≠ ⊤) :
    BW1.stateChart (ExplState.run κ b jumps (termSpec θ) D 1) = termChart (D 0) := by
  rw [run_termSpec_one]
  exact (launch_eq_of_ne_top (ExplState.init 0) 0 (D 0) θ ⊤ (GW1W.min_top_ne_top hfin)).1

/-- The ordinary pieces after a launch: the new piece is appended. -/
theorem pieces_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).1 =
      s.1 ++ [(s.2.2.2.2.1, fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal, min t D.2)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  repeat' first
    | rfl
    | split

/-- A launch does not change the real arcs. -/
theorem arcs_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  repeat' first
    | rfl
    | split

/-- The physical set of the restarted program after its piece. -/
theorem prefixPhysSet_termSpec (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    SB.prefixPhysSet κ b jumps (termSpec θ) D 1 = termSet (D 0) := by
  have e1 := pieces_launch (ExplState.init 0) 0 (D 0) θ ⊤
  have e2 := arcs_launch (ExplState.init 0) 0 (D 0) θ ⊤
  simp only [SB.prefixPhysSet, run_termSpec_one, e1, e2]
  ext z
  simp [ExplState.init, termSet, retOf]

/-! ### The two deterministic inputs -/

/-- **Named deterministic input: the relative counterflow after a first piece is a Borel operation, unique when it
exists.** There are a map `R` (jointly measurable, for the product σ-algebras on paths, in the counterflow driver and
the piece) and a measurable set `G` such that, for every regular counterflow driver `V` (`GW1Path.IsRegCf`) and every
regular piece `D`: `(V, D) ∈ G` iff some continuous driver is the relative counterflow of `V` after `D`
(`IsTermRelOf`); and then `R V D` is regular and is the only continuous such driver. (`G` records existence: for a
single deterministic path the relative capacity need not tend to `∞` at the first visit of the piece.) Deterministic
content: the image of a Loewner chain under the conformal map `g_A − W` of the piece before the first contact
(Schramm–Wilson's coordinate change, `GW4Traverse.relMapC`), uniqueness of a continuous Loewner driver given its hull
family (`GW4Ident.eq_of_fwdHull_eq_comp`), and a Borel version of these constructions (as `GW1Path.DetRetargetStatement`
for the retargeting). -/
def DetTerminalStatement : Prop :=
  ∃ (R : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0 → ℝ) (G : Set ((ℝ≥0 → ℝ) × ((ℝ≥0 → ℝ) × ℝ≥0∞))),
    (∀ t, Measurable fun p : (ℝ≥0 → ℝ) × ((ℝ≥0 → ℝ) × ℝ≥0∞) => R p.1 p.2 t) ∧ MeasurableSet G ∧
    ∀ (V : ℝ≥0 → ℝ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞), GW1Path.IsRegCf V → IsRegularDriver D →
      GW1P.PieceRegular D.1 (min ⊤ D.2) →
      ((V, D) ∈ G ↔ ∃ U : ℝ≥0 → ℝ, Continuous U ∧ IsTermRelOf U V D) ∧
      ((V, D) ∈ G → GW1Path.IsRegCf (R V D) ∧
        ∀ U : ℝ≥0 → ℝ, Continuous U → (IsTermRelOf U V D ↔ U = R V D))

/-- **Named deterministic input: BW1's relation in physical coordinates at a walk launch** (supplement p. 615, "the
terminal geometric correspondence"; Astra follow-up 5 §4.3, "Its physical image under the continuous inverse of (4.6)
is the original endpoint"). Along a run of a boundary walk with regular pieces and stage data, at a launch `2n`
followed by a next launch: if a regular counterflow driver `V`, read through the launch chart and the inversion, never
has a tip in the old union, and a regular driver `Q` is the relative counterflow of `V` after the piece
(`IsTermRelOf`, with clock `ℓ`), then `Q`, read through the post-piece chart, is `V` before its first physical visit of
the new union, through the same clock. Deterministic content: the boundary extension `f` of the launch chart's inverse
(`GW1P.HasProperBdryExt`, `GW2aPiece.tipAt_trans_of_ne_zero`), so that physical tips are `f` of launch-coordinate tips;
the injectivity of `f` off the old union (`GW1Z.ChartFiberStatement`), so that `V`'s first physical visit of the new
union is its first launch-coordinate visit of the root and the piece; and the composition of charts
`stChart (run (2n+1)) = (stChart (run (2n))).trans (termChart D)`. -/
def TerminalPhysStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞), (∀ k, IsRegularDriver (D k)) →
    GW1WalkExit.WalkStageData κ b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right D →
    (∀ k c θ', (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (GW1Z.walkSpec b jumps right) k) (D k).2)) →
    ∀ n : ℕ, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠
        none →
    ∀ V Q : ℝ≥0 → ℝ, GW1Path.IsRegCf V → GW1Path.IsRegCf Q →
      (∀ r z, ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n))).trans
          infinitySourceChart).tipAt V r z →
        z ∉ SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n)) →
      ∀ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ → StrictMono ℓ →
        range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart V (termSet (D (2 * n)))} →
        (∀ (r : ℝ≥0) (z : ℂ), ((termChart (D (2 * n))).trans infinitySourceChart).tipAt Q r z ↔
          infinitySourceChart.tipAt V (ℓ r) z) →
        IsRetainedClock
          ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n))).trans infinitySourceChart)
          ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))).trans
            infinitySourceChart)
          V Q (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1)) ℓ

end InteractingSLE.Theorem14.BW1Term
