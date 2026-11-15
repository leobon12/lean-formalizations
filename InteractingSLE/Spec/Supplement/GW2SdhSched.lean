/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdhPair
import InteractingSLE.Spec.Supplement.GW2SdhInst

/-!
# GW2's R11 pair for J32 with the schedule instances (what remains of `RootPairInputs32`)

Packet PROVE-GW2-SDE (round 5). This file plugs the schedule instances of `GW2SdhInst` into the per-stage package and
fixes the near dilations of ruling R112. It then states what is left of `RootPairInputs32` in one structure:

* `SchedVer c r l a`: an announced GB6 version with finite stops at the schedule instance (RELDET's
  `GW2Rd.exists_schedVersionsA*` supply exhausting families of them; the choice of ONE version per history and
  candidate is part of the stop problem S3 of PROVE-GW2-BUF);
* **`PkgFamily.withSched K h13 ver ch`**: the package `K` with its instances replaced by the schedule instances
  (RELDET's good set, the versions `ver`, the choices `ch`);
* **`nearLam`** (`λ = 1` at the empty history, `17/35` otherwise), `nearLam_ne`, **`nearLam_scale`**:
  `λ (17/8 − S) ≤ 17/8` for every start `S ≥ −9/4` (nonempty histories, R112's range `(−9/4, −7/4)`) and `S ≥ 0` at the
  empty history (where `S = 0`);
* **`RootPairInputsSched`**: the inputs that remain, and **`rootPairInputs32_of_sched`**,
  **`retainedComparisons_rootJ32_sched`** (both C24 binders for `RootJ32.constructionFamily`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdh

open GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Rd Supp8.Q3Stop GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6

/-- **An announced GB6 version with finite stops at the schedule instance.** -/
structure SchedVer {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) where
  R : ℝ≥0 → Ω → ℝ
  V : Ω → ℝ≥0∞
  isA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V
  V_ne_top : ∀ ω, V ω ≠ ⊤

/-- Versions for every source setup, root, history and candidate. -/
abbrev SchedVerFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), SchedVer c r l a

/-- Free instance choices for every source setup, root, history and candidate. -/
abbrev SchedChoiceFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_ : ScaledRootIdx c.Θ c.Q)
    (_ : List (EntryIdx c.Θ c.Q)) (_ : ℕ), SchedChoice Ω

/-- **The package with the schedule instances**: `K`'s stops, near families and shells, with every instance replaced
by the schedule instance of RELDET's good set, the version `ver` and the choices `ch`. -/
def _root_.InteractingSLE.Theorem14.GW2Sde.PkgFamily.withSched (K : PkgFamily.{u})
    (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) : PkgFamily.{u} :=
  fun Ω _ _ c r =>
    { K Ω c r with
      inst := fun l a => schedInst c r l a (schedGT h13 c r l a) (ver Ω c r l a).isA (ch Ω c r l a) }

/-! ### The near dilations of ruling R112 -/

/-- **The near dilations**: `1` at the empty history, `17/35` at every other history. -/
def nearLam : NearDil.{u} := fun _ _ _ _ _ l _ => if l.length = 0 then 1 else 17 / 35

theorem nearLam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), nearLam Ω c r l ω ≠ 0 := by
  intro Ω _ _ c r l ω
  unfold nearLam
  split_ifs <;> norm_num

/-- **R112's scale condition for `nearLam`**: `λ (17/8 − S) ≤ 17/8` for a start `S ≥ −9/4` at a nonempty history and
`S ≥ 0` at the empty history. -/
theorem nearLam_scale (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) {S : ℝ}
    (hS : l.length ≠ 0 → -(9 / 4) ≤ S) (h0 : l.length = 0 → 0 ≤ S) :
    (nearLam Ω c r l ω : ℝ) * (2 + 1 / 8 - S) ≤ 2 + 1 / 8 := by
  unfold nearLam
  split_ifs with hl
  · have := h0 hl
    push_cast
    linarith
  · have := hS hl
    push_cast
    linarith

/-! ### What remains -/

/-- **The remaining inputs of the R11 pair for J32 with the schedule instances** (package `K.withSched h13 ver ch`,
near dilations `nearLam`):
* per instance (STAGEMEAN / RELDET): the word map's three properties, a measurable `E₀`, a bounded harmonic extension
  `u₀`, and the open lines inputs `OpenLines`;
* the stops, frame words, near facts, driver identification, start, lifetime and shells (ROOT2 / GW2-BUF / RELDET),
  as in `RootPairInputs32`. -/
structure RootPairInputsSched (K : PkgFamily.{u}) (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop where
  word : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    Measurable (ch Ω c r l a).β ∧ (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
      ∀ y, ((ch Ω c r l a).β y).IsSorted
  measurableSet_E₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), MeasurableSet (ch Ω c r l a).E₀
  u₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), IsBoundedHarmonicExtension c.b c.jumps (ch Ω c r l a).u₀
  openLines : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    OpenLines (schedInst c r l a (schedGT h13 c r l a) (ver Ω c r l a).isA (ch Ω c r l a)) c r l
      (measurable_schedW c r l a)
  nearStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((K.withSched h13 ver ch Ω c r).nearStop l n m a).Good ((K.withSched h13 ver ch Ω c r).inst l a) c r l
  slowStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((K.withSched h13 ver ch Ω c r).slowStop l a).Good ((K.withSched h13 ver ch Ω c r).inst l a) c r l
  words : FrameNWordStatement RootJ32.constructionFamily ((K.withSched h13 ver ch).rootFrameN nearLam)
  nearImg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), RootNearImg32 (K.withSched h13 ver ch) nearLam Ω c r l
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootDriverIdExact (K.withSched h13 ver ch) Ω c r l a
  startFrozen : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStartFrozen32 Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers (K.withSched h13 ver ch) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootShellChoice32 (K.withSched h13 ver ch) Ω c r l a

/-- **`RootPairInputs32` from the remaining inputs**: the instance field is discharged by `schedInst_good_of_reldet`
(RELDET's good set and versions, STAGEMEAN's lines constructor), the dilation field by `nearLam_ne`. -/
theorem rootPairInputs32_of_sched {K : PkgFamily.{u}} {h13 : Exist.Theorem13Statement.{u}}
    {ver : SchedVerFamily.{u}} {ch : SchedChoiceFamily.{u}} (hK : RootPairInputsSched K h13 ver ch) :
    RootPairInputs32 (K.withSched h13 ver ch) nearLam where
  lam_ne := nearLam_ne
  inst Ω _ _ c r l a := schedInst_good_of_reldet h13 c r l a (ver Ω c r l a).isA (ver Ω c r l a).V_ne_top
    (ch Ω c r l a) (hK.word Ω c r l a) (hK.measurableSet_E₀ Ω c r l a) (hK.u₀ Ω c r l a) (hK.openLines Ω c r l a)
  nearStop := hK.nearStop
  slowStop := hK.slowStop
  words := hK.words
  nearImg := hK.nearImg
  driverId := hK.driverId
  startFrozen := hK.startFrozen
  stopCovers := hK.stopCovers
  shell := hK.shell

/-- **Both C24 binders for J32 with the schedule instances** from the remaining inputs (Theorems 1.2–1.3, R48). -/
theorem retainedComparisons_rootJ32_sched (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) (hK : RootPairInputsSched K h13 ver ch) :
    RetainedNearModelsStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} :=
  retainedComparisons_rootJ32 h12p₀ h13₀ h13 (K.withSched h13 ver ch) nearLam (rootPairInputs32_of_sched hK)

end InteractingSLE.Theorem14.GW2Sdh
