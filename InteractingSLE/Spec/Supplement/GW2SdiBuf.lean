/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdiPair
import InteractingSLE.Spec.Supplement.GW2BfJ32Slow
import InteractingSLE.Spec.Supplement.GW2BfJ32Drv

/-!
# GW2's lossy R11 pair for J32 with PROVE-GW2-BUF's slow half (no start input)

Packet PROVE-GW2-SDE (round 6). PROVE-GW2-BUF's committed `GW2Bf.retainedBuffer_slow_rootJ32` proves the slow field
of the buffer statement for J32 and round 3's slow comparisons with the stage START DISCHARGED (the retained
functional `GW2Bf.histStart`, `GW2Bf.ae_j32Start_eq_histStart`). The slow comparisons of the dilated family
`comparisonFamilyN (K.rootFrameN lam)` are round 3's by `rfl` (`GW2Sdh.rootFrameN_slow`). So the lossy J32 pair
needs only BUF's three slow items: the driver identification `GW2Bf.J32DriverId` (definitionally round 5's
`GW2Sdh.RootDriverId32`; BUF's `GW2Bf.j32DriverId_of_hull` reduces it to the instance's re-centred hull identity),
the stop cover `GW2Sdg.RootStopCovers`, and the shell choice `GW2Bf.J32ShellChoice` (start `histStart`).

* `j32DriverId_of_exact`: BUF's form from GEOM2's exact-horizon form (round 5's bridge);
* **`RootPairInputs32LB K lam`**, **`retainedComparisonsLossy_rootJ32B`**;
* **`RootPairInputsSchedLB Kb h13 ver ch`**, **`retainedComparisonsLossy_rootJ32B_sched`** (round 5's schedule
  instances, dilations `nearLam`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdi

open GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6
  GW2TipSystem.RootN4

/-- BUF's driver identification from GEOM2's exact-horizon form (Theorem 1.3). -/
theorem j32DriverId_of_exact (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u}) (Ω : Type u)
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : RootDriverIdExact K Ω c r l a) : GW2Bf.J32DriverId K Ω c r l a :=
  rootDriverId32_of_exact h13 K Ω c r l a h

/-- **The named inputs of the lossy R11 pair for J32 with BUF's slow half**: as `RootPairInputs32L`, with the slow
items of `GW2Bf.retainedBuffer_slow_rootJ32` for `K 0` (no start input). -/
structure RootPairInputs32LB (K : ℕ → PkgFamily.{u}) (lam : NearDil.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  inst : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K k Ω c r).inst l a).Good c r l
  nearStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((K k Ω c r).nearStop l n m a).Good ((K k Ω c r).inst l a) c r l
  slowStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k' : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k' + 4 → ∀ a : ℕ,
      ((K k Ω c r).slowStop l a).Good ((K k Ω c r).inst l a) c r l
  words : ∀ k : ℕ, FrameNWordStatement RootJ32.constructionFamily ((K k).rootFrameN lam)
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    RootNearImg32L (K k) lam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32DriverId (K 0) Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers (K 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32ShellChoice (K 0) Ω c r l a

/-- **Both C24 binders for J32, lossy near binder, with BUF's slow half** (R114; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossy_rootJ32B (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : ℕ → PkgFamily.{u})
    (lam : NearDil.{u}) (hK : RootPairInputs32LB K lam) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} := by
  have hsde : ∀ k, RetainedStoppedSDEStatement RootJ32.constructionFamily (comparisonFamilyN ((K k).rootFrameN lam)) :=
    fun k => retainedStoppedSDEStatement_rootFrameN h12p₀ h13₀ h13 hK.lam_ne (hK.inst k) (hK.nearStop k)
      (hK.slowStop k) (hK.words k)
  refine retainedComparisonsLossy_of_stoppedSDE_buffer RootJ32.constructionFamily
    (fun k => comparisonFamilyN ((K k).rootFrameN lam)) hsde ?_ ?_
  · intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_rootFrameN (K k) lam Ω c r l (hK.lam_ne Ω c r l) (hK.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  · exact GW2Bf.retainedBuffer_slow_rootJ32 h13 (K 0) hK.driverId hK.stopCovers hK.shell

/-- **The remaining inputs of the lossy R11 pair for J32 with the schedule instances and BUF's slow half.** -/
structure RootPairInputsSchedLB (Kb : ℕ → PkgFamily.{u}) (h13 : Exist.Theorem13Statement.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) : Prop where
  word : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    Measurable (ch Ω c r l a).β ∧ (range fun y => Supp8.Q3Stop.wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
      ∀ y, ((ch Ω c r l a).β y).IsSorted
  measurableSet_E₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), MeasurableSet (ch Ω c r l a).E₀
  u₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), IsBoundedHarmonicExtension c.b c.jumps (ch Ω c r l a).u₀
  openLines : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    OpenLines (schedInst c r l a (schedGT h13 c r l a) (ver Ω c r l a).isA (ch Ω c r l a)) c r l
      (GW2Rd.measurable_schedW c r l a)
  nearStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      (((Kb k).withSched h13 ver ch Ω c r).nearStop l n m a).Good (((Kb k).withSched h13 ver ch Ω c r).inst l a) c r l
  slowStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k' : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k' + 4 → ∀ a : ℕ,
      (((Kb k).withSched h13 ver ch Ω c r).slowStop l a).Good (((Kb k).withSched h13 ver ch Ω c r).inst l a) c r l
  words : ∀ k : ℕ, FrameNWordStatement RootJ32.constructionFamily (((Kb k).withSched h13 ver ch).rootFrameN nearLam)
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    RootNearImg32L ((Kb k).withSched h13 ver ch) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32DriverId ((Kb 0).withSched h13 ver ch) Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers ((Kb 0).withSched h13 ver ch) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32ShellChoice ((Kb 0).withSched h13 ver ch) Ω c r l a

theorem rootPairInputs32LB_of_sched {Kb : ℕ → PkgFamily.{u}} {h13 : Exist.Theorem13Statement.{u}}
    {ver : SchedVerFamily.{u}} {ch : SchedChoiceFamily.{u}} (hK : RootPairInputsSchedLB Kb h13 ver ch) :
    RootPairInputs32LB (fun k => (Kb k).withSched h13 ver ch) nearLam where
  lam_ne := nearLam_ne
  inst _ Ω _ _ c r l a := schedInst_good_of_reldet h13 c r l a (ver Ω c r l a).isA (ver Ω c r l a).V_ne_top
    (ch Ω c r l a) (hK.word Ω c r l a) (hK.measurableSet_E₀ Ω c r l a) (hK.u₀ Ω c r l a) (hK.openLines Ω c r l a)
  nearStop := hK.nearStop
  slowStop := hK.slowStop
  words := hK.words
  nearImg := hK.nearImg
  driverId := hK.driverId
  stopCovers := hK.stopCovers
  shell := hK.shell

/-- **Both C24 binders for J32 with the schedule instances, the lossy near binder and BUF's slow half** (R114;
Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossy_rootJ32B_sched (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (Kb : ℕ → PkgFamily.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) (hK : RootPairInputsSchedLB Kb h13 ver ch) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} :=
  retainedComparisonsLossy_rootJ32B h12p₀ h13₀ h13 _ nearLam (rootPairInputs32LB_of_sched hK)

end InteractingSLE.Theorem14.GW2Sdi
