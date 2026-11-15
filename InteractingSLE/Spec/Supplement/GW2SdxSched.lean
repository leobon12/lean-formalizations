/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdxPair
import InteractingSLE.Spec.Supplement.GW2SdiInst

/-!
# The schedule-instance pair with the time-order guard (ruling R119, decision D1)

Packet PROVE-GW2-SDE (round 10). Decision D1 for the corrected schedule instances (`GW2Sdi.schedInstS`): the
instance inputs `word`, `measurableSet_E₀`, `u₀`, `openLines` of `RootPairInputsSchedLBS` are asked only on
time-ordered histories, and `StageInst.Good` is concluded only there. (The near and slow stop targets are guarded too;
that only weakens the inputs.)

* **`schedInstS_goodT`** (`StageInst.Good` on time-ordered histories);
* `RootPairInputs32LBT` (`RootPairInputs32LB` with guarded instance and stop targets),
  **`retainedComparisonsLossy_rootJ32BT`**;
* `RootPairInputsSchedLBST` (the successor of `RootPairInputsSchedLBS`), `rootPairInputs32LBT_of_schedST`,
  **`retainedComparisonsLossy_rootJ32B_schedST`** (the successor of the frozen
  `retainedComparisonsLossy_rootJ32B_schedS`);
* decision D3 for instance-built packages: **`PkgFamily.toVX K`** (version `n`'s slow variable from `K n`'s instance
  and slow stop) and **`vpkgXSafe_toVX`** (guarded `Good` targets per version give `VPkgXSafe`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdx

open GW2JDetR11 GW2Rd GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2Sdi GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6
  GW2TipSystem.RootN4 Supp8.GB6.RelDrv Supp8.Q3Stop

/-- **`StageInst.Good` for the corrected schedule instance on time-ordered histories** (decision D1). -/
theorem schedInstS_goodT {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (hV : ∀ ω, V ω ≠ ⊤)
    (ch : SchedChoice Ω)
    (hβ : HistOrdered c r l →
      Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : HistOrdered c r l → MeasurableSet ch.E₀)
    (hu₀ : HistOrdered c r l → IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : HistOrdered c r l →
      OpenLinesS (schedInstS c r l a (schedGT h13 c r l a) hA ch) c r l (measurable_schedW c r l a)) :
    HistOrdered c r l → (schedInstS c r l a (schedGT h13 c r l a) hA ch).Good c r l :=
  fun hTO => schedInstS_good_of_reldet h13 c r l a hA hV ch (hβ hTO) (hE₀ hTO) (hu₀ hTO) (hopen hTO)

/-- **The named inputs of the lossy pair for J32 with BUF's slow half, guarded** (decision D1). -/
structure RootPairInputs32LBT (K : ℕ → PkgFamily.{u}) (lam : NearDil.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  inst : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
      ((K k Ω c r).inst l a).Good c r l
  nearStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ∀ a : ℕ, ((K k Ω c r).nearStop l n m a).Good ((K k Ω c r).inst l a) c r l
  slowStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k' : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k' + 4 →
      HistOrdered c r l → ∀ a : ℕ, ((K k Ω c r).slowStop l a).Good ((K k Ω c r).inst l a) c r l
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

/-- **Both C24 binders for J32, lossy near binder, from guarded inputs** (decision D1; R114; Theorems 1.2–1.3,
R48). -/
theorem retainedComparisonsLossy_rootJ32BT (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : ℕ → PkgFamily.{u})
    (lam : NearDil.{u}) (hK : RootPairInputs32LBT K lam) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} := by
  have hsde : ∀ k, RetainedStoppedSDEStatement RootJ32.constructionFamily (comparisonFamilyN ((K k).rootFrameN lam)) :=
    fun k => retainedStoppedSDEStatement_rootFrameNT h12p₀ h13₀ h13 hK.lam_ne aliveOrdered_rootJ32 (hK.inst k)
      (hK.nearStop k) (hK.slowStop k) (hK.words k)
  refine retainedComparisonsLossy_of_stoppedSDE_buffer RootJ32.constructionFamily
    (fun k => comparisonFamilyN ((K k).rootFrameN lam)) hsde ?_ ?_
  · intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_rootFrameN (K k) lam Ω c r l (hK.lam_ne Ω c r l) (hK.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  · exact GW2Bf.retainedBuffer_slow_rootJ32 h13 (K 0) hK.driverId hK.stopCovers hK.shell

/-- **The successor of `RootPairInputsSchedLBS`** (decision D1): the instance inputs and the stop targets only on
time-ordered histories. -/
structure RootPairInputsSchedLBST (Kb : ℕ → PkgFamily.{u}) (h13 : Exist.Theorem13Statement.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) : Prop where
  word : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
    Measurable (ch Ω c r l a).β ∧ (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
      ∀ y, ((ch Ω c r l a).β y).IsSorted
  measurableSet_E₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
      MeasurableSet (ch Ω c r l a).E₀
  u₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
      IsBoundedHarmonicExtension c.b c.jumps (ch Ω c r l a).u₀
  openLines : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
    OpenLinesS (schedInstS c r l a (schedGT h13 c r l a) (ver Ω c r l a).isA (ch Ω c r l a)) c r l
      (measurable_schedW c r l a)
  nearStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ∀ a : ℕ, (((Kb k).withSchedS h13 ver ch Ω c r).nearStop l n m a).Good
        (((Kb k).withSchedS h13 ver ch Ω c r).inst l a) c r l
  slowStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k' : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k' + 4 →
      HistOrdered c r l → ∀ a : ℕ,
      (((Kb k).withSchedS h13 ver ch Ω c r).slowStop l a).Good (((Kb k).withSchedS h13 ver ch Ω c r).inst l a) c r l
  words : ∀ k : ℕ,
    FrameNWordStatement RootJ32.constructionFamily (((Kb k).withSchedS h13 ver ch).rootFrameN nearLam)
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    RootNearImg32L ((Kb k).withSchedS h13 ver ch) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32DriverId ((Kb 0).withSchedS h13 ver ch) Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers ((Kb 0).withSchedS h13 ver ch) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32ShellChoice ((Kb 0).withSchedS h13 ver ch) Ω c r l a

theorem rootPairInputs32LBT_of_schedST {Kb : ℕ → PkgFamily.{u}} {h13 : Exist.Theorem13Statement.{u}}
    {ver : SchedVerFamily.{u}} {ch : SchedChoiceFamily.{u}} (hK : RootPairInputsSchedLBST Kb h13 ver ch) :
    RootPairInputs32LBT (fun k => (Kb k).withSchedS h13 ver ch) nearLam where
  lam_ne := nearLam_ne
  inst _ Ω _ _ c r l hTO a := schedInstS_goodT h13 c r l a (ver Ω c r l a).isA (ver Ω c r l a).V_ne_top
    (ch Ω c r l a) (fun h => hK.word Ω c r l h a) (fun h => hK.measurableSet_E₀ Ω c r l h a)
    (fun h => hK.u₀ Ω c r l h a) (fun h => hK.openLines Ω c r l h a) hTO
  nearStop := hK.nearStop
  slowStop := hK.slowStop
  words := hK.words
  nearImg := hK.nearImg
  driverId := hK.driverId
  stopCovers := hK.stopCovers
  shell := hK.shell

/-- **Both C24 binders for J32 with the corrected schedule instances, guarded** (decision D1): the successor of
`GW2Sdi.retainedComparisonsLossy_rootJ32B_schedS` (Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossy_rootJ32B_schedST (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (Kb : ℕ → PkgFamily.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) (hK : RootPairInputsSchedLBST Kb h13 ver ch) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} :=
  retainedComparisonsLossy_rootJ32BT h12p₀ h13₀ h13 _ nearLam (rootPairInputs32LBT_of_schedST hK)

/-! ### Decision D3 for instance-built packages -/

/-- **Version-indexed instance packages**: the near data of `K 0`, and version `n`'s slow variable from `K n`'s
instance and slow stop. -/
def _root_.InteractingSLE.Theorem14.GW2Sde.PkgFamily.toVX (K : ℕ → PkgFamily.{u}) : VPkgXFamily.{u} :=
  fun Ω _ _ c r =>
    { nearFamily := (K 0 Ω c r).nearFamily
      nearCandidate := (K 0 Ω c r).nearCandidate
      nearVar := fun l n m a => ((K 0 Ω c r).inst l a).var c r l ((K 0 Ω c r).nearStop l n m a)
      slowShell := (K 0 Ω c r).slowShell
      slowVar := fun l a n => ((K n Ω c r).inst l a).var c r l ((K n Ω c r).slowStop l a) }

/-- **Guarded per-version `Good` targets give the safe laws of the version-indexed instance package** (decisions D1,
D3). -/
theorem vpkgXSafe_toVX {K : ℕ → PkgFamily.{u}}
    (hinst : ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
        ((K n Ω c r).inst l a).Good c r l)
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
        ∀ a : ℕ, ((K 0 Ω c r).nearStop l n m a).Good ((K 0 Ω c r).inst l a) c r l)
    (hslow : ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
        HistOrdered c r l → ∀ a : ℕ, ((K n Ω c r).slowStop l a).Good ((K n Ω c r).inst l a) c r l) :
    VPkgXSafe (PkgFamily.toVX K) where
  nearSafe Ω _ _ c r l hTO n := (hnear Ω c r l hTO n).mono fun _ hm a =>
    ⟨(hinst 0 Ω c r l hTO a).generates _, (hinst 0 Ω c r l hTO a).isSafe (hm a)⟩
  slowSafe n Ω _ _ c r k l hl hTO a :=
    ⟨(hinst n Ω c r l hTO a).generates _, (hinst n Ω c r l hTO a).isSafe (hslow n Ω c r k l hl hTO a)⟩

end InteractingSLE.Theorem14.GW2Sdx
