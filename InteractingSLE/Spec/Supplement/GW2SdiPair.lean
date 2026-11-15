/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdiLossy
import InteractingSLE.Spec.Supplement.GW2SdhSched

/-!
# GW2's R11 pair for J32 with the lossy near interface (ruling R114)

Packet PROVE-GW2-SDE (round 6). Round 5's J32 pair (`GW2Sdh.retainedComparisons_rootJ32`,
`GW2Sdh.retainedComparisons_rootJ32_sched`) with the near interface made lossy (R114, F-DEATH). The near candidates
are those of ROOT2's buffer selection with conditional loss `(k + 1)⁻¹`, so the package depends on `k`:
`K : ℕ → PkgFamily` (the slow inputs are asked of `K 0`).

* `NearImgPathLossy`, **`nearBufferFactLossy_of_imgPath`** (round 4's image-state reduction, lossy);
* **`RootNearImg32L K lam ε`** (round 5's `RootNearImg32` off a set of conditional probability `≤ ε`),
  `nearImgPathLossy_rootFrameN`;
* **`RootPairInputs32L K lam`** and **`retainedComparisonsLossy_rootJ32`**: the lossy near binder and the slow binder
  for `RootJ32.constructionFamily`;
* **`RootPairInputsSchedL`** and **`retainedComparisonsLossy_rootJ32_sched`**: the same with round 5's schedule
  instances (`PkgFamily.withSched`) and the dilations `nearLam`.
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

/-! ### The image-state reduction, lossy -/

/-- **The lossy near facts with the image state of the comparison driver.** -/
def NearImgPathLossy {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} (z : NearData Ω κ) (μ : Measure Ω)
    (sample : ℕ → Ω → RootV7.DriverRecord) (reach : ℕ → Set RootV7.DriverRecord) (n m : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∃ N : Set Ω, μ N ≤ ε ∧ ∀ᵐ ξ ∂μ, ξ ∉ N → 0 < (z.dynamics n m).stop ξ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) = (z.dynamics n m).stop ξ → v < (n : ℝ≥0) →
      imgState z.family.xL z.family.xR (fun s => (z.dynamics n m).W s ξ) v ∉ nearBuffer z.family n) ∧
    ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (z.dynamics n m).stop ξ →
      imgState z.family.xL z.family.xR (fun s => (z.dynamics n m).W s ξ) t ∈ nearTarget z.family →
      sample (z.candidate n m) ξ ∈ reach (z.candidate n m)

/-- **The lossy near fact from the lossy image-state facts** for stopped comparison dynamics. -/
theorem nearBufferFactLossy_of_imgPath {Ω : Type u} [MeasurableSpace Ω] {κ κ' : ℝ} {z : NearData Ω κ}
    {μ : Measure Ω} {sample : ℕ → Ω → RootV7.DriverRecord} {reach : ℕ → Set RootV7.DriverRecord} {n m : ℕ}
    {ε : ℝ≥0∞} {ρL : Fin z.family.nL → ℝ} {ρR : Fin z.family.nR → ℝ}
    (hst : (z.dynamics n m).IsStopped μ κ' z.family.xL ρL z.family.xR ρR)
    (hreach : MeasurableSet (reach (z.candidate n m))) (h : NearImgPathLossy z μ sample reach n m ε) :
    NearBufferFactLossy z μ sample reach n m ε := by
  obtain ⟨N, hN, hae⟩ := h
  refine ⟨hreach, N, hN, ?_⟩
  filter_upwards [hae, ae_state_eq_of_isStopped hst] with ξ hξ hs hξN
  obtain ⟨h0, hex, htg⟩ := hξ hξN
  refine ⟨h0, fun v hv hvn => ?_, fun t htn ht htar => ?_⟩
  · have hv0 : 0 < v := by
      have : (0 : ℝ≥0∞) < v := hv ▸ h0
      exact_mod_cast this
    rw [hs.2 v hv hv0]
    exact hex v hv hvn
  · rw [hs.1 t ht] at htar
    exact htg t htn ht htar

/-! ### ROOT2's frame with near dilations, J32, lossy -/

/-- **The lossy near facts for J32** in terms of the actual stage driver, dilated by `λ = lam Ω c r l ω`: off a set of
conditional probability at most `ε`, the stop is positive, the image state at the stop is outside the buffer, and an
image-state visit of the target before the stop puts J32's sample in the reach set. -/
def RootNearImg32L (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ε : ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
    ∀ n : ℕ, ∀ᶠ m in atTop, ∃ N : Set Ω, condExpKernel c.P (c.sigma r l) ω N ≤ ε ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∉ N →
      0 < (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
        ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
          ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ →
        v < (n : ℝ≥0) →
        imgState ((K Ω c r).nearFamily l ω).xL ((K Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * lam Ω c r l ω * ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c
            (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ))
          v ∉ nearBuffer ((K Ω c r).nearFamily l ω) n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) →
        (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
          ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ →
        imgState ((K Ω c r).nearFamily l ω).xL ((K Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * lam Ω c r l ω * ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c
            (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ))
          t ∈ nearTarget ((K Ω c r).nearFamily l ω) →
        RootJ32.sourceSample c r l ((K Ω c r).nearCandidate l ω n m) ξ ∈ RootD25.reachSet

theorem nearImgPathLossy_rootFrameN (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    {ε : ℝ≥0∞} (hlam : ∀ ω, lam Ω c r l ω ≠ 0) (h : RootNearImg32L K lam Ω c r l ε) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearImgPathLossy ((comparisonFamilyN (K.rootFrameN lam) Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ32.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ32.constructionFamily Ω c).experiment r).data.reach l) n m ε := by
  filter_upwards [h] with ω hω halive n
  filter_upwards [hω halive n] with m hm
  obtain ⟨N, hN, hae⟩ := hm
  refine ⟨N, hN, ?_⟩
  filter_upwards [hae] with ξ hξ hξN
  obtain ⟨h0, hex, htg⟩ := hξ hξN
  have hW : (fun s => (((comparisonFamilyN (K.rootFrameN lam) Ω c r).near l ω).dynamics n m).W s ξ) =
      fun s => (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * lam Ω c r l ω *
        ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c
          (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ) :=
    funext fun s => rootFrameN_near_W K lam Ω c r l ω n m s ξ
  have hS := rootFrameN_near_stop K lam Ω c r l ω n m ξ (hlam ω)
  refine ⟨hS ▸ h0, fun v hv hvn => ?_, fun t htn ht htar => ?_⟩
  · rw [hW]
    exact hex v (hv.trans hS) hvn
  · rw [hW] at htar
    exact htg t htn (ht.trans_eq hS) htar

/-- **The named inputs of the lossy R11 pair for J32**: packages `K k` whose near candidates select buffers with
conditional loss `(k + 1)⁻¹`; the per-stage targets and words for every `K k`; the lossy near facts; the slow inputs
for `K 0`. -/
structure RootPairInputs32L (K : ℕ → PkgFamily.{u}) (lam : NearDil.{u}) : Prop where
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
      RootDriverIdExact (K 0) Ω c r l a
  startFrozen : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStartFrozen32 Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers (K 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootShellChoice32 (K 0) Ω c r l a

/-- **Both C24 binders for J32 with the lossy near binder** (R114; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossy_rootJ32 (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : ℕ → PkgFamily.{u})
    (lam : NearDil.{u}) (hK : RootPairInputs32L K lam) :
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
  · exact retainedBuffer_slow_rootFrame32 (K 0) lam
      (fun Ω _ _ c r k l hl a => rootDriverId32_of_exact h13 (K 0) Ω c r l a (hK.driverId Ω c r k l hl a))
      hK.startFrozen hK.stopCovers hK.shell

/-! ### With round 5's schedule instances -/

/-- **The remaining inputs of the lossy R11 pair for J32 with the schedule instances** (packages
`(Kb k).withSched h13 ver ch`, dilations `nearLam`). The instance inputs do not depend on `k`. -/
structure RootPairInputsSchedL (Kb : ℕ → PkgFamily.{u}) (h13 : Exist.Theorem13Statement.{u})
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
      RootDriverIdExact ((Kb 0).withSched h13 ver ch) Ω c r l a
  startFrozen : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStartFrozen32 Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers ((Kb 0).withSched h13 ver ch) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootShellChoice32 ((Kb 0).withSched h13 ver ch) Ω c r l a

theorem rootPairInputs32L_of_sched {Kb : ℕ → PkgFamily.{u}} {h13 : Exist.Theorem13Statement.{u}}
    {ver : SchedVerFamily.{u}} {ch : SchedChoiceFamily.{u}} (hK : RootPairInputsSchedL Kb h13 ver ch) :
    RootPairInputs32L (fun k => (Kb k).withSched h13 ver ch) nearLam where
  lam_ne := nearLam_ne
  inst _ Ω _ _ c r l a := schedInst_good_of_reldet h13 c r l a (ver Ω c r l a).isA (ver Ω c r l a).V_ne_top
    (ch Ω c r l a) (hK.word Ω c r l a) (hK.measurableSet_E₀ Ω c r l a) (hK.u₀ Ω c r l a) (hK.openLines Ω c r l a)
  nearStop := hK.nearStop
  slowStop := hK.slowStop
  words := hK.words
  nearImg := hK.nearImg
  driverId := hK.driverId
  startFrozen := hK.startFrozen
  stopCovers := hK.stopCovers
  shell := hK.shell

/-- **Both C24 binders for J32 with the schedule instances and the lossy near binder** (R114; Theorems 1.2–1.3,
R48). -/
theorem retainedComparisonsLossy_rootJ32_sched (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (Kb : ℕ → PkgFamily.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) (hK : RootPairInputsSchedL Kb h13 ver ch) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} :=
  retainedComparisonsLossy_rootJ32 h12p₀ h13₀ h13 _ nearLam (rootPairInputs32L_of_sched hK)

end InteractingSLE.Theorem14.GW2Sdi
