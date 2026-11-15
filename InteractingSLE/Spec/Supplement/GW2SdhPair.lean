/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdhRead
import InteractingSLE.Spec.Supplement.GW2SdgPair

/-!
# GW2's R11 pair for J32 with dilated near comparisons (rulings R110, R112)

Packet PROVE-GW2-SDE (round 5). Round 4's `GW2Sdg.retainedComparisons_rootJ31` re-targeted to J32
(`RootJ32.constructionFamily`) and to the comparison family with per-history near dilations
(`comparisonFamilyN (K.rootFrameN lam)`, `GW2SdhFrame`):

* **`RootNearImg32 K lam`**: the near facts for J32 in terms of the actual stage driver, DILATED by `λ = lam l ω`
  (comparison driver `(−1)^{|l|} 2^{r.2} λ R(·/(4^{r.2} λ²))`, stop `4^{r.2} λ² τ`), with J32's sample;
  `nearImgPath_rootFrameN`, **`retainedBuffer_near_rootFrameN`** (via round 4's image-state reduction);
* **`RootPairInputs32 K lam`**: the complete list of named inputs (the near dilations nonzero, round 2's per-stage
  targets, the frame words with dilated near words, `RootNearImg32`, (a) in GEOM2's exact-horizon form, (b), (c),
  the shell choice);
* **`retainedPair_rootJ32`** (both R11 properties for the same comparison family) and
  **`retainedComparisons_rootJ32`** (both C24 binders for `RootJ32.constructionFamily`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdh

open GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4

/-- **The near facts for J32 with dilated near comparisons** (ROOT2 / GW2-BUF): for the comparison driver
`(−1)^{|l|} 2^{r.2} λ R(·/(4^{r.2} λ²))` (`λ = lam Ω c r l ω`, `R` the stage relative driver of the selected candidate's
instance) and the stop `4^{r.2} λ² τ`, the stop is positive, the image state at the stop is outside the buffer, and an
image-state visit of the target before the stop puts J32's sample in the reach set. -/
def RootNearImg32 (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
    ∀ n : ℕ, ∀ᶠ m in atTop, ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω),
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

/-- `RootNearImg32` is `NearImgPath` for J32 and the comparison family with dilated near comparisons. -/
theorem nearImgPath_rootFrameN (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hlam : ∀ ω, lam Ω c r l ω ≠ 0) (h : RootNearImg32 K lam Ω c r l) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearImgPath ((comparisonFamilyN (K.rootFrameN lam) Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ32.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ32.constructionFamily Ω c).experiment r).data.reach l) n m := by
  filter_upwards [h] with ω hω halive n
  filter_upwards [hω halive n] with m hm
  filter_upwards [hm] with ξ hξ
  obtain ⟨h0, hex, htg⟩ := hξ
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

/-- **The `near` field of J32's buffer statement for the comparison family with dilated near comparisons**, from the
SDE half and `RootNearImg32`. -/
theorem retainedBuffer_near_rootFrameN (K : PkgFamily.{u}) (lam : NearDil.{u})
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hsde : RetainedStoppedSDEStatement RootJ32.constructionFamily (comparisonFamilyN (K.rootFrameN lam)))
    (himg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), RootNearImg32 K lam Ω c r l)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearBufferFact ((comparisonFamilyN (K.rootFrameN lam) Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ32.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ32.constructionFamily Ω c).experiment r).data.reach l) n m :=
  retainedBuffer_near_of_imgPath hsde (fun _ _ _ c r l a => RootJ32.experiment_reach_measurable c r l a)
    (fun Ω _ _ c r l => nearImgPath_rootFrameN K lam Ω c r l (hlam Ω c r l) (himg Ω c r l)) Ω c r l

/-- **The named inputs of the R11 pair for J32** with the per-stage package `K` and the near dilations `lam`. -/
structure RootPairInputs32 (K : PkgFamily.{u}) (lam : NearDil.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  inst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).inst l a).Good c r l
  nearStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l
  slowStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l
  words : FrameNWordStatement RootJ32.constructionFamily (K.rootFrameN lam)
  nearImg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), RootNearImg32 K lam Ω c r l
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootDriverIdExact K Ω c r l a
  startFrozen : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStartFrozen32 Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers K Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootShellChoice32 K Ω c r l a

/-- **Both R11 properties for J32**, for the same comparison family with dilated near comparisons
(Theorems 1.2–1.3, R48). -/
theorem retainedPair_rootJ32 (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u})
    (lam : NearDil.{u}) (hK : RootPairInputs32 K lam) :
    RetainedStoppedSDEStatement RootJ32.constructionFamily (comparisonFamilyN (K.rootFrameN lam)) ∧
      RetainedBufferStatement RootJ32.constructionFamily (comparisonFamilyN (K.rootFrameN lam)) := by
  have hsde := retainedStoppedSDEStatement_rootFrameN h12p₀ h13₀ h13 hK.lam_ne hK.inst hK.nearStop hK.slowStop
    hK.words
  exact ⟨hsde, retainedBuffer_near_rootFrameN K lam hK.lam_ne hsde hK.nearImg,
    retainedBuffer_slow_rootFrame32 K lam
      (fun Ω _ _ c r k l hl a => rootDriverId32_of_exact h13 K Ω c r l a (hK.driverId Ω c r k l hl a))
      hK.startFrozen hK.stopCovers hK.shell⟩

/-- **Both C24 binders for J32** from the named inputs (Theorems 1.2–1.3, R48). -/
theorem retainedComparisons_rootJ32 (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u})
    (lam : NearDil.{u}) (hK : RootPairInputs32 K lam) :
    RetainedNearModelsStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} :=
  have h := retainedPair_rootJ32 h12p₀ h13₀ h13 K lam hK
  retainedComparisons_of_stoppedSDE_buffer _ _ h.1 h.2

end InteractingSLE.Theorem14.GW2Sdh
