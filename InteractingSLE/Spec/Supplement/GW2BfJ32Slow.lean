/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfJ32Start

/-!
# The slow buffer fact for J32 in ROOT2's frame

Packet PROVE-GW2-BUF (rulings R110, R112). JOINTDET's slow buffer fact for `RootJ32.constructionFamily` and
ROOT2's comparison family `comparisonFamilyO K.rootFrame.frame`, on alive histories. The stage start is no longer an
input: it is the retained functional `histStart` (`GW2BfJ32Start.ae_j32Start_eq_histStart`). The remaining inputs
are the three per-stage items:

* **`J32DriverId`** (S1): on ROOT2's retained gate, J32's capacity driver increments after the history's capacity
  are the stage relative driver of the candidate's instance;
* `GW2Sdg.RootStopCovers` (S3): the slow stage stop dominates the capacity gained up to the buffer (the sample's
  lifetime is J31's, so this is SDE's input verbatim);
* the shell choice (S4): on alive histories the shell clauses hold and the shell starts at `histStart`.

Declarations:
* `j32Sample_fst`, **`j32Sample_snd`**: J32's sample lifetime and its live read `histStart`-free form;
* `v0_le_historyTime`: a time-ordered history ends after the root time;
* **`ae_slowBufferFact_rootJ32`**: the slow buffer fact at P-a.e. alive history;
* **`retainedBuffer_slow_rootJ32`**: the slow field of `RetainedBufferStatement` for J32.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open Exist Staged StagedLaw Restart GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24

section Sample

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **J32's sample lifetime** is `4^{r.2}` times the capacity gained up to the buffer (J31's). -/
theorem j32Sample_fst (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ξ : Ω) : (RootJ32.sourceSample c r l a ξ).1 = (4 : ℝ≥0∞) ^ r.2 * (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) := by
  rw [RootJ32.sourceSample_fst, GW2Sdg.sourceSample_fst]

/-- **J32's live read** is its stage start plus the dilated, oriented increment of J32's reader after the history's
capacity. -/
theorem j32Sample_snd (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ξ : Ω) {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1) :
    (RootJ32.sourceSample c r l a ξ).2 q = j32Start c r l a ξ +
      (-1) ^ l.length * ((2 : ℝ) ^ r.2 *
        (j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2) ξ -
          j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ)) := by
  rw [RootJ32.sourceSample_read c r l a ξ hq]
  simp only [RootJ32.sourceDriver, RootJ32.stageDriverRead, j32Start, j32Read, GW2Sdg.rootHistCap,
    GW2Sdg.rootCapAt]
  rw [GW2Sdg.two_pow_sq]
  push_cast
  ring

/-- A time-ordered history ends after the root time. -/
theorem v0_le_historyTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (h : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l)) :
    (rootEntry r.1).2 ≤ RootJ31.historyTime c r l := by
  rw [GW2Sde.historyTime_eq_lastTime]
  exact Gm.le_lastTime_of_mem h _ (List.mem_cons_self ..)

end Sample

section Inputs

variable (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **Input (S1) for J32, the centred capacity driver identification**: on ROOT2's retained gate, before the
buffer, J32's capacity driver read after the history, centred at the history's capacity, is the stage relative
driver of the candidate's instance. -/
def J32DriverId : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
    j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ - j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
      ((K Ω c r).inst l a).drv c u ξ

/-- **The shell choice for J32** (S4): on alive histories, the shell clauses for the drift bound and the shell's
start at the history start functional. -/
def J32ShellChoice : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive
      ((RootJ32.constructionFamily Ω c).G r) l →
    GW2Sdg.ShellFact c.κ (RootJ31.sourceDriftBound c r) ((K Ω c r).slowShell l a ω) ∧
      ((K Ω c r).slowShell l a ω).start = histStart c r l ω

end Inputs

/-- The slow comparison driver of ROOT2's frame, at the frame level. -/
theorem rootFrame_slow_drv (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) (ξ : Ω) :
    (K.rootFrame.frame Ω c r).drv l ((K.rootFrame.frame Ω c r).slowVar l a) q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c (q / (4 : ℝ≥0) ^ r.2) ξ) := by
  rw [← GW2Sdg.slowData_W _ l a ξ]
  exact rootFrame_slow_W K Ω c r l a ξ q ξ

/-- The slow comparison stop of ROOT2's frame, at the frame level. -/
theorem rootFrame_slow_stop' (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) :
    (K.rootFrame.frame Ω c r).stop ((K.rootFrame.frame Ω c r).slowVar l a) ξ =
      (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).slowStop l a).stop ξ := by
  rw [← GW2Sdg.slowData_stop _ l a ξ]
  exact rootFrame_slow_stop K Ω c r l a ξ ξ

/-- **The slow buffer fact for J32** at P-a.e. alive history, from the driver identification (S1), the stop cover
(S3) and the shell choice (S4) (Theorem 1.3 for the live clock). -/
theorem ae_slowBufferFact_rootJ32 (h13 : Theorem13Statement.{u}) (K : PkgFamily.{u}) (Ω : Type u)
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hdrv : J32DriverId K Ω c r l a)
    (hstop : GW2Sdg.RootStopCovers K Ω c r l a) (hshell : J32ShellChoice K Ω c r l a) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive
        ((RootJ32.constructionFamily Ω c).G r) l →
      SlowBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω)
        (condExpKernel c.P (c.sigma r l) ω) (RootJ31.sourceDriftBound c r) (RootJ32.sourceSample c r l a) := by
  by_cases hord : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l)
  · have hv₀ := v0_le_historyTime c r l hord
    have hG : MeasurableSet[c.sigma r l] (GW2Sdg.rootGate c r l) :=
      RootK32.measurableSet_sourceBuffer_gate c r l
    have hread : ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → ∀ q : ℚ≥0,
        ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
        (RootJ32.sourceSample c r l a ξ).2 q = histStart c r l ξ +
          (K.rootFrame.frame Ω c r).drv l ((K.rootFrame.frame Ω c r).slowVar l a) q ξ := by
      filter_upwards [ae_j32Start_eq_histStart h13 c r l hv₀, hdrv] with ξ hst hd hξG q hq
      have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
        lt_of_le_of_lt zero_le (hq.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
      have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < GW2Sdg.rootGain c r l a ξ :=
        GW2Sdg.div_four_pow_lt r.2 (by rw [← j32Sample_fst]; exact hq)
      rw [j32Sample_snd c r l a ξ hq, hst a hlive, hd hξG _ hu, rootFrame_slow_drv]
    have hlife : ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l →
        (RootJ32.sourceSample c r l a ξ).1 ≤
          (K.rootFrame.frame Ω c r).stop ((K.rootFrame.frame Ω c r).slowVar l a) ξ := by
      filter_upwards [hstop] with ξ hs hξG
      rw [j32Sample_fst, rootFrame_slow_stop']
      gcongr
      exact hs hξG
    filter_upwards [GW2Sdg.slowBufferFact_of_read (K.rootFrame.frame Ω c r) l a (RootJ31.sourceDriftBound c r)
      (RootJ32.sourceSample c r l a) hG (measurable_histStart c r l) hread hlife, hshell] with ω h1 h2 halive
    obtain ⟨hcov, hold, -⟩ := RootJ32.alive_spec c r l ω halive
    exact h1 ⟨hcov, hold⟩ (h2 halive).1 (h2 halive).2
  · exact Eventually.of_forall fun ω halive => absurd (RootJ32.alive_spec c r l ω halive).2.2 hord

/-- **The slow field of `RetainedBufferStatement` for J32** in ROOT2's frame, from the per-stage items. -/
theorem retainedBuffer_slow_rootJ32 (h13 : Theorem13Statement.{u}) (K : PkgFamily.{u})
    (hdrv : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
        J32DriverId K Ω c r l a)
    (hstop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
        GW2Sdg.RootStopCovers K Ω c r l a)
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
        J32ShellChoice K Ω c r l a) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
      ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive
          ((RootJ32.constructionFamily Ω c).G r) l →
        SlowBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω)
          (condExpKernel c.P (c.sigma r l) ω) ((RootJ32.constructionFamily Ω c).experiment r).driftBound
          (((RootJ32.constructionFamily Ω c).experiment r).data.sample l a) :=
  fun Ω _ _ c r k l hl a => ae_slowBufferFact_rootJ32 h13 K Ω c r l a (hdrv Ω c r k l hl a)
    (hstop Ω c r k l hl a) (hshell Ω c r k l hl a)

end InteractingSLE.Theorem14.GW2Bf
