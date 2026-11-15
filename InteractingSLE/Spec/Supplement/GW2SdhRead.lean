/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdhFrame
import InteractingSLE.Spec.Supplement.GW2SdgRead
import InteractingSLE.Spec.Supplement.GW2GmJ32Iface

/-!
# GW2's slow buffer reads for J32 (rulings R110, R112)

Packet PROVE-GW2-SDE (round 5). Ruling R110 re-targets the D-specific GW2 work from `RootJ31.constructionFamily` to
`RootJ32.constructionFamily`. J32 shares J31's sample lifetime, buffer, records and retained gate (`GW2GmJ32Data`,
`GW2GmJ32Iface`); its reads use J32's running-maximum capacity driver reader. This file re-proves round 4's slow half
(`GW2Sdg.slowBufferFact_rootFrame`) for J32 and the comparison family with dilated near comparisons
(`comparisonFamilyN (K.rootFrameN lam)`, whose slow data are round 3's):

* J32's reads: `rootRead32` (J32's capacity driver reader of the future pair), `rootStart32` (the start value);
  `sourceSample32_fst` (lifetime `= 4^{r.2} · gain`, shared with J31) and **`sourceSample32_snd`** (the read is
  `rootStart32 + (−1)^{|l|} 2^{r.2} (D₃₂(F_T + q/4^{r.2}) − D₃₂(F_T))`);
* the named inputs: **`RootDriverId32`** (on the retained gate, the centred J32 reads before the buffer are the stage
  relative driver), **`RootStartFrozen32`**, **`RootShellChoice32`** (J32-alive histories); the lifetime input is
  round 4's `GW2Sdg.RootStopCovers` (J32's lifetime is J31's);
* the exact-horizon form of (a): `rootReadExact` (I30's reader of the joined trace with the horizon `T + F`, the form
  of GEOM2's agreement `RootJ32.ae_capacityDriverRead_eq`), `RootDriverIdExact`, and the bridge
  **`rootDriverId32_of_exact`** (Theorem 1.3);
* **`slowBufferFact_rootFrame32`**, **`retainedBuffer_slow_rootFrame32`** (the `slow` field of
  `RetainedBufferStatement RootJ32.constructionFamily (comparisonFamilyN (K.rootFrameN lam))`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdh

open GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 Restart Sec5
  Exist.StagedLaw

/-! ### J32's sample in the joint chart -/

section Root

variable {Ω : Type u} [MeasurableSpace Ω]

/-- J32's capacity driver read of the future pair at a joint-chart capacity `u`. -/
def rootRead32 (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (u : ℝ≥0)
    (ξ : Ω) : ℝ :=
  RootJ32.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) u
    (RootJ31.futurePair c r l a ξ)

/-- **J32's start value** `(−1)^{|l|} 2^{r.2} (D₃₂(F_T) − D₃₂(F_{v₀}))`. -/
def rootStart32 (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) :
    ℝ :=
  (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
    (rootRead32 c r l a (rootHistCap c r l a ξ) ξ -
      rootRead32 c r l a (rootCapAt c r l a (rootEntry r.1).2 ξ).toNNReal ξ)

/-- I30's exact-horizon reader of the joined trace at the buffer horizon `T + F` (the right side of GEOM2's
agreement `RootJ32.ae_capacityDriverRead_eq`). -/
def rootReadExact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (u : ℝ≥0)
    (ξ : Ω) : ℝ :=
  RootJ31.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) u
    (cfRec c.s c.W c.ζ ξ, recOf ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞)
      (Gm.futureJoined c r l a ξ, ⊤))

/-- **J32's sample lifetime** is `4^{r.2}` times the capacity gained up to the buffer (as J31's). -/
theorem sourceSample32_fst (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ξ : Ω) : (RootJ32.sourceSample c r l a ξ).1 = (4 : ℝ≥0∞) ^ r.2 * (rootGain c r l a ξ : ℝ≥0∞) :=
  (RootJ32.sourceSample_fst c r l a ξ).trans (sourceSample_fst c r l a ξ)

/-- **J32's live reads** in terms of J32's centred capacity driver read after the history. -/
theorem sourceSample32_snd (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ξ : Ω) {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1) :
    (RootJ32.sourceSample c r l a ξ).2 q = rootStart32 c r l a ξ +
      (-1) ^ l.length * ((2 : ℝ) ^ r.2 *
        (rootRead32 c r l a (rootHistCap c r l a ξ + (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2) ξ -
          rootRead32 c r l a (rootHistCap c r l a ξ) ξ)) := by
  rw [RootJ32.sourceSample_read c r l a ξ hq]
  simp only [RootJ32.sourceDriver, RootJ32.stageDriverRead, rootStart32, rootRead32, rootHistCap, rootCapAt]
  rw [two_pow_sq]
  push_cast
  ring

end Root

/-! ### The named per-stage inputs for J32 -/

section Inputs

variable (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **Input (a) for J32**: on the retained gate, before the sample's buffer, J32's capacity driver read after the
history, centred at the history's capacity, is the stage relative driver of the candidate's instance. -/
def RootDriverId32 : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ u : ℝ≥0, u < rootGain c r l a ξ →
    rootRead32 c r l a (rootHistCap c r l a ξ + u) ξ - rootRead32 c r l a (rootHistCap c r l a ξ) ξ =
      ((K Ω c r).inst l a).drv c u ξ

/-- **Input (a) in the exact-horizon form** (RELDET / GEOM2): the same identification for I30's reader of the joined
trace at the buffer horizon. -/
def RootDriverIdExact : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ u : ℝ≥0, u < rootGain c r l a ξ →
    rootReadExact c r l a (rootHistCap c r l a ξ + u) ξ - rootReadExact c r l a (rootHistCap c r l a ξ) ξ =
      ((K Ω c r).inst l a).drv c u ξ

/-- **Input (b) for J32, the frozen start**: on the retained gate, J32's start value is determined by the retained
history up to a null set. -/
def RootStartFrozen32 : Prop :=
  ∃ S : Ω → ℝ, Measurable[c.sigma r l] S ∧ ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → rootStart32 c r l a ξ = S ξ

/-- The shell choice for J32: the shell clauses for ROOT2's drift bound and the shell's start at J32's start value,
on the J32-alive histories. -/
def RootShellChoice32 : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
    ShellFact c.κ (RootJ31.sourceDriftBound c r) ((K Ω c r).slowShell l a ω) ∧
      ((K Ω c r).slowShell l a ω).start = rootStart32 c r l a ω

end Inputs

/-- Capacities below the gain lie below the capacity at the buffer. -/
theorem le_capAt_of_lt_gain {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) {u : ℝ≥0} (hu : u < rootGain c r l a ξ) {v : ℝ≥0} (hv : v ≤ u) :
    ((rootHistCap c r l a ξ + v : ℝ≥0) : ℝ) ≤
      RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ)
        (RootJ31.futurePair c r l a ξ) := by
  have h0 : 0 ≤ rootCapAt c r l a (RootJ31.historyTime c r l) ξ :=
    RootJ32.forwardCapacity_nonneg (rootPt r.1) c.s _ _
  have hu' : (u : ℝ) < rootCapAt c r l a (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) ξ -
      rootCapAt c r l a (RootJ31.historyTime c r l) ξ := by
    have := (Real.lt_toNNReal_iff_coe_lt).1 hu
    exact this
  have hv' : (v : ℝ) ≤ u := hv
  simp only [rootHistCap, NNReal.coe_add, Real.coe_toNNReal _ h0]
  simp only [rootCapAt] at hu' h0 ⊢
  linarith

/-- **Input (a) for J32 from its exact-horizon form**, by GEOM2's agreement (Theorem 1.3). -/
theorem rootDriverId32_of_exact (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u}) (Ω : Type u)
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : RootDriverIdExact K Ω c r l a) : RootDriverId32 K Ω c r l a := by
  filter_upwards [RootJ32.ae_capacityDriverRead_eq h13 c r, h] with ξ hag hex hg u hu
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    rw [sourceSample_fst]
    have hg0 : (0 : ℝ≥0∞) < (rootGain c r l a ξ : ℝ≥0∞) := ENNReal.coe_pos.2 (lt_of_le_of_lt zero_le hu)
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) hg0.ne'
  have e1 : rootRead32 c r l a (rootHistCap c r l a ξ + u) ξ = rootReadExact c r l a (rootHistCap c r l a ξ + u) ξ :=
    hag l a hlive _ (le_capAt_of_lt_gain c r l a ξ hu le_rfl)
  have e2 : rootRead32 c r l a (rootHistCap c r l a ξ) ξ = rootReadExact c r l a (rootHistCap c r l a ξ) ξ := by
    have := hag l a hlive (rootHistCap c r l a ξ + 0) (le_capAt_of_lt_gain c r l a ξ hu zero_le)
    rwa [add_zero] at this
  rw [e1, e2]
  exact hex hg u hu

/-- **The slow buffer fact for J32 against the comparison family with dilated near comparisons**, from the named
inputs. -/
theorem slowBufferFact_rootFrame32 (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hid : RootDriverId32 K Ω c r l a) (hst : RootStartFrozen32 Ω c r l a) (hcov : RootStopCovers K Ω c r l a)
    (hsh : RootShellChoice32 K Ω c r l a) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      SlowBufferFact ((comparisonFamilyN (K.rootFrameN lam) Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((RootJ32.constructionFamily Ω c).experiment r).driftBound
        (((RootJ32.constructionFamily Ω c).experiment r).data.sample l a) := by
  obtain ⟨S, hSm, hSe⟩ := hst
  have hW : ∀ q : ℝ≥0, ∀ ξ : Ω, (K.rootFrame.frame Ω c r).drv l ((K.rootFrame.frame Ω c r).slowVar l a) q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c (q / (4 : ℝ≥0) ^ r.2) ξ) := fun q ξ => by
    rw [← rootFrame_slow_W K Ω c r l a ξ q ξ]
    exact congrFun (congrFun (slowData_W (K.rootFrame.frame Ω c r) l a ξ).symm q) ξ
  have hT : ∀ ξ : Ω, (K.rootFrame.frame Ω c r).stop ((K.rootFrame.frame Ω c r).slowVar l a) ξ =
      (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).slowStop l a).stop ξ := fun ξ => by
    rw [← rootFrame_slow_stop K Ω c r l a ξ ξ]
    exact congrFun (slowData_stop (K.rootFrame.frame Ω c r) l a ξ).symm ξ
  have hread : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 → (RootJ32.sourceSample c r l a ξ).2 q =
        S ξ + (K.rootFrame.frame Ω c r).drv l ((K.rootFrame.frame Ω c r).slowVar l a) q ξ := by
    filter_upwards [hid, hSe] with ξ h hξ hg q hq
    rw [sourceSample32_snd c r l a ξ hq, hW, hξ hg,
      h hg _ (div_four_pow_lt r.2 ((sourceSample32_fst c r l a ξ) ▸ hq))]
  have hlife : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → (RootJ32.sourceSample c r l a ξ).1 ≤
      (K.rootFrame.frame Ω c r).stop ((K.rootFrame.frame Ω c r).slowVar l a) ξ := by
    filter_upwards [hcov] with ξ h hg
    have h' := h hg
    rw [sourceSample32_fst, hT]
    gcongr
  filter_upwards [slowBufferFact_of_read (K.rootFrame.frame Ω c r) l a (RootJ31.sourceDriftBound c r)
    (RootJ32.sourceSample c r l a) (RootK32.measurableSet_sourceBuffer_gate c r l) hSm hread hlife, hsh, hSe]
    with ω h hω hSω halive
  have hspec := RootJ32.alive_spec c r l ω halive
  have hg : ω ∈ rootGate c r l := ⟨hspec.1, hspec.2.1⟩
  obtain ⟨h1, h2⟩ := hω halive
  exact h hg h1 (h2.trans (hSω hg))

/-- **The `slow` field of `RetainedBufferStatement RootJ32.constructionFamily (comparisonFamilyN (K.rootFrameN lam))`**
from the named inputs on the slow histories. -/
theorem retainedBuffer_slow_rootFrame32 (K : PkgFamily.{u}) (lam : NearDil.{u})
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootDriverId32 K Ω c r l a)
    (hst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStartFrozen32 Ω c r l a)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStopCovers K Ω c r l a)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootShellChoice32 K Ω c r l a)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)) (hl : l.length = 2 * k + 4) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      SlowBufferFact ((comparisonFamilyN (K.rootFrameN lam) Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((RootJ32.constructionFamily Ω c).experiment r).driftBound
        (((RootJ32.constructionFamily Ω c).experiment r).data.sample l a) :=
  slowBufferFact_rootFrame32 K lam Ω c r l a (hid Ω c r k l hl a) (hst Ω c r k l hl a) (hcov Ω c r k l hl a)
    (hsh Ω c r k l hl a)

end InteractingSLE.Theorem14.GW2Sdh
