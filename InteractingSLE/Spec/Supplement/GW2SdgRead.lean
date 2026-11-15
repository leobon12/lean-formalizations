/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdfPkg
import InteractingSLE.Spec.Supplement.GW2RootJ31Construction
import InteractingSLE.Spec.Supplement.GW2RootK32Retained
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# GW2's slow buffer reads against the comparison family in the samples' frame

Packet PROVE-GW2-SDE (round 4). ROOT2's remaining target is `RetainedBufferStatement RootJ31.constructionFamily C`
for the SAME `C` as the SDE half; round 3 built that `C` as `comparisonFamilyO K.rootFrame.frame`. This file proves
the slow half of the buffer statement for that `C`. It is reduced to three named per-stage inputs about the actual
samples, and the shell choice.

* `ShellFact κ driftBound z`: the first three clauses of `SlowBufferFact` (they concern only the shell);
* **`slowBufferFact_of_read`** (any oriented frame, any sample, any retained gate `G`): if on `G` the sample reads
  `S + (comparison driver)` P-a.s. with `S` a `c.sigma r l`-measurable start, and its lifetime is below the
  comparison stop P-a.s., then the kernel clauses of `SlowBufferFact` hold at P-a.e. conditioning sample in `G` (`S`
  is frozen and `G` is charged fully by the kernel);
* ROOT2's sample in the joint chart: `rootRead` (capacity driver read of the future pair), `rootHistCap` (capacity of
  the retained history), `rootGain` (capacity gained up to the sample's buffer), `rootStart` (the sample's start
  value), `rootGate` (ROOT2's retained gate: cover event and retained success); `sourceSample_fst`
  (`lifetime = 4^{r.2} · gain`) and **`sourceSample_snd`** (the read is
  `rootStart + (−1)^{|l|} 2^{r.2} (D(F_T + q/4^{r.2}) − D(F_T))`);
* the named inputs, required on the retained gate only: **`RootDriverId`** (the centred capacity driver read is the
  stage relative driver before the buffer), **`RootStartFrozen`** (the start value is `c.sigma r l`-measurable up to
  a null set), **`RootStopCovers`** (the stage stop dominates the capacity gained up to the buffer);
* **`slowBufferFact_rootFrame`**, **`retainedBuffer_slow_rootFrame`** (the `slow` field of
  `RetainedBufferStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame)`), and
  **`retainedBufferStatement_rootFrame`** (with the `near` field as the remaining input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdg

open GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 Restart Sec5

/-- **The shell clauses of `SlowBufferFact`**: separated angles, the literal starting word in `startsU`, and the
drift bound of the shell's force weights. -/
def ShellFact (κ driftBound : ℝ) (z : SlowShell) : Prop :=
  (∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧ (z.start, z.xL, z.xR) ∈ Prop59Stage.startsU ∧
    driftBound = Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀

/-! ### Any oriented frame -/

section Frame

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}

theorem slowData_W (F : FrameO c r) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (F.slowData l a ω).dynamics.W = F.drv l (F.slowVar l a) := by
  simp only [FrameO.slowData, chooseDyn_W]

theorem slowData_stop (F : FrameO c r) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (F.slowData l a ω).dynamics.stop = F.stop (F.slowVar l a) := by
  simp only [FrameO.slowData, chooseDyn_stop]

/-- **The kernel clauses of `SlowBufferFact` from P-a.s. reads on a retained gate.** Let `G` be an event of the
retained σ-algebra. If on `G` the sample reads `S + (comparison driver)` before its lifetime and its lifetime is at
most the comparison stop, both P-a.s., with `S` measurable for the retained σ-algebra, then at P-a.e. conditioning
sample in `G` whose shell starts at `S` the whole slow buffer fact holds (the kernel charges only `G` there). -/
theorem slowBufferFact_of_read (F : FrameO c r) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (driftBound : ℝ)
    (sample : Ω → RootV7.DriverRecord) {G : Set Ω} (hG : MeasurableSet[c.sigma r l] G) {S : Ω → ℝ}
    (hS : Measurable[c.sigma r l] S)
    (hread : ∀ᵐ ξ ∂c.P, ξ ∈ G → ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
      (sample ξ).2 q = S ξ + F.drv l (F.slowVar l a) q ξ)
    (hlife : ∀ᵐ ξ ∂c.P, ξ ∈ G → (sample ξ).1 ≤ F.stop (F.slowVar l a) ξ) :
    ∀ᵐ ω ∂c.P, ω ∈ G → ShellFact c.κ driftBound (F.slowShell l a ω) → (F.slowShell l a ω).start = S ω →
      SlowBufferFact (F.slowData l a ω) (condExpKernel c.P (c.sigma r l) ω) driftBound sample := by
  have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hread, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hlife,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 hS, KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hG]
    with ω hr hlf hfz hGc hωG hsh hst
  have hGξ : ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∈ G := ae_iff.2 (hGc.1 hωG)
  refine ⟨hsh.1, hsh.2.1, hsh.2.2, ?_, ?_⟩
  · filter_upwards [hlf, hGξ] with ξ h hξG
    rw [slowData_stop]
    exact h hξG
  · filter_upwards [hr, hfz, hGξ] with ξ h hξ hξG q hq
    rw [h hξG q hq, hξ, slowData_W]
    change _ = (F.slowShell l a ω).start + _
    rw [hst]

end Frame

/-! ### ROOT2's samples in the joint chart -/

section Root

variable {Ω : Type u} [MeasurableSpace Ω]

/-- ROOT2's capacity driver read of the future pair at a joint-chart capacity `u`. -/
def rootRead (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (u : ℝ≥0)
    (ξ : Ω) : ℝ :=
  RootJ31.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) u
    (RootJ31.futurePair c r l a ξ)

/-- The joint-chart capacity of the future pair's hull at physical time `t`. -/
def rootCapAt (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0)
    (ξ : Ω) : ℝ :=
  RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ)

/-- The joint-chart capacity of the retained history (`F_T`). -/
def rootHistCap (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) :
    ℝ≥0 :=
  (rootCapAt c r l a (RootJ31.historyTime c r l) ξ).toNNReal

/-- The joint-chart capacity gained between the end of the history and the sample's buffer. -/
def rootGain (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) : ℝ≥0 :=
  (rootCapAt c r l a (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) ξ -
    rootCapAt c r l a (RootJ31.historyTime c r l) ξ).toNNReal

/-- **ROOT2's retained gate**: the cover event and the success of the retained history. It is an event of the
retained σ-algebra (`RootK32.measurableSet_sourceBuffer_gate`) and contains every alive history
(`RootK32.sourceBuffer_gate_of_alive`). -/
def rootGate (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Set Ω :=
  {ω | ω ∈ RootCv.coverEvent c r ∧ RootJ31.oldSuccess c r l ω}

/-- **The sample's start value** `(−1)^{|l|} 2^{r.2} (D(F_T) − D(F_{v₀}))`. -/
def rootStart (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) : ℝ :=
  (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
    (rootRead c r l a (rootHistCap c r l a ξ) ξ -
      rootRead c r l a (rootCapAt c r l a (rootEntry r.1).2 ξ).toNNReal ξ)

theorem two_pow_sq (k : ℕ) : ((2 : ℝ≥0) ^ k) ^ 2 = (4 : ℝ≥0) ^ k := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **The sample's lifetime** is `4^{r.2}` times the capacity gained up to the buffer. -/
theorem sourceSample_fst (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ξ : Ω) : (RootJ31.sourceSample c r l a ξ).1 = (4 : ℝ≥0∞) ^ r.2 * (rootGain c r l a ξ : ℝ≥0∞) := by
  simp only [RootJ31.sourceSample, RootJ31.switchedSample, RootJ31.capacityIncrement, rootGain, rootCapAt]
  rw [two_pow_sq]
  push_cast
  rfl

/-- **The sample's live reads** in terms of the centred capacity driver read after the history. -/
theorem sourceSample_snd (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ξ : Ω) {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < (RootJ31.sourceSample c r l a ξ).1) :
    (RootJ31.sourceSample c r l a ξ).2 q = rootStart c r l a ξ +
      (-1) ^ l.length * ((2 : ℝ) ^ r.2 *
        (rootRead c r l a (rootHistCap c r l a ξ + (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2) ξ -
          rootRead c r l a (rootHistCap c r l a ξ) ξ)) := by
  rw [RootJ31.sourceSample_read c r l a ξ hq]
  simp only [RootJ31.sourceDriver, RootJ31.stageDriverRead, rootStart, rootRead, rootHistCap, rootCapAt]
  rw [two_pow_sq]
  push_cast
  ring

end Root

/-! ### The named per-stage inputs and the slow half -/

section Inputs

variable (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **Input (a), the centred capacity driver identification** (ROOT2 / SWITCH): on the retained gate, before the
sample's buffer, the capacity driver read after the history, centred at the history's capacity, is the stage relative
driver of the candidate's instance. -/
def RootDriverId : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ u : ℝ≥0, u < rootGain c r l a ξ →
    rootRead c r l a (rootHistCap c r l a ξ + u) ξ - rootRead c r l a (rootHistCap c r l a ξ) ξ =
      ((K Ω c r).inst l a).drv c u ξ

/-- **Input (b), the frozen start** (ROOT2 / SWITCH): on the retained gate, the start value is determined by the
retained history up to a null set. -/
def RootStartFrozen : Prop :=
  ∃ S : Ω → ℝ, Measurable[c.sigma r l] S ∧ ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → rootStart c r l a ξ = S ξ

/-- **Input (c), the stage stop covers the buffer** (ROOT2): on the retained gate, the slow stage stop dominates the
capacity gained up to the sample's buffer. -/
def RootStopCovers : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → (rootGain c r l a ξ : ℝ≥0∞) ≤ ((K Ω c r).slowStop l a).stop ξ

/-- The shell choice: the shell clauses for ROOT2's drift bound and the shell's start at the sample's start value, on
the alive histories. -/
def RootShellChoice : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive ((RootJ31.constructionFamily Ω c).G r) l →
    ShellFact c.κ (RootJ31.sourceDriftBound c r) ((K Ω c r).slowShell l a ω) ∧
      ((K Ω c r).slowShell l a ω).start = rootStart c r l a ω

end Inputs

theorem div_four_pow_lt {q g : ℝ≥0} (k : ℕ) (h : ((q : ℝ≥0) : ℝ≥0∞) < (4 : ℝ≥0∞) ^ k * (g : ℝ≥0∞)) :
    q / (4 : ℝ≥0) ^ k < g := by
  have h4 : (0 : ℝ≥0) < (4 : ℝ≥0) ^ k := pow_pos (by norm_num) k
  rw [div_lt_iff₀ h4, mul_comm]
  have h' : ((q : ℝ≥0) : ℝ≥0∞) < (((4 : ℝ≥0) ^ k * g : ℝ≥0) : ℝ≥0∞) := by
    push_cast
    exact h
  exact ENNReal.coe_lt_coe.1 h'

/-- **The slow buffer fact for ROOT2's construction against the comparison family in the samples' frame**, from the
named inputs (a)–(c) and the shell choice. -/
theorem slowBufferFact_rootFrame (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hid : RootDriverId K Ω c r l a) (hst : RootStartFrozen Ω c r l a) (hcov : RootStopCovers K Ω c r l a)
    (hsh : RootShellChoice K Ω c r l a) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive ((RootJ31.constructionFamily Ω c).G r) l →
      SlowBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((RootJ31.constructionFamily Ω c).experiment r).driftBound
        (((RootJ31.constructionFamily Ω c).experiment r).data.sample l a) := by
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
      ((q : ℝ≥0) : ℝ≥0∞) < (RootJ31.sourceSample c r l a ξ).1 → (RootJ31.sourceSample c r l a ξ).2 q =
        S ξ + (K.rootFrame.frame Ω c r).drv l ((K.rootFrame.frame Ω c r).slowVar l a) q ξ := by
    filter_upwards [hid, hSe] with ξ h hξ hg q hq
    rw [sourceSample_snd c r l a ξ hq, hW, hξ hg,
      h hg _ (div_four_pow_lt r.2 ((sourceSample_fst c r l a ξ) ▸ hq))]
  have hlife : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → (RootJ31.sourceSample c r l a ξ).1 ≤
      (K.rootFrame.frame Ω c r).stop ((K.rootFrame.frame Ω c r).slowVar l a) ξ := by
    filter_upwards [hcov] with ξ h hg
    have h' := h hg
    rw [sourceSample_fst, hT]
    gcongr
  filter_upwards [slowBufferFact_of_read (K.rootFrame.frame Ω c r) l a (RootJ31.sourceDriftBound c r)
    (RootJ31.sourceSample c r l a) (RootK32.measurableSet_sourceBuffer_gate c r l) hSm hread hlife, hsh, hSe]
    with ω h hω hSω halive
  have hg : ω ∈ rootGate c r l := RootK32.sourceBuffer_gate_of_alive c r l ω halive
  obtain ⟨h1, h2⟩ := hω halive
  exact h hg h1 (h2.trans (hSω hg))

/-- **The `slow` field of `RetainedBufferStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame)`**
from the named inputs on the slow histories. -/
theorem retainedBuffer_slow_rootFrame (K : PkgFamily.{u})
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootDriverId K Ω c r l a)
    (hst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStartFrozen Ω c r l a)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStopCovers K Ω c r l a)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootShellChoice K Ω c r l a)
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)) (hl : l.length = 2 * k + 4) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive ((RootJ31.constructionFamily Ω c).G r) l →
      SlowBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((RootJ31.constructionFamily Ω c).experiment r).driftBound
        (((RootJ31.constructionFamily Ω c).experiment r).data.sample l a) :=
  slowBufferFact_rootFrame K Ω c r l a (hid Ω c r k l hl a) (hst Ω c r k l hl a) (hcov Ω c r k l hl a)
    (hsh Ω c r k l hl a)

/-- **ROOT2's buffer statement for the comparison family of the SDE half**, with the slow half reduced to the named
inputs and the near half as the remaining input. -/
theorem retainedBufferStatement_rootFrame (K : PkgFamily.{u})
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((RootJ31.constructionFamily Ω c).experiment r).data.alive
          ((RootJ31.constructionFamily Ω c).G r) l →
        ∀ n, ∀ᶠ m in atTop, NearBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω)
          (condExpKernel c.P (c.sigma r l) ω) (((RootJ31.constructionFamily Ω c).experiment r).data.sample l)
          (((RootJ31.constructionFamily Ω c).experiment r).data.reach l) n m)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootDriverId K Ω c r l a)
    (hst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStartFrozen Ω c r l a)
    (hcov : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootStopCovers K Ω c r l a)
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a, RootShellChoice K Ω c r l a) :
    RetainedBufferStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame) :=
  ⟨hnear, retainedBuffer_slow_rootFrame K hid hst hcov hsh⟩

end InteractingSLE.Theorem14.GW2Sdg
