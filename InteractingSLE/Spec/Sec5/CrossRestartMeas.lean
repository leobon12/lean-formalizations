/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartPack
import InteractingSLE.Spec.Sec5.Lemma57

/-!
# The counterflow restart carrier from the law of the canonical restart chart path

Packet PROVE-SEC5-G. SEC5-E's named carrier `Sec5.CounterflowSegmentRestartStatement` (`Lemma57.lean`) has four
layers (`planning/handoffs/PROVE-SEC5-E.md`, `planning/handoffs/PROVE-SEC5-F.md`): (i) the conditional law of the
field given the two explorations (the Figure 5.5 data), (ii) the coordinate change to the restart chart and its
packaging into `IsCounterflowChartContinuation`, (iii) Theorem 2.4's converse under the conditional law, (iv) the
measurable restart variable and kernel. This file removes layer (ii) from the carrier.

* **The canonical restart objects of one sample** (deterministic functions of the flow-line driver `w`, its lifetime
  `ζ`, the time `σ` and the counterflow `(w′, ζ′, γ′)`): the segment driver `segDrive` (the driver frozen after a
  time between `σ` and `ζ`), `x₁ = segStart = g_A(−1 − q)`, the **exit time** `restartExit` (the supremum of the
  times up to which the counterflow is alive in the restart chart, `CrossRestartPack.IsRestartAlive`), the **chart
  capacity lifetime** `restartLife` (the supremum of the chart capacity clock before the exit) and the chart path in
  capacity time `CrossRestartPack.restartChartPath`.
* `IsRestartIdent`: a path `γ` with lifetime `V` is the canonical restart chart path: `V` is at least the chart
  capacity lifetime, `γ` is the canonical chart path before it, and at a finite chart capacity lifetime `γ` sits on
  the target arcs `(−∞, −1] ∪ (Q, ∞)` (the chart image of `∂_L𝒮 ∪ η([0, σ])`).
* **`CounterflowRestartLawStatement`** (named input, layers (i), (iii) and (iv)): the carrier with its pathwise
  conjunct `IsCounterflowChartContinuation` replaced by `IsRestartIdent` for any version `w` of the flow-line
  driver.
* **`counterflowSegmentRestartStatement_of_restartLaw`**: with Aux. lemma 7 for `κ′ = 16/κ` (Lemma 4.5 under the
  conditional law), the named input gives the carrier. Lemma 4.5 under the kernel and the disintegration make the
  restart path almost surely immortal and off the target arcs, so the chart capacity lifetime is infinite, the chart
  capacity clock is exhausting, and `CrossRestartPack.IsRestartData.isCounterflowChartContinuation` gives the
  pathwise continuation (`isCounterflowChartContinuation_of_ident`, deterministic).

Aux. lemma 7 for `κ′` is the input SEC5-E's consumers (`ae_isFirstHitPoint_of_counterflowSegmentRestart`,
`lemma57_of_counterflowSegmentRestart`) already take.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther

/-! ### The canonical restart objects of one sample -/

/-- A time strictly between `σ` and `ζ` (when `σ < ζ`). -/
def midTime (σ : ℝ≥0) (ζ : ℝ≥0∞) : ℝ := if ζ = ⊤ then σ + 1 else (σ + ζ.toReal) / 2

theorem lt_toReal_of_coe_lt {σ : ℝ≥0} {ζ : ℝ≥0∞} (h : (σ : ℝ≥0∞) < ζ) (hζ : ζ ≠ ⊤) : (σ : ℝ) < ζ.toReal := by
  have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hζ).2 h
  simpa using this

theorem lt_midTime {σ : ℝ≥0} {ζ : ℝ≥0∞} (h : (σ : ℝ≥0∞) < ζ) : (σ : ℝ) < midTime σ ζ := by
  unfold midTime
  split_ifs with hζ
  · linarith
  · linarith [lt_toReal_of_coe_lt h hζ]

theorem ofReal_midTime_lt {σ : ℝ≥0} {ζ : ℝ≥0∞} (h : (σ : ℝ≥0∞) < ζ) : ENNReal.ofReal (midTime σ ζ) < ζ := by
  unfold midTime
  split_ifs with hζ
  · rw [hζ]; exact ENNReal.ofReal_lt_top
  · have h1 := lt_toReal_of_coe_lt h hζ
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hζ]
    linarith

/-- **The segment driver**: the flow-line driver read on `ℝ` and frozen after `midTime σ ζ` (continuous on `ℝ`
when `w` is continuous before `ζ > σ`; its hull at `σ` is the flow-line hull). -/
def segDrive (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (σ : ℝ≥0) : ℝ → ℝ := frozenDrive w (midTime σ ζ)

/-- **The image `x₁ = g_A(−1 − q)` of the counterflow start** (real part of the boundary value). -/
def segStart (q : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (σ : ℝ≥0) : ℝ := (bdryVal (segDrive w ζ σ) (-1 - q) σ).re

/-- **The exit time of the counterflow from the restart chart**: the supremum of the times `t` such that the
counterflow is alive in the restart chart at every `s ≤ t` and `s` is before its lifetime. -/
def restartExit (q : ℝ) (U : ℝ → ℝ) (σ : ℝ) (w' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : ∀ s : ℝ≥0, s ≤ t → IsRestartAlive q U σ w' γ' s ∧ (s : ℝ≥0∞) < ζ'), (t : ℝ≥0∞)

/-- **The chart capacity lifetime**: the supremum of the chart capacity clock before the exit time. -/
def restartLife (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (w' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < restartExit q U σ w' ζ' γ'), ENNReal.ofReal (restartClock q U σ x₁ w' t)

section Canonical

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ}

theorem alive_of_lt_restartExit {t : ℝ≥0} (ht : (t : ℝ≥0∞) < restartExit q U σ w' ζ' γ') :
    IsRestartAlive q U σ w' γ' t ∧ (t : ℝ≥0∞) < ζ' := by
  rw [restartExit, lt_iSup_iff] at ht
  obtain ⟨T, hT⟩ := ht
  rw [lt_iSup_iff] at hT
  obtain ⟨hT, htT⟩ := hT
  exact hT t (ENNReal.coe_le_coe.1 htT.le)

theorem restartExit_le : restartExit q U σ w' ζ' γ' ≤ ζ' :=
  iSup₂_le fun t ht => (ht t le_rfl).2.le

theorem restartExit_pos_of_restartLife_eq_top (h : restartLife q U σ x₁ w' ζ' γ' = ⊤) :
    0 < restartExit q U σ w' ζ' γ' := by
  rw [pos_iff_ne_zero]
  intro h0
  have : restartLife q U σ x₁ w' ζ' γ' = 0 := by
    refine le_antisymm (iSup₂_le fun t ht => ?_) bot_le
    rw [h0] at ht
    exact absurd ht (not_lt_zero)
  rw [this] at h
  exact ENNReal.zero_ne_top h

theorem exists_le_restartClock_of_restartLife_eq_top (h : restartLife q U σ x₁ w' ζ' γ' = ⊤) (u : ℝ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < restartExit q U σ w' ζ' γ' ∧ u ≤ restartClock q U σ x₁ w' t := by
  by_contra hcon
  push Not at hcon
  have : restartLife q U σ x₁ w' ζ' γ' ≤ ENNReal.ofReal u :=
    iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal (hcon t ht).le
  rw [h] at this
  exact ENNReal.ofReal_ne_top (top_le_iff.1 this)

end Canonical

/-- **`γ` (lifetime `V`) is the canonical restart chart path**: the chart capacity lifetime `Ue` is at most `V`,
`γ` is the canonical chart path in capacity time before `Ue`, and if `Ue` is finite then `γ(Ue)` lies on the
target arcs `(−∞, −1] ∪ (Q, ∞)`. -/
def IsRestartIdent (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (w' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) (Q : ℝ)
    (γ : ℝ≥0 → ℂ) (V : ℝ≥0∞) : Prop :=
  restartLife q U σ x₁ w' ζ' γ' ≤ V ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < restartLife q U σ x₁ w' ζ' γ' →
      γ u = restartChartPath q U σ x₁ w' γ' (restartExit q U σ w' ζ' γ') u) ∧
    (restartLife q U σ x₁ w' ζ' γ' < ⊤ →
      γ (restartLife q U σ x₁ w' ζ' γ').toNNReal ∈ ((↑) : ℝ → ℂ) '' (Iic (-1) ∪ Ioi Q))

/-! ### The pathwise continuation from the identification -/

/-- **The pathwise restart from the identification** (deterministic). Let `η` be a generating trace of `w` (`w`
continuous before `ζ`, `w 0 = 0`), `σ < ζ` with `η((0, σ]) ⊆ ℍ`, and let the counterflow `γ′` be a generating trace
of `w′` (continuous before `ζ′`, `w′ 0 = 0`). If `γ` (lifetime `V = ∞`) is the canonical restart chart path and
never visits `(−∞, −1] ∪ (Q, ∞)`, then the completed counterflow is `ψ ∘ γ` in a clock
(`IsCounterflowChartContinuation`). -/
theorem isCounterflowChartContinuation_of_ident {q : ℝ} (hq : 0 < q) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) (hηH : ∀ t : ℝ≥0, 0 < t → t ≤ σ → η t ∈ H)
    {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} (hγ' : IsGeneratingTrace w' ζ' γ')
    (hw'c : ContinuousOn w' {t | (t : ℝ≥0∞) < ζ'}) (hw'0 : w' 0 = 0) {Q : ℝ} {γ : ℝ≥0 → ℂ} {V : ℝ≥0∞}
    (hid : IsRestartIdent q (segDrive w ζ σ) σ (segStart q w ζ σ) w' ζ' γ' Q γ V) (hV : V = ⊤)
    (havoid : ∀ t, γ t ∉ ((↑) : ℝ → ℂ) '' (Iic (-1) ∪ Ioi Q)) :
    IsCounterflowChartContinuation ((fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ)) (η σ)
      (stripCounterflowPath q γ') Q γ V := by
  set U := segDrive w ζ σ with hUdef
  set x₁ := segStart q w ζ σ with hx₁def
  obtain ⟨-, hagree, hfin⟩ := hid
  have hUe : restartLife q U σ x₁ w' ζ' γ' = ⊤ := by
    by_contra hne
    exact havoid _ (hfin (lt_top_iff_ne_top.2 hne))
  have hTe := restartExit_pos_of_restartLife_eq_top hUe
  have hexh := exists_le_restartClock_of_restartLife_eq_top hUe
  have hσ₂ := lt_midTime hσ
  have hσ₂ζ := ofReal_midTime_lt hσ
  have hUc : Continuous U := continuous_frozenDrive_of_lt hwc hσ₂ζ
  have hU0 : U 0 = 0 := by
    rw [hUdef, segDrive, frozenDrive_zero ((NNReal.coe_nonneg σ).trans hσ₂.le), hw0]
  -- the start of the counterflow is off the closed segment hull
  have hal0 := (alive_of_lt_restartExit (t := 0) (q := q) (U := U) (σ := σ) (w' := w') (ζ' := ζ') (γ' := γ')
    (by simpa using hTe)).1
  have hcl : ((-1 - q : ℝ) : ℂ) ∉ closure (QuantumZipper.fwdHull U σ) := fun h =>
    Set.disjoint_left.1 hal0.far₂ h (mem_insert _ _)
  obtain ⟨r', hr', hr'd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hcl)
  have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r') (QuantumZipper.fwdHull U σ) :=
    Set.disjoint_left.2 fun z hz hzA => hr'd hz (subset_closure hzA)
  have him := (bdryVal_spec hUc hU0 (NNReal.coe_nonneg σ) hr' hball).1
  have hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) σ := by
    apply Complex.ext
    · simp [hx₁def, segStart, hUdef]
    · simp [him]
  have hd : IsRestartData q U σ x₁ w' ζ' γ' (restartExit q U σ w' ζ' γ') :=
    ⟨hq, hUc, hU0, NNReal.coe_nonneg σ, hx₁, hγ', hw'c, hw'0, restartExit_le, hTe,
      fun t ht => (alive_of_lt_restartExit ht).1⟩
  -- the segment and the tip
  have hK : QuantumZipper.fwdHull U σ = QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) σ :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg σ) hσ₂ fun r hr => frozenDrive_eq hr
  have himg : (fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ) = η '' Icc 0 σ := by
    rw [image_toNNReal_Icc η (NNReal.coe_nonneg σ), Real.toNNReal_coe]
  have hA : (fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ) ∩ H ⊆ QuantumZipper.fwdHull U σ := by
    rw [himg, hK]
    exact inter_H_subset_of_isFilling (hη.2.2 σ hσ)
  have hA₁ : ((-1 - q : ℝ) : ℂ) ∉ (fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ) := by
    rw [himg]
    rintro ⟨s, hs, hseq⟩
    rcases eq_or_lt_of_le (zero_le (a := s)) with h0 | hpos
    · rw [← h0, hη.1] at hseq
      have := congrArg Complex.re hseq
      simp at this
      linarith
    · have hH : η s ∈ H := hηH s hpos hs.2
      have hi : 0 < (η s).im := hH
      rw [hseq] at hi
      simp at hi
  have htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 (η σ)) := by
    have h1 := hη.tendsto_fwdMapInv_tip hwc hw0 hσ
    rwa [← fwdMapInv_eq_of_eqOn (W := U) (NNReal.coe_nonneg σ) hσ₂ fun r hr => frozenDrive_eq hr] at h1
  obtain ⟨hcont, -⟩ := hd.isCounterflowChartContinuation (Q := Q) hA hA₁ htip hexh
  have hγeq : γ = restartChartPath q U σ x₁ w' γ' (restartExit q U σ w' ζ' γ') :=
    funext fun u => hagree u (by rw [hUe]; exact ENNReal.coe_lt_top)
  rw [hγeq, hV]
  exact hcont

/-! ### The named input and the reduction -/

/-- **Named input: the law of the canonical restart chart path** (layers (i), (iii), (iv) of the counterflow
restart; specification p. 118, Lemma 4.7's proof, and p. 138, Lemma 5.7's proof). The statement of
`Sec5.CounterflowSegmentRestartStatement` with its pathwise conjunct `IsCounterflowChartContinuation` replaced by
the identification of the restart variable with the **canonical restart chart path** (`IsRestartIdent`, built
from any version `w` of the flow-line driver): a measurable restart variable `X` (layer (iv)), whose conditional law
given the chart datum has the Figure 5.5 data (layer (i)) and is the trace law of the flow line of the mapped field
(layer (iii)), and which almost surely is the canonical chart path up to its chart capacity lifetime, landing on the
target arcs if that lifetime is finite. The coordinate change and the chart continuation (layer (ii)) are proved
(`counterflowSegmentRestartStatement_of_restartLaw`). -/
def CounterflowRestartLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ α x₀ a b a' b' θ : ℝ, IsFig51Bounds κ a b a' b' →
    -(π / 2) ≤ θ → θ ≤ π / 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hhm : Measurable h),
      IsFig51Field κ α x₀ a b a' b' P h →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ' →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) →
      CondIndep (MeasurableSpace.comap h inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P →
    ∀ σ : ℝ≥0, ∀ w : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
        ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0) →
    ∃ (S : Type) (_ : MeasurableSpace S) (γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (M : Set Ω)
      (β : Ω → ℝ × BoundaryWord) (X : Ω → S) (K : Kernel (ℝ × BoundaryWord) S),
      (∀ t, Measurable fun s => γ s t) ∧ Measurable U ∧
      (∀ s, ContinuousOn (γ s) {u | (u : ℝ≥0∞) ≤ U s}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ d ∂(P.restrict M).map β,
        IsFig55RestartDatum κ α θ a b a' b' d ∧ IsFlowLineTraceLaw (16 / κ) d.2 (K d) γ U) ∧
      ∀ᵐ ω ∂P, (σ : ℝ≥0∞) < ζ ω → (∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H) →
        ω ∈ M ∧ IsRestartIdent (Real.exp (π * x₀)) (segDrive (fun t => w t ω) (ζ ω) σ) σ
          (segStart (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) σ) (fun t => W' t ω) (ζ' ω) (γ' ω)
          (β ω).1 (γ (X ω)) (U (X ω))

/-- The flow line of `IsStripFlowLineAt` has a driver that is almost surely continuous before its lifetime, starts
at `0` and is generated by the trace. -/
theorem exists_driver_of_isStripFlowLineAt {κ α θ : ℝ} {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsStripFlowLineAt κ α θ bL bU JL JU P h η ζ) :
    ∃ w : ℝ≥0 → Ω → ℝ, ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
      ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0 := by
  obtain ⟨_, 𝓕, W, VL, VR, B, _, hcpl, htr⟩ := hη
  refine ⟨W, ?_⟩
  filter_upwards [htr, hcpl.1.2.2.2.2] with ω hω hp
  refine ⟨by simpa only [Complex.ofReal_zero, sub_zero] using hω, hp.2.2.2.1, hp.1⟩

/-- The driver of a strip counterflow is almost surely continuous before its lifetime and starts at `0`. -/
theorem ae_continuousOn_of_isStripCounterflowDriver {κ α q : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsStripCounterflowDriver κ α q P h W' ζ') :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧ W' 0 ω = 0 := by
  obtain ⟨_, _, _, _, _, _, 𝓕, VL, VR, B, _, hcpl⟩ := hcf
  filter_upwards [hcpl.1.2.2.2.2] with ω hp
  exact ⟨hp.2.2.2.1, hp.1⟩

/-- **The counterflow restart carrier from the law of the canonical restart chart path**: Aux. lemma 7 for
`κ′ = 16/κ` and `CounterflowRestartLawStatement` give `Sec5.CounterflowSegmentRestartStatement`. Layer (ii) (the
restart chart, its inverse, the exit time, the capacity clocks and the packaging into
`IsCounterflowChartContinuation`) is proved here. -/
theorem counterflowSegmentRestartStatement_of_restartLaw
    (h7 : ∀ κ : ℝ, 0 < κ → κ < 4 → Aux7Statement.{0} (16 / κ))
    (hR : CounterflowRestartLawStatement.{u}) : CounterflowSegmentRestartStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨w, hw⟩ := exists_driver_of_isStripFlowLineAt hη
  obtain ⟨S, mS, γ, U, M, β, X, K, hγm, hUm, hγc, hM, hβ, hX, hK, hlaw, hdat, hpath⟩ :=
    hR κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w hw
  refine ⟨S, mS, γ, U, M, β, X, K, hγm, hUm, hγc, hM, hβ, hX, hK, hlaw, hdat, ?_⟩
  have hκ' : 0 < 16 / κ := by positivity
  -- Lemma 4.5 under the kernel, integrated back (the argument of `MarkovOther.ae_isFirstHitPoint_of_restart`)
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 < r → X ω ∈ restartEvent γ U r := by
    intro r
    set E : Set ((ℝ × BoundaryWord) × S) := {p | (r : ℝ) ≤ p.1.1} ∪ univ ×ˢ restartEvent γ U r
    have hE : MeasurableSet E :=
      (measurableSet_le measurable_const (measurable_fst.comp measurable_fst)).union
        (MeasurableSet.univ.prod (measurableSet_restartEvent hγm hUm hγc r))
    have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂(K d), (d, s) ∈ E := by
      filter_upwards [hdat] with d ⟨hd, hfl⟩
      have hd' := isRestartTargetDatum_of_isFig55RestartDatum hκ hκ4 hbd hθ₁ hθ₂ hd
      by_cases hdr : (r : ℝ) ≤ d.1
      · exact Eventually.of_forall fun s => Or.inl hdr
      · push Not at hdr
        filter_upwards [ae_restartEvent_of_isFlowLineTraceLaw hκ' (h7 κ hκ hκ4) hd' hfl] with s hs
        obtain ⟨hU, hav, him, htr⟩ := hs
        refine Or.inr ⟨mem_univ _, hU, fun t ht => hav t ?_, him, htr⟩
        obtain ⟨x, hx, hxt⟩ := ht
        refine ⟨x, ?_, hxt⟩
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (show d.1 ≤ x from hdr.le.trans hx)
    filter_upwards [ae_mem_of_compProd_eq_prod hM hβ hX hlaw hE hKE] with ω hω hωM hlt
    rcases hω hωM with h | ⟨-, h⟩
    · exact absurd h (not_le.2 hlt)
    · exact h
  rw [← ae_all_iff] at hr
  filter_upwards [hr, hw, htr', ae_continuousOn_of_isStripCounterflowDriver hcf, hpath]
    with ω hrω hwω htrω hcfω hpω hσζ hηH
  obtain ⟨hωM, hid⟩ := hpω hσζ hηH
  refine ⟨hωM, ?_⟩
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (β ω).1
  obtain ⟨hUX, -, -, -⟩ := hrω r₀ hωM hr₀
  have havoid : ∀ t, γ (X ω) t ∉ ((↑) : ℝ → ℂ) '' (Iic (-1) ∪ Ioi (β ω).1) := by
    intro t
    rintro ⟨x, hx, hxt⟩
    rcases hx with hx | hx
    · obtain ⟨-, hav, -⟩ := hrω r₀ hωM hr₀
      exact hav t ⟨x, Or.inl hx, hxt⟩
    · have hx' : (β ω).1 < x := hx
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hx'
      obtain ⟨-, hav, -⟩ := hrω r hωM hr1
      exact hav t ⟨x, Or.inr (show (r : ℝ) ≤ x from hr2.le), hxt⟩
  exact isCounterflowChartContinuation_of_ident (Real.exp_pos _) hwω.1 hwω.2.1 hwω.2.2 hσζ hηH htrω
    hcfω.1 hcfω.2 hid hUX havoid

end CrossRestart

end Sec5

end InteractingSLE
