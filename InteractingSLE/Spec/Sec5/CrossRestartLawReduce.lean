/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartLaw
import InteractingSLE.Spec.Sec5.CrossRestartLawPath
import InteractingSLE.Spec.Restart.ChartSpace

/-!
# The counterflow restart carrier from the law of an explicit restart variable

Packet PROVE-SEC5-H, layer (iv) of the counterflow restart. SEC5-G's named input
`CrossRestart.CounterflowRestartLawStatement` asks for a *measurable* restart variable identified with the canonical
chart path, whose conditional law is the flow-line trace law. Here the restart variable is **explicit**:

* `restartVar`: the code (`Restart.encPath`, Theorem 2.2's dyadic path codes) of the measurable-form chart path
  `lawPath` with the measurable-form chart capacity lifetime `lawLife` (`CrossRestartLawPath.lean`), built from the
  flow-line driver `w`, its lifetime `ζ`, the flow-line trace `η`, the time `σ` and the counterflow `(ζ′, γ′)`. Its
  values live in the standard Borel space `(PCode × PCode) × ℝ≥0∞`, decoded by `Restart.decPath`.

The carrier then splits into two named propositions with disjoint content:

* `CounterflowRestartKernelStatement` (**layers (i) and (iii)**, the law only): whenever the explicit restart
  variable is measurable, its conditional law given the chart datum (on an event containing the explored situations)
  has the Figure 5.5 data and is the flow-line trace law;
* `RestartVarMeasurableStatement` (**the measurability part of layer (iv)**): the explicit restart variable is
  measurable for some versions of the flow-line driver and of the two traces.

**`counterflowSegmentRestartStatement_of_kernel`**: Zhan's Part A inputs at `16/κ`, the law statement and the
measurability statement give SEC5-E's carrier `Sec5.CounterflowSegmentRestartStatement`. The identification of the
explicit variable with the counterflow in its restart chart is proved pathwise (`CrossRestartLawTopo.lean`,
`CrossRestartLawPath.lean`): no exit time, landing clause or identification is assumed any more.
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

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther Sec2.Assembly

/-- **The explicit restart variable** of one sample: the code of the measurable-form chart path in the restart chart
of `ℍ ∖ η([0, σ])` with its measurable-form chart capacity lifetime (segment driver `segDrive w ζ σ`, image
`segStart` of the counterflow start, chart `M_q` of the counterflow). -/
def restartVar (q : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (η : ℝ≥0 → ℂ) (σ : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) :
    (PCode × PCode) × ℝ≥0∞ :=
  encPath (lawPath q (segDrive w ζ σ) σ (segStart q w ζ σ) η σ ζ' γ')
    (lawLife q (segDrive w ζ σ) σ (segStart q w ζ σ) η σ ζ' γ')

theorem restartVar_snd (q : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (η : ℝ≥0 → ℂ) (σ : ℝ≥0) (ζ' : ℝ≥0∞)
    (γ' : ℝ≥0 → ℂ) :
    (restartVar q w ζ η σ ζ' γ').2 = lawLife q (segDrive w ζ σ) σ (segStart q w ζ σ) η σ ζ' γ' := rfl

/-- `lawExit = 0` forces `lawLife = 0`. -/
theorem lawExit_pos_of_lawLife_eq_top {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {η : ℝ≥0 → ℂ} {s : ℝ≥0} {ζ' : ℝ≥0∞}
    {γ' : ℝ≥0 → ℂ} (h : lawLife q U σ x₁ η s ζ' γ' = ⊤) : 0 < lawExit q η s ζ' γ' := by
  rw [pos_iff_ne_zero]
  intro h0
  have : lawLife q U σ x₁ η s ζ' γ' = 0 := by
    refine le_antisymm (iSup₂_le fun r hr => ?_) bot_le
    rw [h0] at hr
    exact absurd hr (not_lt_zero)
  rw [this] at h
  exact ENNReal.zero_ne_top h

/-- **The pathwise restart for the explicit restart variable**: if the flow line `η` (driver `w`, lifetime `ζ`) is in
`ℍ` on `(0, σ]` with `σ < ζ`, the counterflow `γ′` is a generating trace of a driver continuous before its lifetime,
and the lifetime coordinate of the explicit restart variable is infinite, then the completed counterflow continues the
decoded restart variable in the restart chart of `ℍ ∖ η([0, σ])` with tip `η(σ)`. -/
theorem isCounterflowChartContinuation_restartVar {q : ℝ} (hq : 0 < q) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) (hηH : ∀ t : ℝ≥0, 0 < t → t ≤ σ → η t ∈ H)
    {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} (hγ' : IsGeneratingTrace w' ζ' γ')
    (hw'c : ContinuousOn w' {t | (t : ℝ≥0∞) < ζ'}) (hw'0 : w' 0 = 0) {Q : ℝ}
    (hL : (restartVar q w ζ η σ ζ' γ').2 = ⊤) :
    IsCounterflowChartContinuation ((fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ)) (η σ)
      (stripCounterflowPath q γ') Q (decPath (restartVar q w ζ η σ ζ' γ')) (restartVar q w ζ η σ ζ' γ').2 := by
  set U := segDrive w ζ σ with hUdef
  set x₁ := segStart q w ζ σ with hx₁def
  have hLife : lawLife q U σ x₁ η σ ζ' γ' = ⊤ := hL
  have hσ₂ := lt_midTime hσ
  have hσ₂ζ := ofReal_midTime_lt hσ
  have hUc : Continuous U := continuous_frozenDrive_of_lt hwc hσ₂ζ
  have hU0 : U 0 = 0 := by
    rw [hUdef, segDrive, frozenDrive_zero ((NNReal.coe_nonneg σ).trans hσ₂.le), hw0]
  have hK : QuantumZipper.fwdHull U σ = QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) σ :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg σ) hσ₂ fun r hr => frozenDrive_eq hr
  have himg : (fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ) = η '' Icc 0 σ := by
    rw [image_toNNReal_Icc η (NNReal.coe_nonneg σ), Real.toNNReal_coe]
  have hηA : IsAttachedPath η σ :=
    ⟨hη.2.1.mono fun t ht => le_trans (ENNReal.coe_le_coe.2 ht.2) hσ.le, hη.1, hηH⟩
  have hK₁ : QuantumZipper.fwdHull U σ = fillH (η '' Icc 0 σ) := by
    rw [hK]
    exact fwdHull_eq_fillH_of_isFilling hηA.isCompact_image (hη.2.2 σ hσ)
  have htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 (η σ)) := by
    have h1 := hη.tendsto_fwdMapInv_tip hwc hw0 hσ
    rwa [← fwdMapInv_eq_of_eqOn (W := U) (NNReal.coe_nonneg σ) hσ₂ fun r hr => frozenDrive_eq hr] at h1
  have hpH : ((-1 - q : ℝ) : ℂ) ∉ H := fun h => by
    have : (0 : ℝ) < ((-1 - q : ℝ) : ℂ).im := h
    simp at this
  -- the start of the counterflow is off the closed segment hull
  have hcl : ((-1 - q : ℝ) : ℂ) ∉ closure (QuantumZipper.fwdHull U σ) := by
    rw [hK₁]
    intro hmem
    rcases closure_fillH_subset_insert hηA.isCompact_image
      (fun z hz him => hηA.eq_zero_of_im_nonpos hz him) hmem with h0 | h1
    · have := congrArg Complex.re h0
      simp only [ofReal_re] at this
      linarith
    · exact hpH h1.1
  obtain ⟨r', hr', hr'd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hcl)
  have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r') (QuantumZipper.fwdHull U σ) :=
    Set.disjoint_left.2 fun z hz hzA => hr'd hz (subset_closure hzA)
  have him := (bdryVal_spec hUc hU0 (NNReal.coe_nonneg σ) hr' hball).1
  have hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) σ := by
    apply Complex.ext
    · simp [hx₁def, segStart, hUdef]
    · simp [him]
  have hd := isRestartData_lawExit hq hUc hU0 hηA hK₁ htip hx₁ hγ' hw'c hw'0
    (lawExit_pos_of_lawLife_eq_top hLife)
  have hA : (fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ) ∩ H ⊆ QuantumZipper.fwdHull U σ := by
    rw [himg, hK]
    exact inter_H_subset_of_isFilling (hη.2.2 σ hσ)
  have hA₁ : ((-1 - q : ℝ) : ℂ) ∉ (fun s : ℝ => η s.toNNReal) '' Icc 0 (σ : ℝ) := by
    rw [himg]
    intro hmem
    rcases hηA.eq_zero_of_im_nonpos hmem (by simp) |> fun h => h with h0
    have := congrArg Complex.re h0
    simp only [ofReal_re] at this
    linarith
  obtain ⟨hcont, hc⟩ := isCounterflowChartContinuation_lawPath (Q := Q) hd hA hA₁ htip hLife
  have hdec : decPath (restartVar q w ζ η σ ζ' γ') = lawPath q U σ x₁ η σ ζ' γ' := by
    funext t
    exact decPath_encPath hc.continuousOn (by rw [hLife]; exact le_top)
  rw [hdec, hL]
  exact hcont

/-! ### The two named propositions and the reduction -/

/-- **Named input: the conditional law of the explicit restart variable** (layers (i) and (iii) of the counterflow
restart; specification p. 118, Lemma 4.7's proof, and p. 138, Lemma 5.7's proof: "the boundary data for the GFF
which describes the evolution of `ψ(η′)` is as in the right panel of Figure 5.5 … This allows us to use Theorem
2.4"). Setting and binders of `Sec5.CounterflowSegmentRestartStatement`. For every time `σ`, every version `w` of
the flow-line driver, every versions `η₀`, `γ₀` of the two traces and `ζ₀` of the counterflow lifetime for which the
explicit restart variable `restartVar q w ζ η₀ σ ζ₀ γ₀` (`q = e^{πx₀}`) is measurable, there are a measurable event
`M` (containing almost every sample where `σ < ζ` and `η((0, σ]) ⊆ ℍ`), a measurable chart datum `β` and a Markov
kernel `K` that is the conditional law of the restart variable given `β` on `M`, such that for almost every datum `d
= (Q, c)`: `d` has the Figure 5.5 data, and under `K d` the decoded chart path (`Restart.decPath`) with its lifetime
coordinate has the flow-line trace law for `κ′ = 16/κ` and the word `c`. Only the law is asked: measurability is
`RestartVarMeasurableStatement`, and the identification with the counterflow is proved
(`isCounterflowChartContinuation_restartVar`). -/
def CounterflowRestartKernelStatement : Prop :=
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
    ∀ (σ : ℝ≥0) (w : ℝ≥0 → Ω → ℝ) (η₀ γ₀ : Ω → ℝ≥0 → ℂ) (ζ₀ : Ω → ℝ≥0∞),
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
        ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0 ∧ η₀ ω = η ω ∧ γ₀ ω = γ' ω ∧
        ζ₀ ω = ζ' ω) →
      Measurable (fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω)) →
    ∃ (M : Set Ω) (β : Ω → ℝ × BoundaryWord) (K : Kernel (ℝ × BoundaryWord) ((PCode × PCode) × ℝ≥0∞)),
      MeasurableSet M ∧ Measurable β ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω,
          restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω))) =
        (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ d ∂(P.restrict M).map β, IsFig55RestartDatum κ α θ a b a' b' d ∧
        IsFlowLineTraceLaw (16 / κ) d.2 (K d) decPath (fun s => s.2)) ∧
      ∀ᵐ ω ∂P, (σ : ℝ≥0∞) < ζ ω → (∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H) → ω ∈ M

/-- **The measurability of the explicit restart variable** (the measurable-construction part of layer (iv)). Setting
and binders of `Sec5.CounterflowSegmentRestartStatement`: for every time `σ` there are versions `w` of the flow-line
driver, `η₀`, `γ₀` of the two traces and `ζ₀` of the counterflow lifetime for which the explicit restart variable
is measurable. -/
def RestartVarMeasurableStatement : Prop :=
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
    ∀ σ : ℝ≥0, ∃ (w : ℝ≥0 → Ω → ℝ) (η₀ γ₀ : Ω → ℝ≥0 → ℂ) (ζ₀ : Ω → ℝ≥0∞),
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
        ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0 ∧ η₀ ω = η ω ∧ γ₀ ω = γ' ω ∧
        ζ₀ ω = ζ' ω) ∧
      Measurable (fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω))

/-- **SEC5-E's counterflow restart carrier from the law of the explicit restart variable**: Zhan's Part A inputs at
`16/κ` (Aux. lemma 7 for `κ′`), `CounterflowRestartKernelStatement` (the law) and `RestartVarMeasurableStatement`
(measurability) give `Sec5.CounterflowSegmentRestartStatement`. The restart variable is the explicit `restartVar`;
its identification with the counterflow in the restart chart is pathwise
(`isCounterflowChartContinuation_restartVar`), and Lemma 4.5 under the kernel makes its lifetime coordinate almost
surely infinite. -/
theorem counterflowSegmentRestartStatement_of_kernel (hA : PartAInputsSixteenDiv)
    (hK : CounterflowRestartKernelStatement.{u}) (hV : RestartVarMeasurableStatement.{u}) :
    CounterflowSegmentRestartStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨w, η₀, γ₀, ζ₀, hver, hXm⟩ :=
    hV κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨M, β, K, hM, hβ, hKm, hlaw, hdat, hMev⟩ :=
    hK κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w η₀ γ₀ ζ₀ hver hXm
  set X := fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω) with hXdef
  have hγm : ∀ t, Measurable fun s : (PCode × PCode) × ℝ≥0∞ => decPath s t := measurable_decPath
  have hUm : Measurable fun s : (PCode × PCode) × ℝ≥0∞ => s.2 := measurable_snd
  have hγc : ∀ s : (PCode × PCode) × ℝ≥0∞, ContinuousOn (decPath s) {u | (u : ℝ≥0∞) ≤ s.2} :=
    continuousOn_decPath
  refine ⟨(PCode × PCode) × ℝ≥0∞, inferInstance, decPath, fun s => s.2, M, β, X, K, hγm, hUm, hγc, hM, hβ,
    hXm, hKm, hlaw, hdat, ?_⟩
  have hκ' : 0 < 16 / κ := by positivity
  have h7 : Aux7Statement.{0} (16 / κ) := aux7Statement_sixteen_div_of_partA hA hκ hκ4
  -- Lemma 4.5 under the kernel, integrated back (as in `counterflowSegmentRestartStatement_of_restartLaw`)
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 < r → X ω ∈ restartEvent decPath (fun s => s.2) r := by
    intro r
    set E : Set ((ℝ × BoundaryWord) × ((PCode × PCode) × ℝ≥0∞)) :=
      {p | (r : ℝ) ≤ p.1.1} ∪ univ ×ˢ restartEvent decPath (fun s => s.2) r
    have hE : MeasurableSet E :=
      (measurableSet_le measurable_const (measurable_fst.comp measurable_fst)).union
        (MeasurableSet.univ.prod (measurableSet_restartEvent hγm hUm hγc r))
    have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂(K d), (d, s) ∈ E := by
      filter_upwards [hdat] with d ⟨hd, hfl⟩
      have hd' := isRestartTargetDatum_of_isFig55RestartDatum hκ hκ4 hbd hθ₁ hθ₂ hd
      by_cases hdr : (r : ℝ) ≤ d.1
      · exact Eventually.of_forall fun s => Or.inl hdr
      · push Not at hdr
        filter_upwards [ae_restartEvent_of_isFlowLineTraceLaw hκ' h7 hd' hfl] with s hs
        obtain ⟨hU, hav, him, htr⟩ := hs
        refine Or.inr ⟨mem_univ _, hU, fun t ht => hav t ?_, him, htr⟩
        obtain ⟨x, hx, hxt⟩ := ht
        refine ⟨x, ?_, hxt⟩
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (show d.1 ≤ x from hdr.le.trans hx)
    filter_upwards [ae_mem_of_compProd_eq_prod hM hβ hXm hlaw hE hKE] with ω hω hωM hlt
    rcases hω hωM with h | ⟨-, h⟩
    · exact absurd h (not_le.2 hlt)
    · exact h
  rw [← ae_all_iff] at hr
  filter_upwards [hr, hver, htr', ae_continuousOn_of_isStripCounterflowDriver hcf, hMev]
    with ω hrω ⟨hwη, hwc, hw0, hη₀, hγ₀, hζ₀⟩ htrω hcfω hMω hσζ hηH
  have hωM := hMω hσζ hηH
  refine ⟨hωM, ?_⟩
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (β ω).1
  obtain ⟨hUX, -, -, -⟩ := hrω r₀ hωM hr₀
  have hXω : X ω = restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η ω) σ (ζ' ω) (γ' ω) := by
    rw [hXdef]
    simp only [hη₀, hγ₀, hζ₀]
  rw [hXω] at hUX ⊢
  exact isCounterflowChartContinuation_restartVar (Real.exp_pos _) hwη hwc hw0 hσζ hηH htrω hcfω.1 hcfω.2 hUX

end CrossRestart

end Sec5

end InteractingSLE
