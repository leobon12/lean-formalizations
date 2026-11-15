/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119HeightsFlow
import InteractingSLE.Spec.Sec7.StripDetPath
import InteractingSLE.Spec.Sec7.ContinuityProbBase
import InteractingSLE.Spec.Supplement.GW1
import InteractingSLE.Spec.Supplement.LPProbExtract
import InteractingSLE.Spec.Wire.Sec4

/-!
# The first piece of a two-angle strip wall is a flow line of the field; its side heights

Packet PROVE-STRIPSYS27, first item. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440,
p. 410: "Each initial constant-angle path has only original-boundary cumulative values, all nonnegative by the chosen
heights. It therefore has the earlier noncolliding continuous simple proper law and is field determined by (4.4)"),
used by Aux. lemma 119's proof (p. 386: "the own height `λ − θ_Lχ` on a right side of the left path, and
`−λ − θ_Rχ` on a left side of the right path") for the walls before their angle change.

For a staged history `E` of the two-angle program `η^{t₀,∞}_{θ₀,θ}` (`StripSys.twoAngleSpec θ₀ t₀ θ`) of a GFF `h`
with data `b`:

* **`isFlowLineDriver_stage_zero`** (the bridge): the first piece is an angle-`θ₀` flow-line driver of `h` itself with
  the data `b` — the conditional law at stage `0` is the law (`GW1.pastSigma_zero_eq_bot`,
  `GW1.condExpKernel_bot_apply`), the stage-`0` chart is the identity chart, so the chart field is `h`
  (`IsChartTransport.unique`), and the stage data agree with `b` off a finite set
  (`StagedLaw.isFlowLineDriver_word`, `StagedLaw.isFlowLineDriver_congr_of_eqOn`);
* `ae_trace_stage_zero`, `trace0`, **`isFlowLine_trace0`**: if `b` has the (4.4) heights at `θ₀`, the first piece has
  almost surely infinite lifetime and a simple transient generating trace (Remark 2.3 and Proposition 4.12,
  `Sec4.ae_simple_trace_of_cond44`, `Wire.prop412`), and its chosen trace `trace0 E` is a frozen `IsFlowLine`;
* `ae_eqOn_trace0`: every generating trace of the concatenated wall driver agrees with `trace0 E` on `[0, t₀]`
  (uniqueness of the generating trace, `IsGeneratingTrace.eq_of_le`);
* **`ae_sideHeights_first`**: for a version `γ` of the wall with Lemma 6.2's inputs, at every rational stop `q ≤ t₀`,
  almost surely every harmonic representative of the mean of `γ([0, q]) ∩ ℍ` has the side heights of angle `θ₀` at
  every wall point before `q` (`Aux119Heights.ae_hasSideHeights_of_isFlowLine` for the flow line `trace0 E`, version
  `γ`, then `Aux119Heights.hasSideHeights_congr`) — the input `hst0` of `Aux119Heights.ae_sideHeights_rat_of_stages`.

No Theorem 1.2/1.3 (R43, R48). Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)

/-! ### A flow-line driver with a trace is a flow line -/

/-- **A flow-line driver from `0` with an almost sure generating trace is a frozen flow line.** -/
theorem isFlowLine_of_isFlowLineDriver {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {η : Ω → ℝ≥0 → ℂ} (hd : IsFlowLineDriver κ b jumps θ P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) :
    IsFlowLine κ b jumps 0 θ P h η ζ := by
  obtain ⟨h', 𝓕, VL, VR, B, ht, hC⟩ := hd
  refine ⟨h', 𝓕, W, VL, VR, B, ht, hC, ?_⟩
  filter_upwards [htr] with ω hω
  simpa only [Complex.ofReal_zero, sub_zero] using hω

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-! ### The bridge: stage `0` is a flow line of the field itself -/

omit mΩ [StandardBorelSpace Ω] in
/-- The first instruction launches the angle-`θ₀` piece from the root `0` in the identity chart. -/
theorem launches_run_one_twoAngleSpec (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D (0 + 1)).2.2.2.1 0 =
      some (Exist.shiftChart 0, θ₀) := by
  change (ExplState.launch (ExplState.init 0) 0 (D 0) θ₀ (t₀ : ℝ≥0∞)).2.2.2.1 0 = _
  rw [Exist.Staged.launches_launch, Function.update_self]
  rfl

/-- **Stage `0` of a two-angle staged history is a flow line of `h` with the data `b`** (the bridge of
`planning/handoffs/PROVE-STRIPSYS25.md` §5 item 1): the first driver is the angle-`θ₀` flow-line driver of the field
`h` itself, for the original data `b`. -/
theorem isFlowLineDriver_stage_zero (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) :
    IsFlowLineDriver κ b jumps θ₀ P h (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) := by
  obtain ⟨ω₀, hω₀⟩ := (hE.2.2.2 0).exists
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hω₀ _ _ (launches_run_one_twoAngleSpec _)
  rw [Theorem14.GW1.pastSigma_zero_eq_bot, Theorem14.GW1.condExpKernel_bot_apply] at hfl
  have hh' : h' = h := funext fun ω => by
    have h2 := Exist.StagedLaw.isChartTransport_shiftChart 0 (chiC κ) (h ω)
    rw [Prop74B.flowField_zero_zero] at h2
    exact IsChartTransport.unique (Exist.isConformal_shiftChart 0) (hT' ω) h2
  rw [hh'] at hfl
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have h1 := Exist.StagedLaw.isFlowLineDriver_word hκ hh₀ hb' hfl
  exact (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
    (fun y hy => hc₀ y hy)).1 h1

/-! ### The first piece's trace -/

/-- **The first piece has a simple transient trace** (Remark 2.3 and Proposition 4.12 for its flow-line word, which
satisfies (4.4) by the heights of `b` at `θ₀`): almost surely its lifetime is infinite and it has an injective
generating trace on `[0, ∞)`, in `ℍ` at positive times and tending to `∞`. -/
theorem ae_trace_stage_zero (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η ∧ Injective η ∧
      (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := isFlowLineDriver_stage_zero hκ hb hh hE
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps 0
  have h44 := StripDet.cond44_flowLine_of_heights hκ hb θ₀ hL0 hR0
  filter_upwards [Sec4.ae_simple_trace_of_cond44 hκ hκ4 hF h44 hC.1, Wire.prop412 hκ hκ4 hF h44 hC.1]
    with ω h1 h2
  obtain ⟨hζ, -, η, hη, hinj, hH, -⟩ := h1
  exact ⟨hζ, η, hη, hinj, hH, h2.2.2 η hη⟩

omit mΩ [StandardBorelSpace Ω] in
open scoped Classical in
/-- **The trace of the first piece**: a chosen simple transient generating trace of the first driver on `[0, ∞)` when
one exists (almost surely, `ae_trace0`), `0` otherwise. -/
def trace0 (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℂ :=
  if hη : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      Tendsto (fun t => ‖η t‖) atTop atTop then hη.choose else 0

omit mΩ [StandardBorelSpace Ω] in
theorem trace0_spec {ω : Ω} (hη : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η ∧ Injective η ∧
      (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop) :
    IsGeneratingTrace (E 0 ω).1 ⊤ (trace0 E ω) ∧ Injective (trace0 E ω) ∧ (∀ t, 0 < t → trace0 E ω t ∈ H) ∧
      Tendsto (fun t => ‖trace0 E ω t‖) atTop atTop := by
  classical
  have e : trace0 E ω = hη.choose := by
    unfold trace0
    simp only [hη, ↓reduceDIte]
  rw [e]
  exact hη.choose_spec

/-- Almost surely the first piece lives forever and `trace0 E` is its simple transient generating trace. -/
theorem ae_trace0 (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ IsGeneratingTrace (E 0 ω).1 ⊤ (trace0 E ω) ∧ Injective (trace0 E ω) ∧
      (∀ t, 0 < t → trace0 E ω t ∈ H) ∧ Tendsto (fun t => ‖trace0 E ω t‖) atTop atTop := by
  filter_upwards [ae_trace_stage_zero hκ hκ4 hb hh hE hL0 hR0] with ω hω
  exact ⟨hω.1, trace0_spec hω.2⟩

/-- **The first piece's trace is a frozen flow line of `h`** (angle `θ₀`, from `0`, data `b`). -/
theorem isFlowLine_trace0 (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    IsFlowLine κ b jumps 0 θ₀ P h (trace0 E) (fun ω => (E 0 ω).2) := by
  refine isFlowLine_of_isFlowLineDriver (isFlowLineDriver_stage_zero hκ hb hh hE) ?_
  filter_upwards [ae_trace0 hκ hκ4 hb hh hE hL0 hR0] with ω hω
  rw [hω.1]
  exact hω.2.1

/-! ### The wall agrees with the first piece before the change time -/

/-- **A generating trace of the concatenated wall driver is the first piece's trace on `[0, t₀]`** (uniqueness of
generating traces: both generate the chain driven by the first driver on `[0, t₀]`). -/
theorem ae_eqOn_trace0 (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) {γ : Ω → ℝ≥0 → ℂ}
    (htrγ : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ t₀ → γ ω t = trace0 E ω t := by
  filter_upwards [ae_trace0 hκ hκ4 hb hh hE hL0 hR0, htrγ] with ω h0 hγ t ht
  have hγ' : IsGeneratingTrace (E 0 ω).1 t₀ (γ ω) :=
    IsGeneratingTrace.of_eqOn_lt hγ fun s hs => (catPath_of_le (ENNReal.coe_lt_coe.1 hs).le).symm
  have h0' : IsGeneratingTrace (E 0 ω).1 t₀ (trace0 E ω) := LP.isGeneratingTrace_mono h0.2.1 le_top
  have hcont : ContinuousOn (E 0 ω).1 {s : ℝ≥0 | (s : ℝ≥0∞) < t₀} :=
    (hreg 0 ω).1.mono fun s _ => show (s : ℝ≥0∞) < (E 0 ω).2 by rw [h0.1]; exact ENNReal.coe_lt_top
  exact IsGeneratingTrace.eq_of_le hγ' h0' hcont (hreg 0 ω).2.1 (ENNReal.coe_le_coe.2 ht)

/-! ### The side heights of the first piece -/

/-- **The first-piece side heights of a two-angle wall** (the input `hst0` of
`Aux119Heights.ae_sideHeights_rat_of_stages`): for a version `γ` of the wall (a generating trace of the concatenated
driver on `[0, ∞)`) with Lemma 6.2's inputs for the centred field, and versions `g q` of the means of its stopped
ranges, at every rational stop `q ≤ t₀`, almost surely every harmonic representative `v` of `g q` has the side heights
`±λ − θ₀χ` at every wall point `γ(s) ∈ ℍ`, `s < q`, read with the wall driver. -/
theorem ae_sideHeights_first (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω))
    (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal γ (WholeField.centredField h u₀) P)
    (htrγ : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℝ≥0, LocalSets.IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (g q)) :
    ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t₀ → ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, s < q → γ ω s ∈ H →
        StripGeom.HasSideHeights κ θ₀ (γ ω) 0 (catPath (E 0 ω).1 t₀ (E 1 ω).1) q (γ ω s) v u₀ := by
  intro q hq
  have hfl := isFlowLine_trace0 hκ hκ4 hb hh hE hL0 hR0
  have h0 := ae_trace0 hκ hκ4 hb hh hE hL0 hR0
  have htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (E 0 ω).1 t) ((E 0 ω).2)
      (fun t => trace0 E ω t - ((0 : ℝ) : ℂ)) := by
    filter_upwards [h0] with ω hω
    simp only [Complex.ofReal_zero, sub_zero]
    rw [hω.1]
    exact hω.2.1
  have hagree := ae_eqOn_trace0 hκ hκ4 hb hh hE hreg hL0 hR0 htrγ
  have hηce : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (q : ℝ≥0) → (t : ℝ≥0∞) < (E 0 ω).2 → γ ω t = trace0 E ω t :=
    hagree.mono fun ω hω t ht _ => hω t (ht.trans hq)
  have key := Aux119Heights.ae_hasSideHeights_of_isFlowLine hκ hb hh hfl htr hu₀ hγc hγ0 hγm hdet hloc
    (q : ℝ≥0) hηce (hg q)
  filter_upwards [key, hagree, h0] with ω hk ha hω v hv hrep s hs hsH
  have hζ : ((q : ℝ≥0) : ℝ≥0∞) < (E 0 ω).2 := by rw [hω.1]; exact ENNReal.coe_lt_top
  have hst : s ≤ t₀ := hs.le.trans hq
  have h1 := hk hζ v hv hrep s hs (by rw [← ha s hst]; exact hsH)
  rw [← ha s hst] at h1
  exact Aux119Heights.hasSideHeights_congr (fun t ht => (ha t (ht.trans hq)).symm)
    (fun t ht => (catPath_of_le (ht.trans hq)).symm) h1

end Stage

end StripWall

end Sec7

end InteractingSLE
