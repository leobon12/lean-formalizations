/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StagedEntranceStripPast
import InteractingSLE.Spec.Sec4.Prop412
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Entrance-history locality of the strip system's angle-varying path

Packet PROVE-STAGEDLOC2. The strip system's `hloc` (PROVE-STRIPSYS21 §5.1 (ii); spec p. 410): for a two-angle staged
history `E` of `StripSys.twoAngleSpec θ₀ q₀ θ` (angle `θ₀` until the rational own time `q₀ > 0`, then `θ`), with the
(4.4) heights of the data at both angles and `θ₀ ≤ θ ≤ θ₀ + π`, every continuous version `αc` of the joined trace is
entrance-history local for the centred field (Lemma 6.2's locality input).

This is `StagedEntrance.isEntranceHistoryLocal_of_restart_isFlowLine` with its hypotheses discharged:

* `hloc₀` (**`isEntranceHistoryLocal_frozenPath_first`**): the first piece is the angle-`θ₀` flow line of `h` itself
  (**`isFlowLineDriver_first`**, from the staged clause at the trivial past), with a trace by Remark 2.3 for its (4.4)
  word; Aux. lemma 56 at first entrance times;
* `hdet₀`: PROVE-STRIPSYS21's `hdet_of_trace`, frozen;
* `hfr`: the record chart's domain is a component of `ℍ ∖ αc([0, q₀])` (`Strip.frontier_recChart`);
* `hchart`, `hflow`: the staged clause at the continuation (**`ae_isFlowLineDriver_second`**: under the staged
  conditional law the continuation is a flow-line driver of the field read in the record chart), moved to Lemma 6.2's
  past by `Strip.ae_condExpKernel_pastSigma_eq`; field determination of the chart trace from PROVE-STRIPSYS21's
  `ae_drv_one` (R48-safe).

The Loewner concatenation (PROVE-LOEWNERCAT, item R1 of `planning/handoffs/PROVE-STAGEDLOC.md` §5) enters only as
hypotheses on the given versions: `αc` (continuous, `αc 0 = 0`, measurable, a.s. a generating trace of the
concatenated driver) and the chart trace `β` of the continuation (continuous, `β 0 = 0`, measurable, a.s. a generating
trace of `(E 1).1`, in `ℍ` for `s > 0`, and `αc (q₀ + s) = inv (β s)` for the record chart).

## Main results

* **`isEntranceHistoryLocal_strip`**: `Sec6.IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P`.

No Theorem 1.2/1.3 input (R43, R48): the only named input is `AdmCode.Theorem12ParamCond44Statement` (from the §4.2
reference).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

namespace Strip

open Sec6 Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb Sec7.StripDet Sec7.AdmCode

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {q₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-! ### The first piece -/

/-- **The first piece is the angle-`θ₀` flow-line driver of the field itself**, for the data `b` (the staged clause at
the trivial past, launched from the root `0` in the identity chart). -/
theorem isFlowLineDriver_first (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E) :
    IsFlowLineDriver κ b jumps θ₀ P h (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) := by
  obtain ⟨ω₀, hω₀⟩ := (hE.2.2.2 0).exists
  have hl : (ExplState.run κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) (fun j => E j ω₀) (0 + 1)).2.2.2.1 0 =
      some (Exist.shiftChart 0, θ₀) := by
    change (ExplState.launch (ExplState.init 0) 0 (E 0 ω₀) θ₀ (q₀ : ℝ≥0∞)).2.2.2.1 0 = _
    rw [launches_launch, Function.update_self]
    rfl
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hω₀ _ _ hl
  rw [Theorem14.GW1.pastSigma_zero_eq_bot, Theorem14.GW1.condExpKernel_bot_apply] at hfl
  have hh' : h' = h := funext fun ω => by
    have h2 := isChartTransport_shiftChart 0 (chiC κ) (h ω)
    rw [Sec7.Prop74B.flowField_zero_zero] at h2
    exact IsChartTransport.unique (Exist.isConformal_shiftChart 0) (hT' ω) h2
  rw [hh'] at hfl
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  exact (isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
    (fun y hy => hc₀ y hy)).1 (isFlowLineDriver_word hκ hh₀ hb' hfl)

/-- The first piece almost surely lives forever and has a generating trace on `[0, ∞)` (Remark 2.3 for its (4.4)
word). -/
theorem ae_exists_trace_first (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := isFlowLineDriver_first hκ hb hh hE
  filter_upwards [Sec4.ae_simple_trace_of_cond44 hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b jumps 0)
    (cond44_flowLine_of_heights hκ hb θ₀ hL0 hR0) hC.1] with ω hω
  obtain ⟨hζ, -, η, hη, -⟩ := hω
  exact ⟨hζ, η, hη⟩

omit mΩ [StandardBorelSpace Ω] in
open scoped Classical in
/-- A generating trace of the first piece on `[0, ∞)`, chosen where one exists (`0` elsewhere). -/
def firstTrace (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℂ :=
  if hη : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η then hη.choose else 0

omit mΩ [StandardBorelSpace Ω] in
theorem firstTrace_spec {ω : Ω} (hη : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η) :
    IsGeneratingTrace (E 0 ω).1 ⊤ (firstTrace E ω) := by
  classical
  have e : firstTrace E ω = hη.choose := by
    unfold firstTrace
    simp only [hη, ↓reduceDIte]
  rw [e]
  exact hη.choose_spec

/-- **`hloc₀`: the joined trace frozen at `q₀` is entrance-history local** — up to `q₀` it is the first piece, a flow
line of `h` with infinite lifetime (Aux. lemma 56 at first entrance times). -/
theorem isEntranceHistoryLocal_frozenPath_first (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω))
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 q₀ (E 1 ω).1) ⊤ (αc ω)) :
    IsEntranceHistoryLocal (fun ω => frozenPath (αc ω) q₀) (WholeField.centredField h u₀) P := by
  have h0 := ae_exists_trace_first hκ hκ4 hb hh hE hL0 hR0
  obtain ⟨h', 𝓕, VL, VR, B, ht, hC⟩ := isFlowLineDriver_first hκ hb hh hE
  have hfl : IsFlowLine κ b jumps 0 θ₀ P h (firstTrace E) (fun ω => (E 0 ω).2) := by
    refine ⟨h', 𝓕, fun t ω => (E 0 ω).1 t, VL, VR, B, ht, hC, ?_⟩
    filter_upwards [h0] with ω hω
    simp only [Complex.ofReal_zero, sub_zero]
    rw [hω.1]
    exact firstTrace_spec hω.2
  refine isEntranceHistoryLocal_frozenPath_of_isFlowLine hκ hκ4 hb hh hfl (h0.mono fun ω hω => hω.1) hu₀ hαc hαm
    q₀ ?_
  filter_upwards [h0, htr] with ω hω hα t ht
  exact IsGeneratingTrace.eq_of_le (isGeneratingTrace_first hα)
    (LP.isGeneratingTrace_mono (firstTrace_spec hω.2) le_top)
    ((continuous_of_regular_top (hreg 0 ω) hω.1).continuousOn) (hreg 0 ω).2.1 (ENNReal.coe_le_coe.2 ht)

/-! ### The continuation under the staged conditional law -/

/-- **The continuation is a flow-line driver of the field read in the record chart**, under the regular conditional
law given the first record (the staged clause at the continuation; its launch chart is the record chart and its angle
is `θ`). -/
theorem ae_isFlowLineDriver_second (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤) :
    ∀ᵐ ω₀ ∂P, ∃ p : (ℝ → ℝ) × Finset ℝ, IsPiecewiseConstantBoundaryData p.1 p.2 ∧
      IsFlowLineDriver κ p.1 p.2 θ
        (condExpKernel P (_root_.InteractingSLE.pastSigma κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E 1) ω₀)
        (fun ω => recField κ (recOf (q₀ : ℝ≥0∞) (E 0 ω₀)) (h ω)) (fun t ω => (E 1 ω).1 t)
        (fun ω => (E 1 ω).2) := by
  filter_upwards [hE.2.2.2 1, hζ] with ω₀ hcl hω₀
  have h0 : (q₀ : ℝ≥0∞) < (E 0 ω₀).2 := by rw [hω₀]; exact ENNReal.coe_lt_top
  obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1
    (launch_one_of_lt (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (D := fun j => E j ω₀) h0)
  have hθ' : θ' = θ := angle_of_launch _ _ hl
  have hc : c = recChart (recOf (q₀ : ℝ≥0∞) (E 0 ω₀)) := by
    rw [(eq_launch_of_launches _ _ hl).2.2, chart_one_eq (hreg 0 ω₀) h0]
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hcl c θ' hl
  refine ⟨(b', J'), hb', ?_⟩
  have hh' : h' = fun ω => recField κ (recOf (q₀ : ℝ≥0∞) (E 0 ω₀)) (h ω) := funext fun ω => by
    have hT := hT' ω
    rw [hc] at hT
    exact IsChartTransport.unique (isConformal_recChart _) hT (isChartTransport_recField κ _ _)
  rw [hh', hθ'] at hfl
  exact hfl

/-! ### The strip system's locality -/

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] mΩ in
/-- Every point of `ℍ` is in the domain of the identity chart. -/
theorem mem_dom_id {z : ℂ} (hz : z ∈ H) : z ∈ Chart.id.dom := by
  rw [← SetLike.mem_coe, Chart.isConformal_id.coe_dom]
  exact ⟨z, hz, rfl⟩

/-- **Entrance-history locality of the strip system's angle-varying path** (`hloc` of PROVE-STRIPSYS21 §5.1 (ii),
R48-safe). Let `E` be a two-angle staged history (angle `θ₀` until the rational own time `q > 0`, then `θ`) of a GFF
`h` with piecewise constant data `b` having the (4.4) heights at `θ₀` and at `θ`, `θ₀ ≤ θ ≤ θ₀ + π`, and let `u₀` be
the bounded harmonic extension of `b`. Let `αc` be a version of the joined trace (continuous, `αc 0 = 0`, measurable at
fixed times, almost surely a generating trace of the concatenated driver on `[0, ∞)`) and `β` a version of the
continuation's chart trace (continuous, `β 0 = 0`, measurable, almost surely a generating trace of `(E 1).1` on
`[0, ∞)`, in `ℍ` at positive times, with `αc (q + s) = inv (β s)` for the record chart of the first piece): the Loewner
concatenation of PROVE-LOEWNERCAT. Then `αc` is entrance-history local for the centred field `h − u₀`. -/
theorem isEntranceHistoryLocal_strip (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {q : ℚ≥0} (hq : 0 < q)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 (q : ℝ≥0) (E 1 ω).1) ⊤ (αc ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (β ω))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → β ω s ∈ H ∧
      αc ω ((q : ℝ≥0) + s) = (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).2.1 (β ω s)) :
    IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P := by
  classical
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hd0 := ae_drv_zero h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0
  have hd1 := ae_drv_one h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0 hL hR hθ hθπ
  have hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ := by
    filter_upwards [hd0, hd1] with ω h0 h1
    exact ⟨h0.1, h1.1⟩
  have hq' : (0 : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hq
  have hpast : StagedEntrance.pastSigma αc (q : ℝ≥0) ≤ mΩ := pastSigma_le hαm
  have hK := ae_condExpKernel_pastSigma_eq hE hreg hq' hαm hζ htr
  -- the record chart of the first piece, replaced by the identity chart off the good event
  let G : Ω → Prop := fun ω => ∀ z ∈ H,
    z ∈ closure ((recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).dom : Set ℂ) →
      z ∉ (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).dom → z ∈ αc ω '' Icc 0 (q : ℝ≥0)
  have hG : ∀ᵐ ω ∂P, G ω := by
    filter_upwards [hζ, htr] with ω hω hα
    exact frontier_recChart (hreg 0 ω) (hreg 1 ω) hω.1 hω.2 hα
  let c : Ω → Chart := fun ω => if G ω then recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)) else Chart.id
  have hcG : ∀ ω, G ω → c ω = recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)) := fun ω hω => by
    simp only [c, hω, ↓reduceIte]
  have hcN : ∀ ω, ¬ G ω → c ω = Chart.id := fun ω hω => by
    simp only [c, hω, ↓reduceIte]
  have hc : ∀ ω, (c ω).IsConformal := fun ω => by
    by_cases hω : G ω
    · rw [hcG ω hω]; exact isConformal_recChart _
    · rw [hcN ω hω]; exact Chart.isConformal_id
  have hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ αc ω '' Icc 0 (q : ℝ≥0) := by
    intro ω z hz hcl hnd
    by_cases hω : G ω
    · rw [hcG ω hω] at hcl hnd
      exact hω z hz hcl hnd
    · rw [hcN ω hω] at hnd
      exact absurd (mem_dom_id hz) hnd
  -- the chart field and its data
  let h'' : Ω → Ω → DistOn upperHalfPlaneOpens := fun ω₀ ω => recField κ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀)) (h ω)
  have hst : ∀ᵐ ω₀ ∂P, ∃ p : (ℝ → ℝ) × Finset ℝ, IsPiecewiseConstantBoundaryData p.1 p.2 ∧
      IsFlowLineDriver κ p.1 p.2 θ (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀)
        (fun t ω => (E 1 ω).1 t) (fun ω => (E 1 ω).2) := by
    filter_upwards [ae_isFlowLineDriver_second hE hreg (hζ.mono fun ω hω => hω.1), hK] with ω₀ h1 h2
    rw [h2] at h1
    exact h1
  let bJ : Ω → (ℝ → ℝ) × Finset ℝ := fun ω₀ => Classical.epsilon fun p : (ℝ → ℝ) × Finset ℝ =>
    IsPiecewiseConstantBoundaryData p.1 p.2 ∧
      IsFlowLineDriver κ p.1 p.2 θ (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀)
        (fun t ω => (E 1 ω).1 t) (fun ω => (E 1 ω).2)
  let u' : Ω → ℂ → ℝ := fun ω₀ => Classical.epsilon fun u : ℂ → ℝ =>
    IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 u
  have hu' : ∀ ω₀, IsPiecewiseConstantBoundaryData (bJ ω₀).1 (bJ ω₀).2 →
      IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 (u' ω₀) := fun ω₀ hp => by
    obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hp
    exact Classical.epsilon_spec (p := fun u : ℂ → ℝ => IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 u) ⟨u, hu⟩
  let m : Ω → TestOn upperHalfPlaneOpens → ℝ := fun ω₀ φ =>
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ (Chart.pushTest (hc ω₀) φ) +
      chiC κ * Chart.liftDist (c ω₀) φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀) φ
  have hchart : ∀ᵐ ω₀ ∂P, IsPiecewiseConstantBoundaryData (bJ ω₀).1 (bJ ω₀).2 ∧
      IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 (u' ω₀) ∧
      IsGFFWithBoundaryData (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀) (bJ ω₀).1
        (bJ ω₀).2 ∧
      ∀ φ, ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀),
        WholeField.centredField (h'' ω₀) (u' ω₀) ω φ =
          WholeField.centredField h u₀ ω (Chart.pushTest (hc ω₀) φ) + m ω₀ φ := by
    filter_upwards [hst, hG] with ω₀ hp hGω
    obtain ⟨hbp, hfl⟩ := Classical.epsilon_spec hp
    refine ⟨hbp, hu' ω₀ hbp, Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hbp hfl,
      fun φ => Eventually.of_forall fun ω => ?_⟩
    have e1 : h'' ω₀ ω φ = 1 * h ω (Chart.pushTest (isConformal_recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) φ) +
        0 * Chart.oneDist φ + chiC κ * Chart.liftDist (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) φ :=
      Chart.chartTransport_apply' _ _ _ _ _ _
    have e2 : Chart.pushTest (hc ω₀) φ =
        Chart.pushTest (isConformal_recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) φ :=
      pushTest_congr _ _ (hcG ω₀ hGω) φ
    have e3 : Chart.liftDist (c ω₀) = Chart.liftDist (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) := by
      rw [hcG ω₀ hGω]
    simp only [WholeField.centredField, m, sub_apply, e1, e2, e3]
    ring
  -- the a.s. facts under Lemma 6.2's conditional laws
  have hT1 := KernelTower.ae_ae_condExpKernel_of_ae hpast hd1
  have hT3 := KernelTower.ae_ae_condExpKernel_of_ae hpast hβtr
  have hT4 := KernelTower.ae_ae_condExpKernel_of_ae hpast hcat
  have hT2 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀),
      recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω) = recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀) := by
    have hm : Measurable[_root_.InteractingSLE.pastSigma κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E 1]
        (pastMap κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E 1) := by
      rw [pastSigma_eq_comap]
      exact comap_measurable _
    filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hE.2.1 1) hm, hK] with ω₀ h1 h2
    rw [← h2]
    filter_upwards [h1] with ω hω
    have e := pastMap_one_last (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (t₀ := (q : ℝ≥0)) (E := E) ω
    have e' := pastMap_one_last (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (t₀ := (q : ℝ≥0)) (E := E) ω₀
    rw [← e, ← e', hω]
  have hflow : ∀ᵐ ω₀ ∂P,
      IsFlowLine κ (bJ ω₀).1 (bJ ω₀).2 0 θ (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀) β
        (fun ω => (E 1 ω).2) ∧
      (∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀), (E 1 ω).2 = ⊤) ∧
      (∀ ω, Continuous (β ω)) ∧ (∀ ω, β ω 0 = 0) ∧ (∀ t, Measurable fun ω => β ω t) ∧
      (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => β ω t) =ᵐ[condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀]
          fun ω => f (WholeField.centredField (h'' ω₀) (u' ω₀) ω)) ∧
      ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀), ∀ s, 0 < s →
        β ω s ∈ H ∧ αc ω ((q : ℝ≥0) + s) = (c ω₀).2.1 (β ω s) := by
    filter_upwards [hst, hG, hT1, hT2, hT3, hT4] with ω₀ hp hGω h1 h2 h3 h4
    obtain ⟨-, hfl⟩ := Classical.epsilon_spec hp
    refine ⟨?_, h1.mono fun ω hω => hω.1, hβc, hβ0, hβm, fun t => ?_, ?_⟩
    · obtain ⟨h₃, 𝓕, VL, VR, B, ht, hC⟩ := hfl
      refine ⟨h₃, 𝓕, fun t ω => (E 1 ω).1 t, VL, VR, B, ht, hC, ?_⟩
      filter_upwards [h1, h3] with ω hω hβω
      simp only [Complex.ofReal_zero, sub_zero]
      rw [hω.1]
      exact hβω
    · refine ⟨fun X => LP.traceAt t (admDrv h44 hκ hκ4 θ (word₁ κ θ₀ c₀ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀)),
        X + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀))).1, ?_, ?_⟩
      · exact (LP.measurable_traceAt t).comp (measurable_fst.comp ((measurable_admDrv h44 hκ hκ4 θ).comp
          (measurable_const.prodMk (Coupling.measurable_add_distOnConst _))))
      · filter_upwards [h1, h2, h3] with ω hω hr hβω
        have hc1 : Continuous (E 1 ω).1 := continuous_of_regular_top (hreg 1 ω) hω.1
        have e1 : β ω t = LP.traceAt t (E 1 ω).1 :=
          (LP.traceAt_eq_of_isGeneratingTrace hβω hc1.continuousOn (hreg 1 ω).2.1 ENNReal.coe_lt_top).symm
        have e2 : (E 1 ω).1 = (admDrv h44 hκ hκ4 θ (word₁ κ θ₀ c₀ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)),
            field₁ κ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)) (h ω))).1 := by
          funext s
          refine (hω.2.2 s ?_).symm
          rw [hω.1]
          exact ENNReal.coe_lt_top
        have e3 : WholeField.centredField (h'' ω₀) (u' ω₀) ω +
            SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀) =
              field₁ κ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀)) (h ω) := by
          simp only [WholeField.centredField, sub_add_cancel, h'', field₁, Sec7.Prop74B.flowField_zero_zero]
        change β ω t = LP.traceAt t (admDrv h44 hκ hκ4 θ (word₁ κ θ₀ c₀ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀)),
          WholeField.centredField (h'' ω₀) (u' ω₀) ω +
            SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀))).1
        rw [e3, e1, e2, hr]
    · filter_upwards [h4, h2] with ω hω hr s hs
      rw [hcG ω₀ hGω, ← hr]
      exact hω s hs
  have h0H : (0 : ℂ) ∉ H := fun h0 => by
    have h0' : (0 : ℝ) < (0 : ℂ).im := h0
    rw [Complex.zero_im] at h0'
    exact lt_irrefl _ h0'
  exact isEntranceHistoryLocal_of_restart_isFlowLine hκ hκ4
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) h0H hαc hα0 hαm (q₀ := q)
    (fun t => frozenPath_ae_eq_comp (hdet_of_trace h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ u₀ htr) _ t)
    (isEntranceHistoryLocal_frozenPath_first hκ hκ4 hb hh hE hreg hL0 hR0 hu₀ hαc hαm htr) hc hfr
    (b := fun ω₀ => (bJ ω₀).1) (jumps := fun ω₀ => (bJ ω₀).2) (θ := fun _ => θ) (u₀ := u') (h'' := h'')
    (m := m) (β := fun _ => β) (ζ := fun _ ω => (E 1 ω).2) hchart hflow

/-- **`isEntranceHistoryLocal_strip` at the switching time `1`** (the strip system's `α = η^{1,∞}_{−π/2,θ₁}`,
`StripSys.alphaSpec`), stated with `1 : ℝ≥0`. -/
theorem isEntranceHistoryLocal_strip_one (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ 1 θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 1 (E 1 ω).1) ⊤ (αc ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (β ω))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → β ω s ∈ H ∧
      αc ω (1 + s) = (recChart (recOf ((1 : ℝ≥0) : ℝ≥0∞) (E 0 ω))).2.1 (β ω s)) :
    IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P := by
  have e : ((1 : ℚ≥0) : ℝ≥0) = 1 := NNRat.cast_one
  rw [← e] at hE htr hcat
  exact isEntranceHistoryLocal_strip h44 hκ hκ4 hb hh one_pos hE hreg hL0 hR0 hL hR hθ hθπ hu₀ hαc hα0 hαm htr hβc
    hβ0 hβm hβtr hcat

/-! ### `hmark` and (S) for the strip system (STRIPSYS19's consumers) -/

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- On the good event the concatenated driver agrees through `t₀ + r` with the concatenated record driver. -/
theorem catPath_eq_catPath_recsTwo (hreg : ∀ j ω, IsRegularDriver (E j ω)) {r : ℝ≥0} {ω : Ω}
    (hω : ω ∈ goodEv κ b jumps θ₀ q₀ θ r E) {s : ℝ≥0} (hs : s ≤ q₀ + r) :
    catPath (E 0 ω).1 q₀ (E 1 ω).1 s =
      catPath (recW (recsTwo κ b jumps θ₀ q₀ θ r E ω 0)) q₀ (recW (recsTwo κ b jumps θ₀ q₀ θ r E ω 1)) s := by
  have e0 : recsTwo κ b jumps θ₀ q₀ θ r E ω 0 = recOf (q₀ : ℝ≥0∞) (E 0 ω) := pastMap_two_zero ω
  have e1 : recsTwo κ b jumps θ₀ q₀ θ r E ω 1 = recOf (r : ℝ≥0∞) (E 1 ω) := pastMap_two_one hω.1
  have hz0 := lt_zeta_zero_of_mem_goodEv hω
  have hz1 := lt_zeta_one_of_mem_goodEv hω
  have hW0 := Sec7.StripMark.recW_recOf_of_lt (hreg 0 ω) hz0 (Sec7.StripMark.isDrvGood_recOf_of_lt (hreg 0 ω) hz0)
  have hW1 := Sec7.StripMark.recW_recOf_of_lt (hreg 1 ω) hz1 (Sec7.StripMark.isDrvGood_recOf_of_lt (hreg 1 ω) hz1)
  rw [e0, e1]
  unfold catPath
  split_ifs with hst
  · rw [hW0, min_eq_left hst]
  · rw [hW0, hW1, min_self, min_eq_left (tsub_le_iff_left.2 hs)]

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Almost surely the good event holds when both pieces almost surely live forever. -/
theorem ae_mem_goodEv (hreg : ∀ j ω, IsRegularDriver (E j ω)) [MeasurableSpace Ω] {P : Measure Ω}
    (hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) (r : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ q₀ θ r E :=
  hζ.mono fun ω hω => Sec7.StripMark.mem_goodEv_of_lt hreg (by rw [hω.1]; exact ENNReal.coe_lt_top)
    (by rw [hω.2]; exact ENNReal.coe_lt_top)

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The trace hypothesis of STRIPSYS19's consumers from a generating trace of the concatenated driver on `[0, ∞)`. -/
theorem ae_trace_recsTwo (hreg : ∀ j ω, IsRegularDriver (E j ω)) [MeasurableSpace Ω] {P : Measure Ω}
    (hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) {αc : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 q₀ (E 1 ω).1) ⊤ (αc ω)) (r : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (W' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), ((q₀ + r : ℝ≥0) : ℝ≥0∞) < ζ' ∧
      IsGeneratingTrace W' ζ' (αc ω) ∧ ∀ s : ℝ≥0, s ≤ q₀ + r →
        W' s = catPath (recW (recsTwo κ b jumps θ₀ q₀ θ r E ω 0)) q₀ (recW (recsTwo κ b jumps θ₀ q₀ θ r E ω 1)) s := by
  filter_upwards [ae_mem_goodEv (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) hreg hζ r, htr] with ω hg hα
  exact ⟨_, ⊤, ENNReal.coe_lt_top, hα, fun s hs => catPath_eq_catPath_recsTwo hreg hg hs⟩

/-- **`hmark` for the strip system** (STRIPSYS19's `isHistoryAvoidanceLocal_pastTwo` with Lemma 6.2's inputs
discharged: `hdet` by PROVE-STRIPSYS21, `hloc` by `isEntranceHistoryLocal_strip`): the range of the angle-varying path
through `q + r` is a local set marked by the two retained records. -/
theorem isHistoryAvoidanceLocal_pastTwo_strip (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {q : ℚ≥0} (hq : 0 < q)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 (q : ℝ≥0) (E 1 ω).1) ⊤ (αc ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (β ω))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → β ω s ∈ H ∧
      αc ω ((q : ℝ≥0) + s) = (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).2.1 (β ω s)) (r : ℝ≥0) :
    WholeField.IsHistoryAvoidanceLocal (pastTwo κ b jumps θ₀ (q : ℝ≥0) θ r E)
      (fun ω => αc ω '' Icc 0 ((q : ℝ≥0) + r) ∩ H) (WholeField.centredField h u₀) P := by
  obtain ⟨_, _, -, -, -, -, hD⟩ := exists_borel_drivers h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ
  have hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ := hD.mono fun ω hω => ⟨hω.1, hω.2.1⟩
  have hT : 0 < (q : ℝ≥0) + r := add_pos_of_pos_of_nonneg (by exact_mod_cast hq) zero_le
  exact Sec7.StripMark.isHistoryAvoidanceLocal_pastTwo hreg hT (ae_mem_goodEv hreg hζ r)
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀).measurable hαc hα0 hαm
    (hdet_of_trace h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ u₀ htr)
    (isEntranceHistoryLocal_strip h44 hκ hκ4 hb hh hq hE hreg hL0 hR0 hL hR hθ hθπ hu₀ hαc hα0 hαm htr hβc hβ0 hβm
      hβtr hcat) (ae_trace_recsTwo hreg hζ htr r)

/-- **(S) for the strip system** (STRIPSYS19's `ae_hasSideHeights_stage_of_lemma62` with Lemma 6.2's inputs and the good
event discharged): for every version `g` of the local-set mean of `αc([0, q + r]) ∩ ℍ`, almost surely on the good event
every harmonic representative of `g` has the right-side heights of the continuation at every later trace point. -/
theorem ae_hasSideHeights_stage_strip (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {q : ℚ≥0} (hq : 0 < q)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 (q : ℝ≥0) (E 1 ω).1) ⊤ (αc ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (β ω))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → β ω s ∈ H ∧
      αc ω ((q : ℝ≥0) + s) = (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).2.1 (β ω s)) (r : ℝ≥0)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : LocalSets.IsLocalSetMean (fun ω => αc ω '' Icc 0 ((q : ℝ≥0) + r) ∩ H) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ (q : ℝ≥0) θ r E → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (αc ω '' Icc 0 ((q : ℝ≥0) + r) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (αc ω '' Icc 0 ((q : ℝ≥0) + r) ∩ H) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ (W' : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ) (ζ : ℝ≥0∞), IsGeneratingTrace W' ζ α →
        ContinuousOn W' {s | (s : ℝ≥0∞) < ζ} → W' 0 = 0 →
        (∀ s : ℝ≥0, s ≤ (q : ℝ≥0) + r → W' s = catPath (recW (recsTwo κ b jumps θ₀ (q : ℝ≥0) θ r E ω 0)) (q : ℝ≥0)
          (recW (recsTwo κ b jumps θ₀ (q : ℝ≥0) θ r E ω 1)) s) →
        InjOn α {t | (t : ℝ≥0∞) ≤ ζ} → (((q : ℝ≥0) + r : ℝ≥0) : ℝ≥0∞) < ζ →
        ∀ t₁ : ℝ≥0, (q : ℝ≥0) < t₁ → (t₁ : ℝ≥0∞) < ζ → α t₁ ∈ H →
          Sec7.StripGeom.HasSideHeights κ θ α 0 W' ((q : ℝ≥0) + r) (α t₁) v u₀ := by
  obtain ⟨_, _, -, -, -, -, hD⟩ := exists_borel_drivers h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ
  have hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ := hD.mono fun ω hω => ⟨hω.1, hω.2.1⟩
  have hT : 0 < (q : ℝ≥0) + r := add_pos_of_pos_of_nonneg (by exact_mod_cast hq) zero_le
  exact Sec7.StripMark.ae_hasSideHeights_stage_of_lemma62 hκ hb hh hE hreg r hT hu₀ (ae_mem_goodEv hreg hζ r) hαc
    hα0 hαm (hdet_of_trace h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ u₀ htr)
    (isEntranceHistoryLocal_strip h44 hκ hκ4 hb hh hq hE hreg hL0 hR0 hL hR hθ hθπ hu₀ hαc hα0 hαm htr hβc hβ0 hβm
      hβtr hcat) (ae_trace_recsTwo hreg hζ htr r) hg

end Strip

end StagedEntrance

end Restart

end InteractingSLE
