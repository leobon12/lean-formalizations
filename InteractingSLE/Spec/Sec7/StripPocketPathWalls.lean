/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketConfigWalls
import InteractingSLE.Spec.Sec7.StripWallStage0
import InteractingSLE.Spec.Sec7.StripDetPath
import InteractingSLE.Spec.Sec5.CfRegQ

/-!
# Theorem 1.3's pocket word: the unchanged extremal path `β = η_{π/2}` and the common prefix of `β^{(q)}`

Packet PROVE-STRIPSYS31. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L431–L470,
pp. 410–411): "Each initial constant-angle path has only original-boundary cumulative values, all nonnegative by the
chosen heights. It therefore has the earlier noncolliding continuous simple proper law and is field determined by
(4.4)"; "First construct only `α` and the unchanged extremal path `β = η_{π/2}`"; "Now replace the future of `β`
after this fixed own time `r` by the angle-`θ₂` continuation, obtaining `β^{(r)}`. Its prefix through `r`, the field,
`α`, and the counterflow are unchanged."

In the strip system (`StripSys.IsStripSystem`) the path `β = η_{π/2}` is the one-instruction staged history
`StripSys.leftExtremalSpec`; its version is a family `β` continuous at every sample, `0` at time `0`, and almost surely
a generating trace on `[0, ∞)` of the driver `(E 0).1` of that history. Here:

* `isFlowLineDriver_leftExtremal`: the driver of `leftExtremalSpec` is the angle-`π/2` flow-line driver of `h` itself
  (as `StripWall.isFlowLineDriver_stage_zero` for the first piece of a two-angle path);
* **`ae_simple_trace_leftExtremal`**, **`ae_isSimpleProper_leftExtremal`**: almost surely the lifetime is infinite and
  the driver has a simple transient trace; every version of `β` is almost surely a simple proper curve;
* **`ae_eq_leftExtremal_of_le`** ("Its prefix through `r` … unchanged"): for every own time `r`, a version of the
  two-angle path `β^{(r)} = η^{r,∞}_{π/2,θ₂}` agrees almost surely with the version of `β` on `[0, r]`. Both first
  pieces are angle-`π/2` flow lines of the same field with the same data; for the (4.4) word of the strip heights they
  are both almost surely the field-determined driver `AdmCode.admDrv (c₀, h)` (R48-safe:
  `AdmCode.Theorem12ParamCond44Statement`, proved from the §4.2 reference, no Theorem 1.2/1.3), and generating traces
  of a continuous driver are unique;
* **`ae_counterflow_trace`**, **`ae_isLoewnerTrace_counterflow`** (the counterflow's trace in the chart `m`, p. 410):
  the strip system's centred counterflow driver `W′` is the flow-line driver of an admissible word at `κ′ = 16/κ`
  (Remark 4.8 (b): the strip heights put the counterflow data inside Remark 4.1's bounds at `κ′`), so almost surely its
  lifetime is infinite, it is continuous from `0` and it has a continuous generating trace on `[0, ∞)` (Aux. lemma 7's
  trace part, `ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible`); every version `η` of
  that trace is a continuous Loewner trace of `s ↦ W′(s⁺)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec7

namespace StripPocketPath

open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)

/-! ### The driver of `β = η_{π/2}` -/

section Extremal

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] in
/-- The only instruction of `leftExtremalSpec` launches the angle-`π/2` piece from the root `0` in the identity
chart. -/
theorem launches_run_one_leftExtremalSpec (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps StripSys.leftExtremalSpec D (0 + 1)).2.2.2.1 0 =
      some (Exist.shiftChart 0, π / 2) := by
  change (ExplState.launch (ExplState.init 0) 0 (D 0) (π / 2) ⊤).2.2.2.1 0 = _
  rw [Exist.Staged.launches_launch, Function.update_self]
  rfl

/-- **The driver of `β = η_{π/2}` is the angle-`π/2` flow-line driver of `h`** with the data `b` (the conditional law
at stage `0` is the law, the stage-`0` chart is the identity chart). -/
theorem isFlowLineDriver_leftExtremal (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h StripSys.leftExtremalSpec E) :
    IsFlowLineDriver κ b jumps (π / 2) P h (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) := by
  obtain ⟨ω₀, hω₀⟩ := (hE.2.2.2 0).exists
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hω₀ _ _ (launches_run_one_leftExtremalSpec _)
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

/-- **`β = η_{π/2}` has a simple transient trace** (Remark 2.3 and Proposition 4.12 for its flow-line word, which
satisfies (4.4) by the heights of `b` at `π/2`): almost surely its lifetime is infinite and its driver has an injective
generating trace on `[0, ∞)`, in `ℍ` at positive times and tending to `∞`. -/
theorem ae_simple_trace_leftExtremal (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h StripSys.leftExtremalSpec E)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + π / 2 * chiC κ ≤ -sleLambda κ + π * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + π / 2 * chiC κ) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η ∧ Injective η ∧
      (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := isFlowLineDriver_leftExtremal hκ hb hh hE
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps 0
  have h44 := StripDet.cond44_flowLine_of_heights hκ hb (π / 2) hL0 hR0
  filter_upwards [Sec4.ae_simple_trace_of_cond44 hκ hκ4 hF h44 hC.1, Wire.prop412 hκ hκ4 hF h44 hC.1]
    with ω h1 h2
  obtain ⟨hζ, -, η, hη, hinj, hH, -⟩ := h1
  exact ⟨hζ, η, hη, hinj, hH, h2.2.2 η hη⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **A version of a one-piece path with a simple transient trace is simple proper** almost surely. -/
theorem ae_isSimpleProper_of_simple_trace (hreg : ∀ ω, IsRegularDriver (E 0 ω))
    (hsimple : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 ⊤ η ∧ Injective η ∧
      (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop)
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 0 ω).1 ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (γ ω) := by
  filter_upwards [hsimple, hγtr] with ω hω hγ
  obtain ⟨hζ, η, hη, hinj, hH, htr⟩ := hω
  have hc := StripWall.continuous_of_isRegularDriver (hreg ω) hζ
  have heq : γ ω = η := funext fun t => by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hγ hc.continuousOn (hreg ω).2.1 ENNReal.coe_lt_top,
      LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn (hreg ω).2.1 ENNReal.coe_lt_top]
  refine ⟨hγc ω, heq ▸ hinj, hγ0 ω, heq ▸ hH, ?_⟩
  rw [heq]
  exact htr

end Extremal

/-! ### The strip system's extremal path -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The (4.4) heights at the angle `π/2` from Aux. lemma 130's height choice. -/
theorem heights_pi_div_two (hκ : 0 < κ) (hκ4 : κ < 4)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    (∀ y : ℝ, y < 0 → y ∉ jumps → b y + π / 2 * chiC κ ≤ -sleLambda κ + π * chiC κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + π / 2 * chiC κ := by
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => hcumR _ StripSys.pi_div_two_mem_Icc y hy hyJ⟩
  have := hcumL _ StripSys.pi_div_two_mem_Icc y hy hyJ
  linarith

/-- **`β = η_{π/2}` of the strip system has a simple transient trace** almost surely (Aux. lemma 130's height
choice). -/
theorem ae_simple_trace_leftExtremal_strip (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨hL0, hR0⟩ := heights_pi_div_two hS.kappa_pos hS.kappa_lt_four hcumL hcumR
  exact ae_simple_trace_leftExtremal hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff
    hS.isStagedHistory_leftExtremal hL0 hR0

/-- **Every version of `β = η_{π/2}` is almost surely a simple proper curve** (spec p. 410). -/
theorem ae_isSimpleProper_leftExtremal (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (β ω) :=
  ae_isSimpleProper_of_simple_trace hregE (ae_simple_trace_leftExtremal_strip hS hcumL hcumR) hβc hβ0 hβtr

/-- The two first pieces (of `β^{(r)}` and of `β`) are almost surely the same field-determined driver: both are
`AdmCode.admDrv (π/2) (c₀, h)` with infinite lifetime. -/
theorem ae_driver_betaSpec_eq_leftExtremal (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0) :
    ∀ᵐ ω ∂P, (Es (StripSys.betaSpec r θ₂) 0 ω).2 = ⊤ ∧ (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧
      (Es (StripSys.betaSpec r θ₂) 0 ω).1 = (Es StripSys.leftExtremalSpec 0 ω).1 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  obtain ⟨hL0, hR0⟩ := heights_pi_div_two hκ hκ4 hcumL hcumR
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hcw : ∀ {Wd : ℝ≥0 → Ω → ℝ} {ζd : Ω → ℝ≥0∞},
      IsFlowLineDriver κ b jumps (π / 2) P h Wd ζd → IsFlowLineDriver κ c₀.fn c₀.jumps (π / 2) P h Wd ζd :=
    fun hfl => (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
      (fun y hy => hc₀ y hy)).2 hfl
  have h44c : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 (π / 2))
      (flowLineRhoR κ c₀.fn c₀.jumps 0 (π / 2)) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData (π / 2)
      (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL0 y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR0 y hy hyJ
  have hβd := hcw (StripWall.isFlowLineDriver_stage_zero hκ hb hS.gff (hS.isStagedHistory_beta hθ₂ r))
  have hEd := hcw (isFlowLineDriver_leftExtremal hκ hb hS.gff hS.isStagedHistory_leftExtremal)
  filter_upwards [AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 (π / 2) c₀ h44c hβd,
    AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 (π / 2) c₀ h44c hEd] with ω h1 h2
  refine ⟨h1.1, h2.1, funext fun t => ?_⟩
  rw [← h1.2.2 t (by rw [h1.1]; exact ENNReal.coe_lt_top), ← h2.2.2 t (by rw [h2.1]; exact ENNReal.coe_lt_top)]

/-- **The common prefix** ("Its prefix through `r` … unchanged", p. 411): a version of `β^{(r)} = η^{r,∞}_{π/2,θ₂}`
agrees almost surely with the version of `β = η_{π/2}` on `[0, r]`. -/
theorem ae_eq_leftExtremal_of_le (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) 0 ω))
    {L β : Ω → ℝ≥0 → ℂ}
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
      (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (L ω))
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ r → L ω t = β ω t := by
  filter_upwards [ae_driver_betaSpec_eq_leftExtremal h44 hS hcumL hcumR hθ₂ r, hLtr, hβtr]
    with ω hd hL hβ t ht
  obtain ⟨hζ, -, he⟩ := hd
  have hL' : IsGeneratingTrace (Es (StripSys.betaSpec r θ₂) 0 ω).1 r (L ω) :=
    IsGeneratingTrace.of_eqOn_lt hL fun s hs => (catPath_of_le (ENNReal.coe_lt_coe.1 hs).le).symm
  have hβ' : IsGeneratingTrace (Es (StripSys.betaSpec r θ₂) 0 ω).1 r (β ω) :=
    LP.isGeneratingTrace_mono (he ▸ hβ) le_top
  have hcont : ContinuousOn (Es (StripSys.betaSpec r θ₂) 0 ω).1 {s : ℝ≥0 | (s : ℝ≥0∞) < r} :=
    (StripWall.continuous_of_isRegularDriver (hregβ ω) hζ).continuousOn
  exact IsGeneratingTrace.eq_of_le hL' hβ' hcont (hregβ ω).2.1 (ENNReal.coe_le_coe.2 ht)

/-! ### The counterflow's trace in the chart `m` -/

/-- **Remark 4.8 (b)'s bounds off the jumps**: if `g ≤ −λ + π/2 χ` on `ℝ₋` and `g ≥ λ − π/2 χ` on `ℝ₊` off the jumps
`J`, the counterflow data are `≤ −λ′ + πχ(κ′)` on `ℝ₋` and `≥ λ′ − πχ(κ′)` on `ℝ₊` off the counterflow jumps
(`Sec5.CfRegQ.counterflowData_bounds` with the jumps excluded). -/
theorem counterflowData_bounds_off (hκ : 0 < κ) {g : ℝ → ℝ} {J : Finset ℝ}
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → g x ≤ -sleLambda κ + π / 2 * chiC κ)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda κ - π / 2 * chiC κ ≤ g x) :
    (∀ y : ℝ, y < 0 → y ∉ StripSysField.counterflowJumps J →
      StripSysField.counterflowData κ g y ≤ -sleLambda (16 / κ) + π * chiC (16 / κ)) ∧
      ∀ y : ℝ, 0 < y → y ∉ StripSysField.counterflowJumps J →
        sleLambda (16 / κ) - π * chiC (16 / κ) ≤ StripSysField.counterflowData κ g y := by
  have hlam := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have hchi := Sec4.chiC_sixteen_div hκ
  have hJ : ∀ y : ℝ, y ∉ StripSysField.counterflowJumps J → -y⁻¹ ∉ J := fun y hy hm => hy <| by
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-y⁻¹, hm, ?_⟩)
    rw [inv_neg, inv_inv, neg_neg]
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · have hpos : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have h1 := hR _ hpos (hJ y hyJ)
    simp only [StripSysField.counterflowData, StripSysField.inverseData, StripSysField.returnData,
      StripSysField.cfOffset, StripSysField.cfCoeff, StripSysField.liftBoundary, hy, ↓reduceIte, hchi, hlam]
    nlinarith [Real.pi_pos]
  · have hneg : -y⁻¹ < 0 := neg_neg_iff_pos.2 (inv_pos.2 hy)
    have h1 := hL _ hneg (hJ y hyJ)
    simp only [StripSysField.counterflowData, StripSysField.inverseData, StripSysField.returnData,
      StripSysField.cfOffset, StripSysField.cfCoeff, StripSysField.liftBoundary, not_lt.2 hy.le, ↓reduceIte, hchi,
      hlam]
    nlinarith [Real.pi_pos]

/-- **The strip system's counterflow has a continuous trace** (p. 410; Remark 4.8 (b) and Aux. lemma 7 at
`κ′ = 16/κ`): almost surely the lifetime is infinite, the driver is continuous from `0`, and it has a continuous
generating trace on `[0, ∞)`. -/
theorem ae_counterflow_trace (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η := by
  have hκ := hS.kappa_pos
  have hb := hS.boundaryData
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hS.gff hS.counterflow
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hbd := counterflowData_bounds_off hκ (g := b) (J := jumps)
    (fun x hx hxJ => by have := hcumL _ hm x hx hxJ; linarith)
    (fun x hx hxJ => by have := hcumR _ hp x hx hxJ; linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (StripSysField.isPiecewiseConstant_counterflowData κ hb) hbd.1 hbd.2
  have hF' := Theorem15.isOrderedForceWord_flowLine (StripSysField.counterflowData κ b)
    (StripSysField.counterflowJumps jumps) 0
  have hE := hC'.1
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hpth
  have hw : Continuous fun t => W' t ω := by
    have := hpth.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact ⟨hζ, hw, hpth.1, η, hη⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- `IsLoewnerTrace` only depends on the trace on `[0, ∞)`. -/
theorem isLoewnerTrace_congr {Wd : ℝ → ℝ} {η η' : ℝ → ℂ} (he : EqOn η η' (Ici 0)) (hη : IsLoewnerTrace Wd η) :
    IsLoewnerTrace Wd η' := by
  obtain ⟨h0, hc, hK⟩ := hη
  refine ⟨(he (mem_Ici.2 le_rfl)).symm.trans h0, hc.congr fun s hs => (he hs).symm, fun t ht => ?_⟩
  rw [hK t ht, (he.mono Icc_subset_Ici_self).image_eq]

/-- **Every version of the counterflow's trace is a Loewner trace** (`htrace` of
`StripPocketConfig.pocketWordEvolution_of_stripPocket`): if `η` is almost surely a generating trace on `[0, ∞)` of the
counterflow driver `W′`, then almost surely `η` is a continuous Loewner trace of `s ↦ W′(s⁺)`, which is continuous and
starts at `0`. -/
theorem ae_isLoewnerTrace_counterflow (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω) ∧ Continuous (fun s : ℝ => W' s.toNNReal ω) ∧
      W' (0 : ℝ).toNNReal ω = 0 := by
  filter_upwards [ae_counterflow_trace hS hcumL hcumR, hηtr] with ω hω hη
  obtain ⟨-, hc, h0, -⟩ := hω
  refine ⟨isLoewnerTrace_congr (fun s hs => ?_) (isLoewnerTrace_of_isGeneratingTrace hη),
    hc.comp continuous_real_toNNReal, by rw [Real.toNNReal_zero]; exact h0⟩
  simp only [Real.coe_toNNReal _ (mem_Ici.1 hs)]

end Strip

end StripPocketPath

end Sec7

end InteractingSLE
