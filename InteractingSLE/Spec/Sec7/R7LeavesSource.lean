/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RefWireOuter
import InteractingSLE.Spec.Sec7.StripPocketVersions
import InteractingSLE.Spec.Sec7.WallsPath
import InteractingSLE.Spec.Sec7.R7StopInSelect

/-!
# Theorem R.7's extremal reference: the source objects on the R.7 field

Packet PROVE-R7-LEAVES. The extremal (Aux. lemma 131, `max(r_L, r_R) = k/2 − 4`) reference of Theorem 1.2's R.7 input
asked for about thirty source facts about an abstract reference object (`Wire.Now.ReferenceObjects`): the coupling,
its chart transport, the walls' continuity, determination and locality, the counterflow's trace, and so on. On the
R.7 field of `R7Outer.IsR7OuterConfig` (PROVE-R7-OUTER; the GFF with data `prop74Data (r7A + c) (r7B + c')`, its
centred counterflow and the four incoming flow lines, all Borel functions of the field) these facts are theorems:

* `r7_cf_bounds`, `ae_counterflow_trace_r7`: the counterflow word of the R.7 data is admissible for every
  `c, c' ≥ 0`, so almost surely the counterflow lives forever, has a continuous driver from `0` and a continuous
  generating trace (Zhan's Aux. 6 trace theorem; no Aux. 7 input);
* `exists_cfVersion_r7`, `ae_isLoewnerTrace_counterflow_r7`: a version of that trace, continuous at every sample;
* `exists_wallVersion`: a version of an almost surely simple proper measurable curve, continuous at every sample;
* `IsCfDecomp`, `exists_isCfDecomp`: the transport, translation and coupling data of the frozen
  `IsCenteredCounterflowDriver (16/k)`, rewritten at the parameter `k = 16/(16/k)`;
* `hdet_of_borel`, `isEntranceHistoryLocal_of_flowLine`: Lemma 6.2's determination and locality inputs for a version
  of a Borel flow line.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R7Leaves

open R7Outer Sec5.Prop55Half

/-! ### The counterflow of the R.7 field -/

section Counterflow

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **The R.7 data are below the counterflow's non-hit heights** (the hypotheses of
`StripPocketPath.counterflowData_bounds_off`) for every `c, c' ≥ 0`: `r7A ≥ λ − πχ/2` because `max(θ_L, π/2) ≥ π/2`,
and `r7B ≥ λ + πχ/2` because `min(θ_R, −π/2) ≤ −π/2`. -/
theorem r7_cf_bounds (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    (∀ x : ℝ, x < 0 → x ∉ ({0} : Finset ℝ) →
      prop74Data (r7A k rR + c) (r7B k rL + c') x ≤ -sleLambda (16 / k) + π / 2 * chiC (16 / k)) ∧
    ∀ x : ℝ, 0 < x → x ∉ ({0} : Finset ℝ) →
      sleLambda (16 / k) - π / 2 * chiC (16 / k) ≤ prop74Data (r7A k rR + c) (r7B k rL + c') x := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hhi : π / 2 * chiC (16 / k) ≤ r7ThetaHi k rR * chiC (16 / k) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hχ.le
  have hlo : r7ThetaLo k rL * chiC (16 / k) ≤ -(π / 2) * chiC (16 / k) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hχ.le
  have hpχ : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le hχ.le
  refine ⟨fun x hx _ => ?_, fun x hx _ => ?_⟩
  · simp only [prop74Data, hx, ↓reduceIte, r7A]
    linarith
  · simp only [prop74Data, not_lt_of_ge hx.le, ↓reduceIte, r7B]
    linarith

/-- **The counterflow of the R.7 field has a continuous trace** (`StripPocketPath.ae_counterflow_trace` for the R.7
data; its word is admissible by `r7_cf_bounds`): almost surely the lifetime is infinite, the driver is continuous from
`0`, and it has a continuous generating trace on `[0, ∞)`. -/
theorem ae_counterflow_trace_r7 (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / (16 / k) := by positivity
  obtain ⟨hbL, hbR⟩ := r7_cf_bounds (rL := rL) (rR := rR) hk4 hc hc'
  have hbd := StripPocketPath.counterflowData_bounds_off hκ (g := prop74Data (r7A k rR + c) (r7B k rL + c'))
    (J := {0}) hbL hbR
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (StripSysField.isPiecewiseConstant_counterflowData (16 / k) hb) hbd.1 hbd.2
  have hF' := Theorem15.isOrderedForceWord_flowLine
    (StripSysField.counterflowData (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')))
    (StripSysField.counterflowJumps {0}) 0
  have hE := hC'.1
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hpth
  have hw : Continuous fun t => W' t ω := by
    have := hpth.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact ⟨hζ, hw, hpth.1, η, hη⟩

/-- **A version of the R.7 counterflow's trace** (`StripPocketVersions.exists_cfVersion` for the R.7 field):
continuous on `[0, ∞)` at every sample, in `ℍ̄`, `0` at `0`, measurable at fixed times, and almost surely the
generating trace of the counterflow driver `W′` on `[0, ∞)`. -/
theorem exists_cfVersion_r7 (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') :
    ∃ η : Ω → ℝ → ℂ, (∀ ω, ContinuousOn (η ω) (Ici 0)) ∧ (∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) ∧
      (∀ ω, η ω 0 = 0) ∧ (∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t) := by
  set w : Ω → ℝ≥0 → ℝ := fun ω => Sec5.CfRegQ.hDrv (Sec5.Cond44Ref.cfHistory W' ζ' ω) with hw
  have hwm : Measurable w := Sec5.CfRegQ.measurable_hDrv.comp (Sec5.Cond44Ref.measurable_cfHistory
    (Sec5.Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf))
  have hwe : ∀ᵐ ω ∂P, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η) ∧ w ω = fun t => W' t ω := by
    filter_upwards [ae_counterflow_trace_r7 hk4 hc hc' hh hcf] with ω hω
    obtain ⟨hζ, hc, h0, η, hη⟩ := hω
    refine ⟨hc, h0, ⟨η, hη⟩, funext fun t => ?_⟩
    exact WangWu.pathsOfHistory_killedHistory_driver hc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  obtain ⟨γ, hc, h0, hH, hm, htr⟩ := StripPocketVersions.exists_traceVersion hwm (by
    filter_upwards [hwe] with ω hω
    obtain ⟨hc, h0, ⟨η, hη⟩, he⟩ := hω
    rw [he]
    exact ⟨hc, h0, η, hη⟩)
  refine ⟨fun ω s => γ ω s.toNNReal, fun ω => ((hc ω).comp continuous_real_toNNReal).continuousOn,
    fun ω t _ => hH ω _, fun ω => by simpa using h0 ω, fun t _ => hm _, ?_⟩
  filter_upwards [htr, hwe] with ω h1 h2
  rw [h2.2.2.2] at h1
  simpa only [Real.toNNReal_coe] using h1

/-- **Every version of the R.7 counterflow's trace is a Loewner trace** (`StripPocketPath.ae_isLoewnerTrace_counterflow`
for the R.7 field). -/
theorem ae_isLoewnerTrace_counterflow_r7 (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω) ∧ Continuous (fun s : ℝ => W' s.toNNReal ω) ∧
      W' 0 ω = 0 := by
  filter_upwards [ae_counterflow_trace_r7 hk4 hc hc' hh hcf, hηtr] with ω hω hη
  obtain ⟨-, hc, h0, -⟩ := hω
  refine ⟨StripPocketPath.isLoewnerTrace_congr (fun s hs => ?_) (isLoewnerTrace_of_isGeneratingTrace hη),
    hc.comp continuous_real_toNNReal, h0⟩
  simp only [Real.coe_toNNReal _ (mem_Ici.1 hs)]

end Counterflow

/-! ### The coupling data of the centred counterflow at the parameter `k` -/

section Decomp

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The data of the frozen `IsCenteredCounterflowDriver (16/k) P h W′ ζ′`**, with `16/(16/k)` written `k`: the
piecewise-constant data `b′` (exceptional set `J′`) of the parameter field `h′` (the chart transport of `h` from the
infinity source), its translate `h″` by `0 · χ(k)` and the optional hull coupling of the flow-line word of `b′` at
parameter `k` with filtration `𝓕`, force points `VL`, `VR` and Brownian motion `B`. -/
def IsCfDecomp (k : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens)
    (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) : Prop :=
  IsPiecewiseConstantBoundaryData b' J' ∧
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / k))) (chiC k) (h ω) (h' ω)) ∧
    (∀ ω, IsTranslateAddConst 0 (0 * chiC k) (h' ω) (h'' ω)) ∧
    IsOptionalHullCoupling k (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) P 𝓕 W' VL VR B ζ' h''

/-- The frozen `IsCenteredCounterflowDriver (16/k)` unpacked at the parameter `k` (`16/(16/k) = k`). -/
theorem exists_isCfDecomp {k : ℝ} (hk : k ≠ 0) {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') :
    ∃ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B := by
  have e : 16 / (16 / k) = k := by field_simp
  obtain ⟨b', J', h', hb', htr, h'', 𝓕, VL, VR, B, htac, hC⟩ := hcf
  rw [e] at htr htac hC
  exact ⟨b', J', h', h'', 𝓕, VL, VR, B, hb', htr, htac, hC⟩

end Decomp

/-! ### Versions of the walls -/

section Walls

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A version of an almost surely simple proper curve**, continuous and `0` at `0` at every sample, measurable at
fixed times: the curve itself off a measurable null set, the constant `0` on it. -/
theorem exists_wallVersion {α : Ω → ℝ≥0 → ℂ} (hm : ∀ t, Measurable fun ω => α ω t)
    (hreg : ∀ᵐ ω ∂P, IsSeedProper (α ω)) :
    ∃ R : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (R ω)) ∧ (∀ ω, R ω 0 = 0) ∧ (∀ t, Measurable fun ω => R ω t) ∧
      ∀ᵐ ω ∂P, R ω = α ω := by
  classical
  set N : Set Ω := toMeasurable P {ω | ¬ IsSeedProper (α ω)} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 hreg
  have hgood : ∀ ω, ω ∉ N → IsSeedProper (α ω) := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable _ _ hc)
  refine ⟨fun ω => if ω ∈ N then fun _ => 0 else α ω, fun ω => ?_, fun ω => ?_, fun t => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuous_const
    · simp only [hω, ↓reduceIte]; exact (hgood ω hω).1
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hgood ω hω).2.2.1
  · have : (fun ω => (if ω ∈ N then fun _ => (0 : ℂ) else α ω) t) = fun ω => if ω ∈ N then 0 else α ω t := by
      funext ω; split_ifs <;> rfl
    rw [this]
    exact Measurable.ite hNm measurable_const (hm t)
  · have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hae] with ω hω
    simp only [hω, ↓reduceIte]

/-- **Lemma 6.2's determination input for a version of a Borel curve of the field**: if `α ω = Φ (h ω)` at every
sample and `R = α` almost surely, then each coordinate of `R` is almost surely a Borel function of the centred field
`h − u₀`. -/
theorem hdet_of_borel {h : Ω → DistOn upperHalfPlaneOpens} {α R : Ω → ℝ≥0 → ℂ}
    {Φ : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ} (hΦ : Measurable Φ) (hαΦ : ∀ ω, α ω = Φ (h ω))
    (hRα : ∀ᵐ ω ∂P, R ω = α ω) (u₀ : ℂ → ℝ) (t : ℝ≥0) :
    ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  set cst : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u₀ with hcst
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens => g + cst := Coupling.measurable_add_distOnConst cst
  refine ⟨fun g => Φ (g + cst) t, (measurable_pi_apply t).comp (hΦ.comp hadd), ?_⟩
  filter_upwards [hRα] with ω hω
  have hcent : WholeField.centredField h u₀ ω + cst = h ω := by
    simp only [WholeField.centredField, hcst, sub_add_cancel]
  simp only [hcent, hω, hαΦ ω]

/-- **Lemma 6.2's locality input for a version of a flow line of infinite lifetime** (as
`Aux37Walls.isEntranceHistoryLocal_const`): a continuous, measurable version `R` from `0` of a flow line `α` of the
field `h` is entrance-history local for the centred field. -/
theorem isEntranceHistoryLocal_of_flowLine [IsProbabilityMeasure P] {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {α : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b jumps 0 θ P h α ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {R : Ω → ℝ≥0 → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t)
    (hRα : ∀ᵐ ω ∂P, R ω = α ω) :
    Sec6.IsEntranceHistoryLocal R (WholeField.centredField h u₀) P := by
  have hfl' : IsFlowLine κ b jumps 0 θ P h R ζ :=
    IsFlowLine.congr_path hfl (hRα.mono fun ω hω t _ => by rw [hω])
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  have h0H : (0 : ℂ) ∉ H := fun h0' => by
    have h' : (0 : ℝ) < (0 : ℂ).im := h0'
    simp at h'
  refine Lemma71G.isEntranceHistoryLocal_of_capAt hhm hRc hRm (fun ω => by rw [hR0 ω]; exact h0H) fun n => ?_
  exact Restart.StagedEntrance.isEntranceHistoryLocal_frozenPath_of_isFlowLine hκ hκ4 hb hh hfl' hζ hu₀ hRc hRm
    (n : ℝ≥0) (Eventually.of_forall fun ω t _ => rfl)

end Walls

end InteractingSLE.Sec7.R7Leaves
