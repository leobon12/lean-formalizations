/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelGB6Chart
import InteractingSLE.Spec.Supplement.GB6RestartProof
import InteractingSLE.Spec.Sec4.Aux25Prob
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# GB6's flow prefix does not return to its base; GB6's retained chart for the actual flow

Packet PROVE-Q3-REL2, first step ("prove the no-return condition"). PROVE-Q3-REL's `isRetainedChartOff_relMap` needs
the flow trace not to return to `0` on `(0, σ]` (`hNR`). For a flow line (`0 < κ < 4`) this is Aux. lemma 25: the
trace of an integrated `SLE_κ(ρ)` evolution is injective before its lifetime
(`IsIntegratedSLEEvolution.ae_injOn_lt`), and its value at `0` is `0`.

* **`ae_trace_ne_zero_of_isFlowLineDriver`**: almost surely, every continuous generating trace of a flow-line driver
  does not vanish at positive times before the lifetime;
* `exists_frozen_retainedChartOff` (deterministic): from a generating trace with no return to `0` up to the stop `s`, a
  globally continuous driver `U` (the flow driver frozen after a time `t₂ ∈ (s, ζα)`) with a global Loewner trace,
  agreeing with the flow on `[0, t₂]`, for which GB6's retained chart is an `IsRetainedChartOff`;
* **`ae_exists_frozen_retainedChartOff`**: the same almost surely on the interior-tip event of GB6's setting.

The frozen driver has the same relative map and clock as the actual flow driver (`GB6.relMap_eq_of_eqOn`,
`GB6.relClock_eq_of_eqOn`), so consumers may work with it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Supp8.Q3Kernel

open GB6 (relMap relInv)
open Q3Rel (invHull relLog relBad IsRetainedChartOff)
open YuanCorollary13 (extDrive extTrace)

/-! ### No return of the flow prefix -/

/-- **No return of a flow line to its base** (Aux. lemma 25, `0 < κ < 4`): almost surely every continuous generating
trace of a flow-line driver does not vanish at positive times before the lifetime. -/
theorem ae_trace_ne_zero_of_isFlowLineDriver {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) :
    ∀ᵐ ω ∂P, ∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α v ≠ 0 := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := hF
  have hinj := IsIntegratedSLEEvolution.ae_injOn_lt hκ hκ4 hC.1
  filter_upwards [hinj] with ω hω α hα v hv hvζ hαv
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζα ω := lt_of_le_of_lt bot_le hvζ
  exact hv.ne' (hω α hα hvζ h0 (hαv.trans hα.1.symm))

/-! ### GB6's retained chart for a frozen flow driver -/

section Sample

variable {wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α : ℝ≥0 → ℂ} {s : ℝ≥0}

/-- **GB6's retained chart for the frozen flow driver** (deterministic). Let `α` be a generating trace of the flow
driver `wα` (continuous before `Tα`, from `0`), `0 < s < Tα`, and let `α` not vanish on `(0, s]`. Then for some
`t₂ ∈ (s, Tα)` the flow driver frozen after `t₂` is a continuous driver `U` from `0` with a global Loewner trace `αr`,
both agreeing with the flow on `[0, t₂]`, and `(relMap U s, relInv U s, relLog U s)` is a retained chart of
`invHull U s` landing off `relBad U s`. -/
theorem exists_frozen_retainedChartOff (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hs0 : 0 < s)
    (hNR : ∀ v : ℝ≥0, 0 < v → v ≤ s → α v ≠ 0) :
    ∃ (U : ℝ → ℝ) (αr : ℝ → ℂ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ ENNReal.ofReal t₂ < Tα ∧ Continuous U ∧ U 0 = 0 ∧
      IsLoewnerTrace U αr ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal) ∧
      (∀ r ∈ Icc (0 : ℝ) t₂, αr r = α r.toNNReal) ∧
      IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s) := by
  obtain ⟨t₃, hst₃, ht₃⟩ := exists_real_btwn_of_lt hs
  set t₂ : ℝ := ((s : ℝ) + t₃) / 2 with ht₂def
  have hst₂ : (s : ℝ) < t₂ := by rw [ht₂def]; linarith
  have ht₂₃ : t₂ < t₃ := by rw [ht₂def]; linarith
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg s).trans hst₂.le
  have ht₃0 : 0 ≤ t₃ := ht₂0.trans ht₂₃.le
  have ht₂T : ENNReal.ofReal t₂ < Tα := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht₂₃.le) ht₃
  set W₃ : ℝ → ℝ := frozenDrive wα t₃ with hW₃
  have hW₃c : Continuous W₃ := continuous_frozenDrive_of_lt hwα ht₃
  have hW₃0 : W₃ 0 = 0 := by rw [hW₃, frozenDrive_zero ht₃0, hwα0]
  have hLT := hα.isLoewnerTraceLT ht₃
  have hext := hLT.isLoewnerTrace_ext hW₃c hW₃0 ht₂0 ht₂₃
  set U : ℝ → ℝ := extDrive W₃ t₂ with hUdef
  set αr : ℝ → ℂ := extTrace W₃ (fun r : ℝ => α r.toNNReal) t₂ with hαrdef
  have hU : Continuous U := YuanCorollary13.continuous_extDrive hW₃c
  have hU0 : U 0 = 0 := YuanCorollary13.extDrive_zero hW₃0 ht₂0
  have hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal := fun r hr => by
    rw [hUdef, YuanCorollary13.extDrive_eq hr.2, hW₃, frozenDrive_eq ⟨hr.1, hr.2.trans ht₂₃.le⟩]
  have hαeq : ∀ r ∈ Icc (0 : ℝ) t₂, αr r = α r.toNNReal := fun r hr => by
    rw [hαrdef, YuanCorollary13.extTrace_eq hr.2]
  have hNR' : ∀ v ∈ Ioc (0 : ℝ) s, αr v ≠ 0 := fun v hv => by
    rw [hαeq v ⟨hv.1.le, hv.2.trans hst₂.le⟩]
    refine hNR v.toNNReal (Real.toNNReal_pos.2 hv.1) ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hv.1.le]
    exact hv.2
  refine ⟨U, αr, t₂, hst₂, ht₂T, hU, hU0, hext, hUeq, hαeq, ?_⟩
  exact Q3Rel.isRetainedChartOff_relMap hU hU0 hext (by exact_mod_cast hs0) hNR'

end Sample

/-! ### Almost surely on GB6's interior-tip event -/

/-- **GB6's retained chart for the actual flow, almost surely** (`0 < κ < 4`). For a flow-line driver `Wα` with
generating traces `α`, almost surely on the interior-tip event `{s < ζα, α(s) ∈ ℍ}` there is a frozen flow driver `U`
(continuous, from `0`, with a global Loewner trace, agreeing with the flow driver on `[0, t₂]` for some `t₂ > s`, so
with the same relative map and clock) whose relative map is an `IsRetainedChartOff` of `invHull U s` landing off
`relBad U s`. -/
theorem ae_exists_frozen_retainedChartOff {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∃ (U : ℝ → ℝ) (αr : ℝ → ℂ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ ENNReal.ofReal t₂ < ζα ω ∧ Continuous U ∧ U 0 = 0 ∧
        IsLoewnerTrace U αr ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω) ∧
        (∀ r ∈ Icc (0 : ℝ) t₂, αr r = α ω r.toNNReal) ∧
        IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s) := by
  filter_upwards [GB6.ae_driver_zero_continuousOn hF, hα, ae_trace_ne_zero_of_isFlowLineDriver hκ hκ4 hF]
    with ω hω hαω hNR hs hsH
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · exfalso
      exact GB6.ne_zero_of_mem_H hsH (by rw [← h0]; exact hαω.1)
    · exact h0
  exact exists_frozen_retainedChartOff hαω hω.2 hω.1 hs hs0 fun v hv hvs =>
    hNR (α ω) hαω v hv (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hvs) hs)

end InteractingSLE.Supp8.Q3Kernel
