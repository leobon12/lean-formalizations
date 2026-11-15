/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockMeasCap

/-!
# The measurable chart path of a continuation

Packet PROVE-RESTART-CPL5. For measurable pair data `d` (CPL4's `PairData.IsMeasGood`) and a measurable event `E₁`
of first contacts on which a continuation `ρ ω (σ ω + ·)` (`σ` its start, `ζ` its lifetime) has forward chart limits
with unique preimages (`IsContSpec`), the **chart path**

  `cPath ω r = lim_{z → ρ(σ + r), z ∈ D} φ(z)`  (time clamped to `[0, ζ − σ]`; `0` off `E₁`)

is continuous in `r` for every `ω`, measurable in `ω` for every `r`, lies in `ℍ̄`, starts at `0`, and satisfies
`ψ ∘ cPath = ρ(σ + ·)` on the continuation interval.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### Clamped continuation times -/

/-- The continuation time `σ + min(r, ζ − σ)`. -/
def contTime (σ : ℝ≥0) (ζ : ℝ≥0∞) (r : ℝ≥0) : ℝ≥0 := σ + (min (r : ℝ≥0∞) (ζ - σ)).toNNReal

theorem toNNReal_min_coe (r : ℝ≥0) (c : ℝ≥0∞) :
    (min (r : ℝ≥0∞) c).toNNReal = if c = ⊤ then r else min r c.toNNReal := by
  split_ifs with hc
  · rw [hc, min_top_right, ENNReal.toNNReal_coe]
  · rw [← ENNReal.coe_toNNReal hc, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.coe_toNNReal hc]

theorem contTime_of_le {σ r : ℝ≥0} {ζ : ℝ≥0∞} (hr : (r : ℝ≥0∞) ≤ ζ - σ) : contTime σ ζ r = σ + r := by
  rw [contTime, min_eq_left hr, ENNReal.toNNReal_coe]

theorem le_contTime (σ : ℝ≥0) (ζ : ℝ≥0∞) (r : ℝ≥0) : σ ≤ contTime σ ζ r := le_self_add

theorem min_le_sub (σ : ℝ≥0) (ζ : ℝ≥0∞) (r : ℝ≥0) :
    (((min (r : ℝ≥0∞) (ζ - σ)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ - σ := by
  rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
  exact min_le_right _ _

theorem contTime_le {σ : ℝ≥0} {ζ : ℝ≥0∞} (hσ : (σ : ℝ≥0∞) ≤ ζ) (r : ℝ≥0) : (contTime σ ζ r : ℝ≥0∞) ≤ ζ :=
  (coe_le_sub_iff hσ).1 (min_le_sub σ ζ r)

theorem continuous_contTime (σ : ℝ≥0) (ζ : ℝ≥0∞) : Continuous (contTime σ ζ) := by
  unfold contTime
  simp only [toNNReal_min_coe]
  split_ifs
  · exact continuous_const.add continuous_id
  · exact continuous_const.add (continuous_id.min continuous_const)

theorem measurable_contTime {Ω : Type*} [MeasurableSpace Ω] {σ : Ω → ℝ≥0} {ζ : Ω → ℝ≥0∞}
    (hσ : Measurable σ) (hζ : Measurable ζ) (r : ℝ≥0) : Measurable fun ω => contTime (σ ω) (ζ ω) r :=
  hσ.add (ENNReal.measurable_toNNReal.comp (measurable_const.min
    (hζ.sub (measurable_coe_nnreal_ennreal.comp hσ))))

/-- Clamping: `contTime σ ζ r = σ + c r` with `c r = min(r, ζ − σ) ∈ [0, ζ − σ]`. -/
theorem contTime_eq_clamp (σ : ℝ≥0) (ζ : ℝ≥0∞) (r : ℝ≥0) :
    contTime σ ζ r = σ + (min (r : ℝ≥0∞) (ζ - σ)).toNNReal := rfl

/-! ### The specification of a continuation -/

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- **A measurable continuation with chart limits**: on the measurable event `E₁ ⊆ E`, the continuation of `ρ` from
`σ` up to `ζ` is continuous, lies in the closure of the active domain, and every continuation point has a forward
chart limit with a unique `ψ`-preimage in `ℍ̄`; `ψ(0)` is the starting point. -/
structure IsContSpec (d : PairData Ω) (E₁ : Set Ω) (σ : Ω → ℝ≥0) (ρ : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) :
    Prop where
  measurableSet : MeasurableSet E₁
  subset : E₁ ⊆ d.E
  measσ : Measurable σ
  measζ : Measurable ζ
  measρ : ∀ t, Measurable fun ω => ρ ω t
  cont : ∀ ω ∈ E₁, ContinuousOn (ρ ω) {s | (s : ℝ≥0∞) ≤ ζ ω}
  lt : ∀ ω ∈ E₁, (σ ω : ℝ≥0∞) < ζ ω
  mem : ∀ ω ∈ E₁, ∀ s : ℝ≥0, σ ω ≤ s → (s : ℝ≥0∞) ≤ ζ ω → ρ ω s ∈ closure (d.D ω)
  lim : ∀ ω ∈ E₁, ∀ s : ℝ≥0, σ ω ≤ s → (s : ℝ≥0∞) ≤ ζ ω →
    ∃ w ∈ Hbar, Tendsto (d.fwd ω) (𝓝[d.D ω] (ρ ω s)) (𝓝 w) ∧ d.inv ω w = ρ ω s ∧
      ∀ w' ∈ Hbar, d.inv ω w' = ρ ω s → w' = w
  inv0 : ∀ ω ∈ E₁, d.inv ω 0 = ρ ω (σ ω)

/-- **The chart path of the continuation** (time clamped to the continuation interval, `0` off `E₁`). -/
def cPath (d : PairData Ω) (E₁ : Set Ω) (σ : Ω → ℝ≥0) (ρ : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (r : ℝ≥0) : ℂ :=
  open scoped Classical in
  if ω ∈ E₁ then limUnder (𝓝[d.D ω] (ρ ω (contTime (σ ω) (ζ ω) r))) (d.fwd ω) else 0

omit [MeasurableSpace Ω] in
theorem cPath_of_mem {E₁ : Set Ω} {σ : Ω → ℝ≥0} {ρ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ E₁)
    (r : ℝ≥0) :
    cPath d E₁ σ ρ ζ ω r = limUnder (𝓝[d.D ω] (ρ ω (contTime (σ ω) (ζ ω) r))) (d.fwd ω) := by
  simp [cPath, hω]

namespace IsContSpec

variable {E₁ : Set Ω} {σ : Ω → ℝ≥0} {ρ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hs : IsContSpec d E₁ σ ρ ζ)
include hs

/-- The chart path is the unique `ψ`-preimage of the (clamped) continuation point, reached by forward limits. -/
theorem cPath_spec {ω : Ω} (hω : ω ∈ E₁) (r : ℝ≥0) :
    cPath d E₁ σ ρ ζ ω r ∈ Hbar ∧
      Tendsto (d.fwd ω) (𝓝[d.D ω] (ρ ω (contTime (σ ω) (ζ ω) r))) (𝓝 (cPath d E₁ σ ρ ζ ω r)) ∧
      d.inv ω (cPath d E₁ σ ρ ζ ω r) = ρ ω (contTime (σ ω) (ζ ω) r) ∧
      ∀ w' ∈ Hbar, d.inv ω w' = ρ ω (contTime (σ ω) (ζ ω) r) → w' = cPath d E₁ σ ρ ζ ω r := by
  have hle := contTime_le (hs.lt ω hω).le r
  obtain ⟨w, hwH, hwt, hwψ, hwu⟩ := hs.lim ω hω _ (le_contTime _ _ r) hle
  have hne : (𝓝[d.D ω] (ρ ω (contTime (σ ω) (ζ ω) r))).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (hs.mem ω hω _ (le_contTime _ _ r) hle)
  have hw : cPath d E₁ σ ρ ζ ω r = w := by rw [cPath_of_mem hω]; exact hwt.limUnder_eq
  rw [hw]
  exact ⟨hwH, hwt, hwψ, hwu⟩

theorem cPath_zero {ω : Ω} (hω : ω ∈ E₁) : cPath d E₁ σ ρ ζ ω 0 = 0 := by
  obtain ⟨-, -, -, hu⟩ := hs.cPath_spec hω 0
  have h0 : contTime (σ ω) (ζ ω) 0 = σ ω := by
    rw [contTime_of_le (by simp)]; simp
  rw [h0] at hu
  exact (hu 0 (show (0 : ℂ).im ≥ 0 by simp) (hs.inv0 ω hω)).symm

/-- **The chart path is continuous** (for every `ω`). -/
theorem continuous_cPath (hd : d.IsMeasGood) (ω : Ω) : Continuous (cPath d E₁ σ ρ ζ ω) := by
  by_cases hω : ω ∈ E₁
  · obtain ⟨-, hC⟩ := hd.isFirstContactChart (hs.subset hω)
    obtain ⟨-, -, -, -, -, -, -, hψc, -, ⟨M, hM⟩, -⟩ := hC
    set U₀ := ζ ω - σ ω with hU₀
    set T : Set ℝ≥0 := {v | (v : ℝ≥0∞) ≤ U₀} with hT
    have hσζ := (hs.lt ω hω).le
    have hct : ∀ v ∈ T, contTime (σ ω) (ζ ω) v = σ ω + v := fun v hv => contTime_of_le hv
    have hρc : ContinuousOn (fun v => ρ ω (σ ω + v)) T :=
      (hs.cont ω hω).comp (continuous_const.add continuous_id).continuousOn fun v hv =>
        (coe_le_sub_iff hσζ).1 hv
    have hγ : ContinuousOn (cPath d E₁ σ ρ ζ ω) T := by
      refine continuousOn_of_unique_preimage hψc hM hρc (fun v _ => (hs.cPath_spec hω v).1)
        (fun v hv => ?_) (fun v hv w hw hwψ => ?_)
      · rw [(hs.cPath_spec hω v).2.2.1, hct v hv]
      · exact (hs.cPath_spec hω v).2.2.2 w hw (by rw [hct v hv]; exact hwψ)
    -- the chart path only reads the clamped time
    have hclamp : cPath d E₁ σ ρ ζ ω = fun r : ℝ≥0 => cPath d E₁ σ ρ ζ ω (min (r : ℝ≥0∞) U₀).toNNReal := by
      funext r
      rw [cPath_of_mem hω, cPath_of_mem hω, contTime_of_le (min_le_sub (σ ω) (ζ ω) r)]
      rfl
    rw [hclamp]
    have hc : Continuous fun r : ℝ≥0 => (min (r : ℝ≥0∞) U₀).toNNReal := by
      simp only [toNNReal_min_coe]
      split_ifs
      · exact continuous_id
      · exact continuous_id.min continuous_const
    exact hγ.comp_continuous hc fun r => min_le_sub (σ ω) (ζ ω) r
  · have : cPath d E₁ σ ρ ζ ω = fun _ => 0 := by funext r; simp [cPath, hω]
    rw [this]
    exact continuous_const

open scoped Classical in
/-- **The chart path is measurable** in `ω` at every time. -/
theorem measurable_cPath (hd : d.IsMeasGood) (r : ℝ≥0) : Measurable fun ω => cPath d E₁ σ ρ ζ ω r := by
  set D' : Ω → Set ℂ := fun ω => if ω ∈ E₁ then d.D ω else H with hD'
  set f' : Ω → ℂ → ℂ := fun ω => if ω ∈ E₁ then d.fwd ω else id with hf'
  set q' : Ω → ℂ := fun ω => if ω ∈ E₁ then ρ ω (contTime (σ ω) (ζ ω) r) else 0 with hq'
  have hDo : ∀ ω, IsOpen (D' ω) := fun ω => by
    simp only [hD']; split_ifs
    · exact hd.isOpen_D ω
    · exact QuantumZipper.isOpen_H
  have hDm : ∀ z, MeasurableSet {ω | z ∈ D' ω} := fun z => by
    have : {ω | z ∈ D' ω} = (E₁ ∩ {ω | z ∈ d.D ω}) ∪ (E₁ᶜ ∩ {_ω | z ∈ H}) := by
      ext ω; by_cases hω : ω ∈ E₁ <;> simp [hD', hω]
    rw [this]
    exact (hs.measurableSet.inter (hd.measurableSet_mem_D z)).union
      (hs.measurableSet.compl.inter (MeasurableSet.const _))
  have hfm : ∀ z, Measurable ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) := fun z => by
    have hfwd : Measurable ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) := by
      have : ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) =
          ({ω | z ∈ d.D ω}.indicator fun ω => d.g ω z) - {ω | z ∈ d.D ω}.indicator d.shift := by
        funext ω; by_cases hω : z ∈ d.D ω <;> simp [Set.indicator, hω, PairData.fwd]
      rw [this]
      exact (hd.measurable_indicator_g z).sub (hd.measurable_shift.indicator (hd.measurableSet_mem_D z))
    have : ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) =
        E₁.piecewise ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) (fun _ => if z ∈ H then z else 0) := by
      funext ω; by_cases hω : ω ∈ E₁ <;> by_cases hz : z ∈ H <;> simp [Set.indicator, Set.piecewise, hD', hf', hω, hz]
    rw [this]
    exact hfwd.piecewise hs.measurableSet measurable_const
  have hq : Measurable q' := by
    have := measurable_piecewise_eval hs.measurableSet hs.measρ (measurable_contTime hs.measσ hs.measζ r)
      (fun ω hω => (hs.cont ω hω).mono fun t ht =>
        (ENNReal.coe_le_coe.2 ht).trans (contTime_le (hs.lt ω hω).le r))
    convert this using 1
  have hqD : ∀ ω, q' ω ∈ closure (D' ω) := fun ω => by
    by_cases hω : ω ∈ E₁
    · simp only [hq', hD', hω, ite_true]
      exact hs.mem ω hω _ (le_contTime _ _ r) (contTime_le (hs.lt ω hω).le r)
    · simp only [hq', hD', hω, ite_false]
      rw [closure_H]; show (0 : ℂ).im ≥ 0; simp
  have hlim : ∀ ω, Tendsto (f' ω) (𝓝[D' ω] (q' ω)) (𝓝 (cPath d E₁ σ ρ ζ ω r)) := fun ω => by
    by_cases hω : ω ∈ E₁
    · simp only [hf', hD', hq', hω, ite_true]
      exact (hs.cPath_spec hω r).2.1
    · simp only [hf', hD', hq', hω, ite_false, cPath]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
  exact measurable_of_tendsto_nhdsWithin hDo hDm hfm hq hqD hlim

end IsContSpec

end Restart

end InteractingSLE
