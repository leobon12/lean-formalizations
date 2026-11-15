/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockMeasPath

/-!
# Measurable relative capacity clocks and capacity-time chart paths

Packet PROVE-RESTART-CPL5. For a continuation specification `IsContSpec d E₁ σ ρ ζ` (`ClockMeasPath.lean`):

* `cClock ω r = hcapHit(cPath_ω([0, r])) / 2` on `E₁` (`0` off `E₁`) is measurable in `ω` and equals the relative
  capacity clock `chartClock (cPath ω)` on `E₁` (`IsContSpec.cClock_eq`);
* `cGamma ω u = cPath ω (a_ω⁻¹(u))` and `cLife ω = capLife a_ω (ζ − σ)` are the chart path in relative capacity time
  and its capacity lifetime; given that `chartClock (cPath ω)` is a clock on `[0, ζ − σ]` for `ω ∈ E₁` (proved in
  `ClockAssembly.lean` from Aux. lemma 76), they are measurable and `cGamma ω` is continuous on `[0, cLife ω]`
  (`IsContSpec.clockData`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

open scoped Classical in
/-- The measurable relative capacity clock. -/
def cClock (d : PairData Ω) (E₁ : Set Ω) (σ : Ω → ℝ≥0) (ρ : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (r : ℝ≥0) :
    ℝ :=
  if ω ∈ E₁ then (WholeField.hcapHit (cPath d E₁ σ ρ ζ ω '' Icc 0 r)).toReal / 2 else 0

open scoped Classical in
/-- The chart path in relative capacity time. -/
def cGamma (d : PairData Ω) (E₁ : Set Ω) (σ : Ω → ℝ≥0) (ρ : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (u : ℝ≥0) :
    ℂ :=
  if ω ∈ E₁ then cPath d E₁ σ ρ ζ ω (invClock (cClock d E₁ σ ρ ζ ω) (ζ ω - σ ω) u) else 0

open scoped Classical in
/-- The capacity lifetime of the continuation. -/
def cLife (d : PairData Ω) (E₁ : Set Ω) (σ : Ω → ℝ≥0) (ρ : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  if ω ∈ E₁ then capLife (cClock d E₁ σ ρ ζ ω) (ζ ω - σ ω) else 0

namespace IsContSpec

variable {E₁ : Set Ω} {σ : Ω → ℝ≥0} {ρ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hs : IsContSpec d E₁ σ ρ ζ)
  (hd : d.IsMeasGood)
include hs hd

/-- On `E₁` the measurable clock is the relative capacity clock of the chart path. -/
theorem cClock_eq {ω : Ω} (hω : ω ∈ E₁) : cClock d E₁ σ ρ ζ ω = chartClock (cPath d E₁ σ ρ ζ ω) := by
  funext r
  have hc := (hs.continuous_cPath hd ω).continuousOn (s := Icc 0 r)
  have h0 : (cPath d E₁ σ ρ ζ ω 0).im ≤ 0 := by rw [hs.cPath_zero hω]; simp
  have hF := isHPHull_fillH_image hc h0
  simp only [cClock, hω, ite_true, chartClock]
  rw [hcapHit_image_eq hc h0, ENNReal.toReal_ofReal]
  rw [ConformalImage.hcapSet_eq hF]
  exact HPHull.hcap_nonneg _

theorem measurable_cClock (r : ℝ≥0) : Measurable fun ω => cClock d E₁ σ ρ ζ ω r := by
  classical
  have h := ((measurable_hcapHit_image (hs.continuous_cPath hd) (hs.measurable_cPath hd) r).ennreal_toReal).div_const
    (2 : ℝ)
  exact Measurable.ite hs.measurableSet h measurable_const

theorem measurable_invClock (u : ℝ≥0) :
    Measurable fun ω => invClock (cClock d E₁ σ ρ ζ ω) (ζ ω - σ ω) u := by
  classical
  refine Measurable.iSup fun q => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  refine (MeasurableSet.const _).inter ((measurableSet_le measurable_const
    (hs.measζ.sub (measurable_coe_nnreal_ennreal.comp hs.measσ))).inter ?_)
  exact measurableSet_lt (hs.measurable_cClock hd _) measurable_const

/-- The chart path is jointly measurable (continuous in time, measurable in `ω`). -/
theorem measurable_uncurry_cPath : Measurable fun p : ℝ≥0 × Ω => cPath d E₁ σ ρ ζ p.2 p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun r ω => cPath d E₁ σ ρ ζ ω r)
    (fun ω => hs.continuous_cPath hd ω) (hs.measurable_cPath hd)

theorem measurable_cGamma (u : ℝ≥0) : Measurable fun ω => cGamma d E₁ σ ρ ζ ω u := by
  classical
  have h := (hs.measurable_uncurry_cPath hd).comp ((hs.measurable_invClock hd u).prodMk measurable_id)
  exact Measurable.ite hs.measurableSet h measurable_const

variable (hclk : ∀ ω ∈ E₁, IsClockOn (chartClock (cPath d E₁ σ ρ ζ ω)) (ζ ω - σ ω))
include hclk

omit [MeasurableSpace Ω] hs hd hclk in
/-- The chart path's image is unchanged after the end of the continuation (clamping). -/
theorem image_cPath_clamp {ω : Ω} (hω : ω ∈ E₁) (r : ℝ≥0) :
    cPath d E₁ σ ρ ζ ω '' Icc 0 r = cPath d E₁ σ ρ ζ ω '' Icc 0 (min (r : ℝ≥0∞) (ζ ω - σ ω)).toNNReal := by
  have hcl : ∀ v : ℝ≥0, cPath d E₁ σ ρ ζ ω v = cPath d E₁ σ ρ ζ ω (min (v : ℝ≥0∞) (ζ ω - σ ω)).toNNReal := by
    intro v
    rw [cPath_of_mem hω, cPath_of_mem hω, contTime_of_le (min_le_sub (σ ω) (ζ ω) v)]
    rfl
  have hmono : (min (r : ℝ≥0∞) (ζ ω - σ ω)).toNNReal ≤ r := by
    rw [toNNReal_min_coe]; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨(min (v : ℝ≥0∞) (ζ ω - σ ω)).toNNReal, ⟨zero_le, ?_⟩, (hcl v).symm⟩
    rw [toNNReal_min_coe, toNNReal_min_coe]
    split_ifs
    · exact hv.2
    · exact min_le_min_right _ hv.2
  · exact image_mono (Icc_subset_Icc_right hmono)

/-- The measurable clock is continuous in time for every `ω`. -/
theorem continuous_cClock (ω : Ω) : Continuous (cClock d E₁ σ ρ ζ ω) := by
  by_cases hω : ω ∈ E₁
  · rw [hs.cClock_eq hd hω]
    have h : chartClock (cPath d E₁ σ ρ ζ ω) =
        fun r : ℝ≥0 => chartClock (cPath d E₁ σ ρ ζ ω) (min (r : ℝ≥0∞) (ζ ω - σ ω)).toNNReal := by
      funext r
      simp only [chartClock]
      rw [image_cPath_clamp hω r]
    rw [h]
    have hc : Continuous fun r : ℝ≥0 => (min (r : ℝ≥0∞) (ζ ω - σ ω)).toNNReal := by
      simp only [toNNReal_min_coe]
      split_ifs
      · exact continuous_id
      · exact continuous_id.min continuous_const
    exact (hclk ω hω).continuousOn.comp_continuous hc fun r => min_le_sub (σ ω) (ζ ω) r
  · have : cClock d E₁ σ ρ ζ ω = fun _ => 0 := by funext r; simp [cClock, hω]
    rw [this]
    exact continuous_const

theorem measurable_cLife : Measurable (cLife d E₁ σ ρ ζ) := by
  classical
  have hU : Measurable fun ω => ζ ω - σ ω := hs.measζ.sub (measurable_coe_nnreal_ennreal.comp hs.measσ)
  have hj : Measurable fun p : ℝ≥0 × Ω => cClock d E₁ σ ρ ζ p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun r ω => cClock d E₁ σ ρ ζ ω r)
      (fun ω => hs.continuous_cClock hd hclk ω) (hs.measurable_cClock hd)
  have hv : Measurable fun ω => cClock d E₁ σ ρ ζ ω (ζ ω - σ ω).toNNReal :=
    hj.comp ((ENNReal.measurable_toNNReal.comp hU).prodMk measurable_id)
  have hcap : Measurable fun ω => capLife (cClock d E₁ σ ρ ζ ω) (ζ ω - σ ω) :=
    Measurable.ite (measurableSet_eq_fun hU measurable_const) measurable_const
      (ENNReal.measurable_ofReal.comp hv)
  exact Measurable.ite hs.measurableSet hcap measurable_const

/-- **The capacity-time clock data of one continuation**: `cGamma` and `cLife` are measurable, `cGamma ω` is
continuous on `[0, cLife ω]` for every `ω`, and on `E₁` they are the chart path read through the inverse relative
capacity clock and its capacity lifetime. -/
theorem clockData :
    (∀ u, Measurable fun ω => cGamma d E₁ σ ρ ζ ω u) ∧ Measurable (cLife d E₁ σ ρ ζ) ∧
      (∀ ω, ContinuousOn (cGamma d E₁ σ ρ ζ ω) {u | (u : ℝ≥0∞) ≤ cLife d E₁ σ ρ ζ ω}) ∧
      ∀ ω ∈ E₁, cGamma d E₁ σ ρ ζ ω =
          (fun u => cPath d E₁ σ ρ ζ ω (invClock (chartClock (cPath d E₁ σ ρ ζ ω)) (ζ ω - σ ω) u)) ∧
        cLife d E₁ σ ρ ζ ω = capLife (chartClock (cPath d E₁ σ ρ ζ ω)) (ζ ω - σ ω) := by
  have heq : ∀ ω ∈ E₁, cGamma d E₁ σ ρ ζ ω =
      (fun u => cPath d E₁ σ ρ ζ ω (invClock (chartClock (cPath d E₁ σ ρ ζ ω)) (ζ ω - σ ω) u)) ∧
      cLife d E₁ σ ρ ζ ω = capLife (chartClock (cPath d E₁ σ ρ ζ ω)) (ζ ω - σ ω) := fun ω hω => by
    refine ⟨funext fun u => ?_, ?_⟩
    · simp only [cGamma, hω, ite_true, hs.cClock_eq hd hω]
    · simp only [cLife, hω, ite_true, hs.cClock_eq hd hω]
  refine ⟨hs.measurable_cGamma hd, hs.measurable_cLife hd hclk, fun ω => ?_, heq⟩
  by_cases hω : ω ∈ E₁
  · rw [(heq ω hω).1, (heq ω hω).2]
    exact (hclk ω hω).continuousOn_comp_invClock (hs.continuous_cPath hd ω).continuousOn
  · have : cGamma d E₁ σ ρ ζ ω = fun _ => 0 := by funext u; simp [cGamma, hω]
    rw [this]
    exact continuousOn_const

end IsContSpec

end Restart

end InteractingSLE
