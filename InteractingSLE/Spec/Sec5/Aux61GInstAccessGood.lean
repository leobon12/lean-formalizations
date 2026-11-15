/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessPath

/-! # Path facts for the selected-access completion -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal Classical
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData Restart

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E c ρ T V)

include hs hV hV0 hland

/-- Completing the chosen access preserves simplicity and the first window exit. -/
theorem accessExitPath_facts
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) {x : X}
    (hx : x ∈ exitEv E c ρ T V) :
    let γ := accessExitPath E c ρ T V x
    let e := exitNN E c ρ T V x
    ContinuousOn γ (Iic e) ∧ γ 0 = 0 ∧ InjOn γ (Iic e) ∧
      (∀ r : ℝ≥0, 0 < r → r < e → γ r ∈ H) ∧ γ e ∈ Hbar ∧
      (∀ r : ℝ≥0, r < e → γ r ∈ V) ∧ γ e ∉ V := by
  intro γ e
  have heT : (e : ℝ≥0∞) ≤ T x := IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x
  have hlt : ∀ r : ℝ≥0, r < e → (r : ℝ≥0∞) < T x :=
    fun r hr => (ENNReal.coe_lt_coe.2 hr).trans_le heT
  have hint : ∀ r : ℝ≥0, r < e → γ r = inPath E c ρ T x r :=
    fun r hr => by
      change r < exitNN E c ρ T V x at hr
      simp [γ, accessExitPath, hx, hr]
  have hin : ∀ r : ℝ≥0, r < e → γ r ∈ V := fun r hr => by
    rw [hint r hr]
    exact (IsRestartSpec.lt_exitTime
      (by rw [← IsRestartSpec.coe_exitNN hx]; exact ENNReal.coe_lt_coe.2 hr)).2
  have hout : γ e ∉ V := by
    simpa [γ, e, accessExitPath, hx] using (accessExitPoint_spec hs hV hV0 hland hx).1
  have hfwd : ∀ r : ℝ≥0, 0 < r → r < e → γ r = (c x).1 (ρ x r) :=
    fun r hr0 hr => (hint r hr).trans (hs.inPath_eq_fwd hx.1.1 hr0 (hlt r hr))
  have hH : ∀ r : ℝ≥0, 0 < r → r < e → γ r ∈ H := fun r hr0 hr => by
    rw [hfwd r hr0 hr]
    exact (hs.conf x hx.1.1).fwd_mem (hs.inside x hx.1.1 r hr0 (hlt r hr))
  have hc := continuousOn_accessExitPath hs hV hV0 hland hx
  have hz : γ 0 = 0 := accessExitPath_zero hs hV hV0 hx
  refine ⟨hc, hz, ?_, hH, ?_, hin, hout⟩
  · intro u hu v hv huv
    rcases lt_or_eq_of_le (mem_Iic.1 hu) with hue | hue <;>
      rcases lt_or_eq_of_le (mem_Iic.1 hv) with hve | hve
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0 <;>
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ v) with hv0 | hv0
      · rw [← hu0, ← hv0]
      · rw [← hu0, hz] at huv
        exact absurd (huv ▸ hH v hv0 hve : (0 : ℂ) ∈ H) (by simp [QuantumZipper.H])
      · rw [← hv0, hz] at huv
        exact absurd (huv.symm ▸ hH u hu0 hue : (0 : ℂ) ∈ H) (by simp [QuantumZipper.H])
      · rw [hfwd u hu0 hue, hfwd v hv0 hve] at huv
        have hρ : ρ x u = ρ x v := by
          rw [← (hs.conf x hx.1.1).inv_fwd (hs.inside x hx.1.1 u hu0 (hlt u hue)),
            ← (hs.conf x hx.1.1).inv_fwd (hs.inside x hx.1.1 v hv0 (hlt v hve)), huv]
        exact hinj x hx.1.1 (hlt u hue) (hlt v hve) hρ
    · exact absurd (huv ▸ hin u hue) (hve ▸ hout)
    · exact absurd (huv.symm ▸ hin v hve) (hue ▸ hout)
    · rw [hue, hve]
  · have hepos : 0 < e := exitNN_pos hs hV hV0 hx
    have hcw : ContinuousWithinAt γ (Iic e) e := hc e (mem_Iic.2 le_rfl)
    have := nhdsLT_neBot_of_exists_lt ⟨0, hepos⟩
    have hl : Tendsto γ (𝓝[<] e) (𝓝 (γ e)) :=
      hcw.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
    refine closure_H ▸ mem_closure_of_tendsto hl ?_
    filter_upwards [Ioo_mem_nhdsLT hepos] with r hr
    exact hH r hr.1 hr.2

theorem isClockOn_accessExitPath
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) :
    ∀ x ∈ exitEv E c ρ T V,
      IsClockOn (chartClock (accessExitPath E c ρ T V x)) (exitNN E c ρ T V x) := by
  intro x hx
  obtain ⟨hc, h0, hi, hH, hUH, -, -⟩ := accessExitPath_facts hs hV hV0 hland hinj hx
  exact (isClockOn_chartClock_of_injOn hc hi h0 hH hUH).1

end InteractingSLE.Sec5.Aux61GInst
