/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeESource
import InteractingSLE.Spec.Restart.ClockInv

/-!
# Continuity of a trace reconstructed through an open lifetime clock

On each compact physical prefix the existing inverse-clock theorem applies.
Cofinal clock coverage then gives continuity of the reconstructed physical
trace at every live capacity time, without a terminal extension assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.GaugeE

/-- Read-back through a compact clock is continuous throughout its capacity
range. The clock inversion itself is reused from the restart API. -/
theorem continuousOn_compactReadback {a : ℝ≥0 → ℝ} {T : ℝ≥0}
    (ha : Restart.IsClockOn a (T : ℝ≥0∞)) {γ X : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hread : ∀ t : ℝ≥0, t ≤ T → X (a t).toNNReal = γ t) :
    ContinuousOn X {u | (u : ℝ≥0∞) ≤ Restart.capLife a T} := by
  have hc : ContinuousOn (fun u => γ (Restart.invClock a T u))
      {u | (u : ℝ≥0∞) ≤ Restart.capLife a T} := hγ.comp_continuousOn ha.continuousOn_invClock
  apply hc.congr
  intro u hu
  obtain ⟨ht, he⟩ := ha.invClock_spec hu
  have hr := hread (Restart.invClock a T u) (ENNReal.coe_le_coe.1 ht)
  rw [he, Real.toNNReal_coe] at hr
  exact hr

/-- A continuous clock, strictly increasing from zero and cofinal in the
live capacity interval, transfers physical trace continuity to that interval. -/
theorem continuousOn_liveReadback {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} (h0 : a 0 = 0)
    (hm : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (hc : ContinuousOn a {t | (t : ℝ≥0∞) < Tc})
    (hrange : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ T : ℝ≥0, (T : ℝ≥0∞) < Tc ∧ (u : ℝ) < a T)
    {γ X : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal = γ t) :
    ContinuousOn X {u | (u : ℝ≥0∞) < L} := by
  intro u hu
  obtain ⟨T, hT, huT⟩ := hrange u hu
  have hclock : Restart.IsClockOn a (T : ℝ≥0∞) :=
    ⟨h0, hm.mono (fun t ht => ht.trans_lt hT), hc.mono (fun t ht => ht.trans_lt hT),
      fun h => (ENNReal.coe_ne_top h).elim⟩
  have hx := continuousOn_compactReadback hclock hγ
    (fun t ht => hread t ((ENNReal.coe_le_coe.2 ht).trans_lt hT))
  have huCap : (u : ℝ≥0∞) < Restart.capLife a T := by
    simp only [Restart.capLife, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.toNNReal_coe]
    rw [← ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.ofReal_lt_iff_lt_toReal u.coe_nonneg ENNReal.ofReal_ne_top).2
    rw [ENNReal.toReal_ofReal (u.coe_nonneg.trans huT.le)]
    exact huT
  have hopen : IsOpen {v : ℝ≥0 | (v : ℝ≥0∞) < Restart.capLife a T} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {v : ℝ≥0 | (v : ℝ≥0∞) ≤ Restart.capLife a T} ∈ 𝓝 u :=
    Filter.mem_of_superset (hopen.mem_nhds huCap) (fun v hv =>
      show (v : ℝ≥0∞) ≤ Restart.capLife a T from le_of_lt hv)
  exact (hx.continuousAt hnhds).continuousWithinAt

end InteractingSLE.Supp8.GB6.GaugeE
