/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Cap

/-!
# The concrete closed inverse-clock cut identity

The relative clock is already clamped after its physical lifetime. Its
nondecreasing extension and strict increase on the live interval give the
closed cut identity even at, or after, a finite terminal time.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb

/-- A nondecreasing clock extension reads each inverse cut on the whole
physical time axis. Only the inverse value must lie in the clock interval. -/
theorem invClock_le_iff_capacity_cut {C : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hc : IsClockOn C L) (hm : Monotone fun t => (C t).toNNReal)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ capLife C L) (t : ℝ≥0) :
    invClock C L q ≤ t ↔ q ≤ (C t).toNNReal := by
  obtain ⟨hr, he⟩ := hc.invClock_spec hq
  have heNN : (C (invClock C L q)).toNNReal = q := by rw [he, Real.toNNReal_coe]
  constructor
  · intro h
    exact heNN ▸ hm h
  · intro h
    by_contra hn
    have htr : t < invClock C L q := lt_of_not_ge hn
    have htL : (t : ℝ≥0∞) ≤ L := (ENNReal.coe_le_coe.2 htr.le).trans hr
    have hlt : C t < q := by simpa only [he] using hc.strictMonoOn htL hr htr
    exact not_le_of_gt ((Real.toNNReal_lt_iff_lt_coe (hc.nonneg htL)).2 hlt) h

/-- The actual measurable first-contact clock has exactly the closed
inverse cuts needed by the censored-event construction. The statement also
covers physical times after the continuation has terminated. -/
theorem fcCapacityClock_inverse_cut {Ω : Type*} [MeasurableSpace Ω]
    {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω))
      (d.ζ₁ ω - d.s₀ ω)) {ω : Ω} (hω : ω ∈ E) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) ≤ cLife d E d.s₀ d.η₁ d.ζ₁ ω) (t : ℝ≥0) :
    invClock (cClock d E d.s₀ d.η₁ d.ζ₁ ω) (d.ζ₁ ω - d.s₀ ω) q ≤ t ↔
      q ≤ fcCapacityClock d E t ω := by
  have hc : IsClockOn (cClock d E d.s₀ d.η₁ d.ζ₁ ω) (d.ζ₁ ω - d.s₀ ω) := by
    rw [hs.cClock_eq hd hω]
    exact hclk ω hω
  have hq' : (q : ℝ≥0∞) ≤ capLife (cClock d E d.s₀ d.η₁ d.ζ₁ ω)
      (d.ζ₁ ω - d.s₀ ω) := by
    simpa only [cLife, ite_eq_left hω] using hq
  exact invClock_le_iff_capacity_cut hc (monotone_fcCapacityClock hd hs hclk ω) hq' t

end InteractingSLE.Restart.FCPlumb
