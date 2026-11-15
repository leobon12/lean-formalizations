/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseConst

/-!
# GW4: one event for constancy on the whole positive lifetime

The existing lattice constancy theorem supplies the deterministic argument.
Here fixed-time almost-sure lattice statements are intersected only on a
countable dense set, giving the simultaneous quantifiers of MART's RepD.
The phase at zero and an empty positive lifetime are unrestricted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix

/-- Continuity and fixed-positive-time quantization give one constant lattice
value on the entire positive lifetime, on one event. No positive-lifetime or
time-zero lattice assumption is needed. -/
theorem ae_exists_lattice_const_of_continuousOn {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {step : ℝ} (hstep : step ≠ 0)
    {V : Ω → ℝ≥0∞} {d : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂ν, ContinuousOn (d · ω) {q : ℝ≥0 | 0 < q ∧ (q : ℝ≥0∞) < V ω})
    (hlat : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂ν,
      (q : ℝ≥0∞) < V ω → ∃ j : ℤ, d q ω = j * step) :
    ∀ᵐ ω ∂ν, ∃ c : ℝ, (∃ j : ℤ, c = j * step) ∧
      ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → d q ω = c := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hDlat : ∀ᵐ ω ∂ν, ∀ q : D, 0 < (q : ℝ≥0) →
      ((q : ℝ≥0) : ℝ≥0∞) < V ω → ∃ j : ℤ, d q ω = j * step := by
    apply ae_all_iff.2
    intro q
    by_cases hq : 0 < (q : ℝ≥0)
    · exact (hlat q hq).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hcont, hDlat] with ω hc hl
  let I : Set ℝ≥0 := {q | 0 < q ∧ (q : ℝ≥0∞) < V ω}
  have hIo : IsOpen I := isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_coe continuous_const)
  by_cases hI : I.Nonempty
  · obtain ⟨r, hrD, hrI⟩ := hDd.exists_mem_open hIo hI
    refine ⟨d r ω, hl ⟨r, hrD⟩ hrI.1 hrI.2, fun q hq hqV => ?_⟩
    let f : ℝ≥0 → ℝ := fun p => if p = 0 then 0 else d p ω
    have hfc : ContinuousOn f I := hc.congr fun p hp => by
      simp only [f, ne_of_gt hp.1, ite_false]
    have hfl : ∀ p ∈ D, (p : ℝ≥0∞) < V ω → ∃ j : ℤ, f p = j * step := by
      intro p hp hpV
      by_cases hp0 : p = 0
      · exact ⟨0, by simp only [f, hp0, ite_true, Int.cast_zero, zero_mul]⟩
      · simpa only [f, hp0, ite_false] using hl ⟨p, hp⟩ (pos_iff_ne_zero.2 hp0) hpV
    have he := Sec7.PhaseClause.eq_of_continuousOn_lattice hstep hDd hfc hfl
      (s := q) (t := r) ⟨hq, hqV⟩ hrI
    simpa only [f, ne_of_gt hq, ne_of_gt hrI.1, ite_false] using he
  · refine ⟨0, ⟨0, by rw [Int.cast_zero, zero_mul]⟩, fun q hq hqV => ?_⟩
    exact (hI ⟨q, hq, hqV⟩).elim

end InteractingSLE.Theorem14.GW4Fix
