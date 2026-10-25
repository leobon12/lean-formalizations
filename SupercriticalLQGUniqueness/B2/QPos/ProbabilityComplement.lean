import Mathlib

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

theorem upper_tail_zero_of_lower_event_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (a : ℕ → ℝ)
    (hgood : Tendsto (fun n => P {ω | X n ω ≤ a n}) atTop (𝓝 1)) :
    Tendsto (fun n => P {ω | a n < X n ω}) atTop (𝓝 0) := by
  have hpair : Tendsto (fun n : ℕ => ((1 : ENNReal), P {ω | X n ω ≤ a n}))
      atTop (𝓝 ((1 : ENNReal), (1 : ENNReal))) := by
    simpa only [nhds_prod_eq] using
      (show Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1)
        from tendsto_const_nhds).prodMk hgood
  have hsub : Tendsto (fun n : ℕ => (1 : ENNReal) - P {ω | X n ω ≤ a n})
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, tsub_self] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  apply hsub.congr'
  filter_upwards [] with n
  have hm : MeasurableSet {ω | X n ω ≤ a n} := (hX n) measurableSet_Iic
  have hfin : P {ω | X n ω ≤ a n} ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one)
  have hc := measure_compl hm hfin
  rw [show P Set.univ = (1 : ENNReal) from measure_univ] at hc
  have hs : {ω | a n < X n ω} = {ω | X n ω ≤ a n}ᶜ := by ext ω; simp
  rw [hs]
  exact hc.symm

end SupercriticalLQGUniqueness.B2.QPos
