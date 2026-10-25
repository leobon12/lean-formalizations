import Mathlib

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos

private theorem tendsto_complement_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n))
    (h : Tendsto (fun n => P (A n)) atTop (𝓝 1)) :
    Tendsto (fun n => P (A n)ᶜ) atTop (𝓝 0) := by
  have hpair : Tendsto (fun n : ℕ => ((1 : ENNReal), P (A n)))
      atTop (𝓝 ((1 : ENNReal), (1 : ENNReal))) := by
    simpa only [nhds_prod_eq] using
      (show Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1)
        from tendsto_const_nhds).prodMk h
  have hsub : Tendsto (fun n : ℕ => (1 : ENNReal) - P (A n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, tsub_self] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  apply hsub.congr'
  filter_upwards [] with n
  have hfin : P (A n) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one)
  have hc := measure_compl (hA n) hfin
  rw [show P Set.univ = (1 : ENNReal) from measure_univ] at hc
  exact hc.symm

theorem probability_inter_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n))
    (hB : ∀ n, MeasurableSet (B n))
    (ha : Tendsto (fun n => P (A n)) atTop (𝓝 1))
    (hb : Tendsto (fun n => P (B n)) atTop (𝓝 1)) :
    Tendsto (fun n => P (A n ∩ B n)) atTop (𝓝 1) := by
  have hac := tendsto_complement_zero P A hA ha
  have hbc := tendsto_complement_zero P B hB hb
  have hbad : Tendsto (fun n => P (A n ∩ B n)ᶜ) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => P (A n)ᶜ + P (B n)ᶜ)
        atTop (𝓝 0) := by simpa only [zero_add] using hac.add hbc
    apply Filter.Tendsto.squeeze' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [] with n
    rw [compl_inter]
    exact measure_union_le _ _
  have hpair : Tendsto (fun n : ℕ => ((1 : ENNReal), P (A n ∩ B n)ᶜ))
      atTop (𝓝 ((1 : ENNReal), (0 : ENNReal))) := by
    simpa only [nhds_prod_eq] using
      (show Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (𝓝 1)
        from tendsto_const_nhds).prodMk hbad
  have hsub : Tendsto (fun n : ℕ => (1 : ENNReal) - P (A n ∩ B n)ᶜ)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, tsub_zero] using
      (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp hpair
  apply hsub.congr'
  filter_upwards [] with n
  have hm : MeasurableSet (A n ∩ B n)ᶜ := (hA n |>.inter (hB n)).compl
  have hfin : P (A n ∩ B n)ᶜ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one)
  have hc := measure_compl hm hfin
  rw [show P Set.univ = (1 : ENNReal) from measure_univ] at hc
  simpa only [compl_compl] using hc.symm

end SupercriticalLQGUniqueness.B2.QPos
