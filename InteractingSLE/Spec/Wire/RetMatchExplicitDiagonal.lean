/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchExplicitGrid

/-!
# A summable-error diagonal choice

Continuity of measure from above makes each row's tail error small. Choose one
column in each row with summable error probabilities, then apply the existing
first Borel--Cantelli lemma. No stopping-time lifting theorem is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchExplicit

/-- If each row of measurable error events eventually fails almost surely,
a deterministic diagonal has the same property, with its column at least its row. -/
theorem exists_diagonal_eventually_notMem
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {E : ℕ → ℕ → Set Ω} (hE : ∀ n k, MeasurableSet (E n k))
    (hrow : ∀ n, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ E n k) :
    ∃ j : ℕ → ℕ, (∀ n, n ≤ j n) ∧ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ E n (j n) := by
  let F : ℕ → ℕ → Set Ω := fun n j => ⋃ k ≥ j, E n k
  have hFm : ∀ n j, MeasurableSet (F n j) := fun n j =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hE n k
  have hFa : ∀ n, Antitone (F n) := by
    intro n j k hjk ω hω
    obtain ⟨i, hi, hmem⟩ : ∃ i ≥ k, ω ∈ E n i := by simpa only [F, mem_iUnion, exists_prop] using hω
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hjk.trans hi, hmem⟩⟩
  have hzero : ∀ n, P (⋂ j, F n j) = 0 := by
    intro n
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hrow n] with ω hω
    intro hmem
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    obtain ⟨k, hk, hbad⟩ : ∃ k ≥ N, ω ∈ E n k := by
      simpa only [F, mem_iUnion, exists_prop] using mem_iInter.1 hmem N
    exact hN k hk hbad
  have hex : ∀ n, ∃ j, n ≤ j ∧ P (F n j) < (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    have hc : Tendsto (fun j => P (F n j)) atTop (𝓝 0) := by
      simpa only [hzero n, Function.comp_def] using
        tendsto_measure_iInter_atTop (fun j => (hFm n j).nullMeasurableSet)
          (hFa n) ⟨0, measure_ne_top P _⟩
    have hpos : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n :=
      bot_lt_iff_ne_bot.2 (pow_ne_zero n (by norm_num))
    obtain ⟨j, hj, hn⟩ := ((hc.eventually (Iio_mem_nhds hpos)).and
      (eventually_ge_atTop n)).exists
    exact ⟨j, hn, hj⟩
  choose j hj hsmall using hex
  have hprob : ∀ n, P (E n (j n)) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    exact (measure_mono fun ω hω => mem_iUnion.2
      ⟨j n, mem_iUnion.2 ⟨le_rfl, hω⟩⟩).trans (hsmall n).le
  have hsum : (∑' n, P (E n (j n))) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (2 : ℝ≥0∞) ≠ ⊤ from by norm_num)
    exact (ENNReal.tsum_le_tsum hprob).trans_eq ENNReal.tsum_geometric_two
  exact ⟨j, hj, ae_eventually_notMem hsum⟩

end InteractingSLE.Wire.RetMatchExplicit
