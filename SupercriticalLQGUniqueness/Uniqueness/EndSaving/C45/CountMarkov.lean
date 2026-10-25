import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.CountSum




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

 

theorem outer_measure_le_of_count
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i))
    (G : Set Ω) (N : ℝ≥0∞) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hcover : G ⊆ {ω | N ≤ ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :
    P G ≤ (∑' i, P (A i)) / N := by
  let count : Ω → ℝ≥0∞ :=
    fun ω => ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω
  have hm : Measurable count := by
    exact Measurable.tsum fun i =>
      (measurable_const.indicator (hA i))
  have hc : P G ≤ P {ω | N ≤ count ω} := measure_mono hcover
  calc
    P G ≤ P {ω | N ≤ count ω} := hc
    _ ≤ (∫⁻ ω, count ω ∂P) / N :=
      meas_ge_le_lintegral_div hm.aemeasurable hN0 hNtop
    _ = (∑' i, P (A i)) / N := by
      rw [lintegral_tsum]
      · congr 1
        apply tsum_congr
        intro i
        simp [lintegral_indicator (hA i)]
      · intro i
        exact (measurable_const.indicator (hA i)).aemeasurable

 

theorem tsum_measure_le_of_ratio_and_occupancy
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (M : ℕ) (C : ℝ≥0∞)
    (hocc : ∀ᵐ ω ∂P, ∀ s : Finset ι,
      Set.ncard ((s : Set ι) ∩ {i | ω ∈ B i}) ≤ M)
    (hratio : ∀ i, P (A i) ≤ C * P (B i)) :
    (∑' i, P (A i)) ≤ C * M := by
  calc
    (∑' i, P (A i)) ≤ ∑' i, C * P (B i) :=
      ENNReal.tsum_le_tsum hratio
    _ = C * (∑' i, P (B i)) := ENNReal.tsum_mul_left
    _ ≤ C * M := by
      gcongr
      exact tsum_measure_le_of_ae_finite_occupancy P B hB M hocc

 
theorem outer_measure_le_of_finite_grid_count
    {Ω ι κ : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Finset κ) (A B : κ → ι → Set Ω)
    (hA : ∀ j ∈ J, ∀ i, MeasurableSet (A j i))
    (hB : ∀ j ∈ J, ∀ i, MeasurableSet (B j i))
    (M : ℕ) (C N : ℝ≥0∞) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hocc : ∀ j ∈ J, ∀ᵐ ω ∂P, ∀ s : Finset ι,
      Set.ncard ((s : Set ι) ∩ {i | ω ∈ B j i}) ≤ M)
    (hratio : ∀ j ∈ J, ∀ i, P (A j i) ≤ C * P (B j i))
    (G : Set Ω)
    (hcover : G ⊆ ⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :
    P G ≤ (J.card : ℝ≥0∞) * (C * M / N) := by
  have hbound : ∀ j ∈ J,
      P {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω} ≤
        C * M / N := by
    intro j hj
    have hcount := outer_measure_le_of_count P (A j) (hA j hj)
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}
      N hN0 hNtop (by rfl)
    exact hcount.trans (by
      gcongr
      exact tsum_measure_le_of_ratio_and_occupancy P (A j) (B j)
        (hB j hj) M C (hocc j hj) (hratio j hj))
  calc
    P G ≤ P (⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :=
        measure_mono hcover
    _ ≤ ∑ j ∈ J,
      P {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω} :=
        measure_biUnion_finset_le J _
    _ ≤ ∑ _j ∈ J, C * M / N := Finset.sum_le_sum hbound
    _ = (J.card : ℝ≥0∞) * (C * M / N) := by simp

 

theorem outer_measure_le_of_ae_finite_grid_count
    {Ω ι κ : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Finset κ) (A B : κ → ι → Set Ω)
    (hA : ∀ j ∈ J, ∀ i, MeasurableSet (A j i))
    (hB : ∀ j ∈ J, ∀ i, MeasurableSet (B j i))
    (M : ℕ) (C N : ℝ≥0∞) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hocc : ∀ j ∈ J, ∀ᵐ ω ∂P, ∀ s : Finset ι,
      Set.ncard ((s : Set ι) ∩ {i | ω ∈ B j i}) ≤ M)
    (hratio : ∀ j ∈ J, ∀ i, P (A j i) ≤ C * P (B j i))
    (G : Set Ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ G → ω ∈ ⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :
    P G ≤ (J.card : ℝ≥0∞) * (C * M / N) := by
  have hfirst : P G ≤ P (⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :=
    measure_mono_ae hcover
  exact hfirst.trans <|
    outer_measure_le_of_finite_grid_count P J A B hA hB M C N hN0 hNtop
      hocc hratio _ (Subset.rfl)

 

theorem outer_measure_le_of_ae_finite_grid_budget
    {Ω ι κ : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (J : Finset κ) (A : κ → ι → Set Ω)
    (hA : ∀ j ∈ J, ∀ i, MeasurableSet (A j i))
    (B N : ℝ≥0∞) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hbudget : ∀ j ∈ J, (∑' i, P (A j i)) ≤ B)
    (G : Set Ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ G → ω ∈ ⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :
    P G ≤ (J.card : ℝ≥0∞) * (B / N) := by
  have hfirst : P G ≤ P (⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) :=
    measure_mono_ae hcover
  have hbound : ∀ j ∈ J,
      P {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω} ≤
        B / N := by
    intro j hj
    exact (outer_measure_le_of_count P (A j) (hA j hj) _ N hN0 hNtop
      (Subset.rfl)).trans (by gcongr; exact hbudget j hj)
  calc
    P G ≤ P (⋃ j ∈ J,
      {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω}) := hfirst
    _ ≤ ∑ j ∈ J,
      P {ω | N ≤ ∑' i, (A j i).indicator (fun _ => (1 : ℝ≥0∞)) ω} :=
        measure_biUnion_finset_le J _
    _ ≤ ∑ _j ∈ J, B / N := Finset.sum_le_sum hbound
    _ = (J.card : ℝ≥0∞) * (B / N) := by simp




end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
