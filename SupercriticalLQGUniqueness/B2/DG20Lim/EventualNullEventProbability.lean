import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodEventualCompare
import LQGMetric.Papers.DFGPS.L2_17CoreRc

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem tendsto_measure_of_ae_eventually_notMem_null
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : ℕ → Set Ω}
    (hE : ∀ n, NullMeasurableSet (E n) P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ E n) :
    Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
  set F : ℕ → Set Ω := fun n => ⋃ m ≥ n, E m
  have hF : ∀ n, NullMeasurableSet (F n) P := fun n =>
    NullMeasurableSet.biUnion (to_countable _) fun m _ => hE m
  have hanti : Antitone F := fun n n' hnn' => biUnion_subset_biUnion_left fun m hm =>
    le_trans hnn' hm
  have h0 : P (⋂ n, F n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    simp only [F, mem_iInter, mem_iUnion, not_forall, not_exists]
    exact ⟨N, fun m hm => hN m hm⟩
  have hlim := tendsto_measure_iInter_atTop hF hanti ⟨0, measure_ne_top _ _⟩
  rw [h0] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun n => measure_mono (subset_biUnion_of_mem (u := E) (le_refl n))

 

theorem eventually_measure_le_of_ae_eventually_imp_null
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : ℕ → Set Ω}
    (hA : ∀ n, NullMeasurableSet (A n) P)
    (hB : ∀ n, NullMeasurableSet (B n) P)
    (himp : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n → ω ∈ B n)
    {b η : ℝ≥0∞} (hη : 0 < η)
    (hbound : ∀ᶠ n in atTop, P (B n) ≤ b) :
    ∀ᶠ n in atTop, P (A n) ≤ b + η := by
  let E : ℕ → Set Ω := fun n => A n \ B n
  have hE : ∀ n, NullMeasurableSet (E n) P := fun n => (hA n).diff (hB n)
  have hevent : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ E n := by
    filter_upwards [himp] with ω hω
    filter_upwards [hω] with n hn
    exact fun hEω => hEω.2 (hn hEω.1)
  have hlim := tendsto_measure_of_ae_eventually_notMem_null hE hevent
  filter_upwards [hbound, hlim.eventually (gt_mem_nhds hη)] with n hBn hEn
  have hsub : A n ⊆ B n ∪ E n := by
    intro ω hω
    by_cases hωB : ω ∈ B n
    · exact Or.inl hωB
    · exact Or.inr ⟨hω, hωB⟩
  calc
    P (A n) ≤ P (B n ∪ E n) := measure_mono hsub
    _ ≤ P (B n) + P (E n) := measure_union_le _ _
    _ ≤ b + η := add_le_add hBn hEn.le

end SupercriticalLQGUniqueness.B2.DG20Lim
