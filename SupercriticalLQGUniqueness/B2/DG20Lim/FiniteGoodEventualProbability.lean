import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodFullTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.EventualNullEventProbability

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def allGoodFail {Ω ι : Type} (E : ℕ → ι → Set Ω) (S : Finset ι) (n : ℕ) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ E n i}

theorem nullMeasurableSet_allGoodFail
    {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → ι → Set Ω) (S : Finset ι)
    (hE : ∀ n i, i ∈ S → NullMeasurableSet (E n i) P) (n : ℕ) :
    NullMeasurableSet (allGoodFail E S n) P := by
  classical
  have hset : allGoodFail E S n = ⋂ i : S, (E n i.1)ᶜ := by
    ext ω
    simp only [allGoodFail, mem_setOf_eq, mem_iInter, mem_compl_iff]
    exact ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩
  rw [hset]
  exact NullMeasurableSet.iInter fun i => (hE n i.1 i.2).compl

theorem eventually_measure_allGoodFail_le_of_ae_eventual_good_imp
    {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A B : ℕ → ι → Set Ω) (S : Finset ι)
    (hA : ∀ n i, i ∈ S → NullMeasurableSet (A n i) P)
    (hB : ∀ n i, i ∈ S → NullMeasurableSet (B n i) P)
    (himp : ∀ i ∈ S, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ A n i → ω ∈ B n i)
    {b η : ℝ≥0∞} (hη : 0 < η)
    (hbound : ∀ᶠ n in atTop, P (allGoodFail A S n) ≤ b) :
    ∀ᶠ n in atTop, P (allGoodFail B S n) ≤ b + η := by
  have hAE : ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ᶠ n in atTop,
      ω ∈ A n i → ω ∈ B n i :=
    (Filter.eventually_all_finset S).2 himp
  have hfin : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ allGoodFail B S n → ω ∈ allGoodFail A S n := by
    filter_upwards [hAE] with ω hω
    have hev : ∀ᶠ n in atTop, ∀ i ∈ S,
        ω ∈ A n i → ω ∈ B n i :=
      (Filter.eventually_all_finset S).2 hω
    filter_upwards [hev] with n hn
    intro hb i hi ha
    exact hb i hi (hn i hi ha)
  exact eventually_measure_le_of_ae_eventually_imp_null
    (fun n => nullMeasurableSet_allGoodFail B S hB n)
    (fun n => nullMeasurableSet_allGoodFail A S hA n)
    hfin hη hbound

end SupercriticalLQGUniqueness.B2.DG20Lim
