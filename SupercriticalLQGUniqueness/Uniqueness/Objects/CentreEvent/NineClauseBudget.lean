import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent.CentreLaw




 







set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent

 

theorem nine_clause_budget {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Fin 9 → Set Ω)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (hfail : ∀ i : Fin 9, P (S i)ᶜ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)) :
    ENNReal.ofReal ((pbar : ℝ) + (1 - (pbar : ℝ)) / 10) ≤ P (⋂ i, S i) := by
  let δ : ℝ := (1 - (pbar : ℝ)) / 10
  have hp : 0 ≤ (pbar : ℝ) := pbar.property.1.le
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith [pbar.property.2]
  have hbad : P (⋂ i, S i)ᶜ ≤ ENNReal.ofReal (9 * δ) := by
    rw [compl_iInter]
    calc
      P (⋃ i, (S i)ᶜ) ≤ ∑ i : Fin 9, P (S i)ᶜ :=
        measure_iUnion_fintype_le P (fun i => (S i)ᶜ)
      _ ≤ ∑ _i : Fin 9, ENNReal.ofReal δ := Finset.sum_le_sum (fun i _ => hfail i)
      _ = ENNReal.ofReal (9 * δ) := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num
  have hsum : ENNReal.ofReal ((pbar : ℝ) + δ) + ENNReal.ofReal (9 * δ) = 1 := by
    rw [← ENNReal.ofReal_add (add_nonneg hp hδ) (mul_nonneg (by norm_num) hδ)]
    have hnum : (pbar : ℝ) + δ + 9 * δ = 1 := by dsimp [δ]; ring
    rw [hnum, ENNReal.ofReal_one]
  have hone : (1 : ℝ≥0∞) ≤ P (⋂ i, S i) + P (⋂ i, S i)ᶜ := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono (union_compl_self _).ge).trans (measure_union_le _ _)
  have hmain : ENNReal.ofReal ((pbar : ℝ) + δ) + ENNReal.ofReal (9 * δ) ≤
      P (⋂ i, S i) + ENNReal.ofReal (9 * δ) := by
    rw [hsum]
    exact hone.trans (add_le_add le_rfl hbad)
  have hfin : ENNReal.ofReal (9 * δ) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.add_le_add_iff_right hfin).1 hmain

end SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent
