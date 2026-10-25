import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Dyadic
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.P36Swap




 















set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

open LQGMetric (DistC)

 
theorem card_relGoodTilde_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ Q : ℝ) (a : Set.Ioo (3 / 4 : ℝ) 1) (θ C : Set.Ioi (0 : ℝ))
    (p : ℝ) (j : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((TwoScale.S36.relGoodTilde P h D D' ξ Q a θ C p (EndSaving.Interfaces.dyadicRadius j) ε).card : ℝ) ≤
      ((goodDyadic P h D D' ξ Q a C θ p) ∩ Icc (ε ^ 2 * dyad j) (ε * dyad j)).ncard := by
  set S := TwoScale.S36.relGoodTilde P h D D' ξ Q a θ C p (EndSaving.Interfaces.dyadicRadius j) ε with hS
  set f : ℕ → ℝ := fun k => dyad (k + j) with hf
  have hfinj : Function.Injective f := by
    intro k₁ k₂ hk
    simp only [hf] at hk
    rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
    · exact absurd hk (ne_of_gt (dyad_lt_iff.2 (by omega)))
    · exact heq
    · exact absurd hk (ne_of_lt (dyad_lt_iff.2 (by omega)))
  have hsub : f '' (S : Set ℕ) ⊆
      (goodDyadic P h D D' ξ Q a C θ p) ∩ Icc (ε ^ 2 * dyad j) (ε * dyad j) := by
    rintro x ⟨k, hk, rfl⟩
    have hk' := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
    obtain ⟨hgrid, hprob⟩ := hk'
    have hgrid' := (TwoScale.S36.mem_gridIdx_iff hε0 hε1 k).1 hgrid
    have hdk : dyad (k + j) = (8 : ℝ) ^ (-(k : ℤ)) * dyad j := by
      rw [dyad_add]; rfl
    refine ⟨⟨k + j, rfl, ?_⟩, ?_, ?_⟩
    · rw [← TwoScale.S36.relRad_dyadic j k]; exact hprob
    · show ε ^ 2 * dyad j ≤ dyad (k + j)
      rw [hdk]; exact mul_le_mul_of_nonneg_right hgrid'.1 (dyad_pos j).le
    · show dyad (k + j) ≤ ε * dyad j
      rw [hdk]; exact mul_le_mul_of_nonneg_right hgrid'.2 (dyad_pos j).le
  have hfin : ((goodDyadic P h D D' ξ Q a C θ p) ∩ Icc (ε ^ 2 * dyad j) (ε * dyad j)).Finite :=
    finite_dyadic_ge (goodDyadic_subset P h D D' ξ Q a C θ p) (by have := dyad_pos j; positivity)
  have hcard : S.card = (f '' (S : Set ℕ)).ncard := by
    rw [Set.ncard_image_of_injective _ hfinj, Set.ncard_coe_finset]
  have hle := Set.ncard_le_ncard hsub hfin
  rw [hcard]
  exact_mod_cast hle

 

theorem attainedGoodSwapDyadic_of_rel (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (cMinus : ℝ≥0∞) (hm0 : 0 < cMinus) (hmt : cMinus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) :
    AttainedGoodSwapDyadic P h ξ Q D D' cMinus := by
  obtain ⟨θ, a, p, hmain⟩ :=
    TwoScale.S36.attained_good_swap_rel ξ Q hQ D D' hD hD' P h hh cMinus hm0 hmt hMinus
  refine ⟨θ, a, p, fun Cmid hCmid => ?_⟩
  obtain ⟨cMid', hlow, hup, hκ⟩ := hmain ⟨Cmid, hCmid⟩
  refine ⟨cMid'.1, hlow, hup, fun κ _ => ?_⟩
  obtain ⟨ε₀, hε₀⟩ := hκ κ
  refine ⟨ε₀, ε₀.2.1, fun η hη0 hηε j hG => ?_⟩
  have hη1 : η ≤ 1 := hηε.trans ε₀.2.2.le
  have hcount := hε₀ (EndSaving.Interfaces.dyadicRadius j) η hη0 hηε hG
  have hle := card_relGoodTilde_le P h D D' (ξ : ℝ) Q a θ
    ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg hCmid⟩ p j hη0 hη1
  exact hcount.trans hle

 
theorem p364DyadicInput_proved : P364DyadicInput :=
  fun ξ Q hQ D D' hD hD' _ _ P _ h hh cMinus hm0 hmt hMinus =>
    attainedGoodSwapDyadic_of_rel ξ Q hQ D D' hD hD' P h hh cMinus hm0 hmt hMinus

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
