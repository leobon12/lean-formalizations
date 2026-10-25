import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.CountWitness
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CorrectedChoices.CorrectedChoicesAS




 
set_option autoImplicit false
noncomputable section
open Set Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

def windowRadii (R : EndSaving.Interfaces.AdmissibleRadii) (ε : ℝ) (b : Set.Ioi (0 : ℝ)) :
    Set (Set.Ioi (0 : ℝ)) :=
  {r | (r : ℝ) ∈ R.radii ∧ ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧
    (r : ℝ) ≤ ε * (b : ℝ)}

theorem windowRadii_finite (R : EndSaving.Interfaces.AdmissibleRadii)
    {ε : ℝ} (hε : 0 < ε) (b : Set.Ioi (0 : ℝ)) :
    (windowRadii R ε b).Finite := by
  let f : Set.Ioi (0 : ℝ) → ℤ := fun r => ⌊Real.logb 8 (r : ℝ)⌋
  have hmaps : f '' windowRadii R ε b ⊆
      (Finset.Icc ⌊Real.logb 8 (ε ^ 2 * (b : ℝ))⌋
        ⌊Real.logb 8 (ε * (b : ℝ))⌋ : Finset ℤ) := by
    intro j hj
    rcases hj with ⟨r, hr, rfl⟩
    exact EndSaving.Choices.floor_logb_mem_box hε b.property hr.2.1 hr.2.2
  apply Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hmaps)
  intro r hr s hs hrs
  apply Subtype.ext
  exact EndSaving.Choices.admissible_floor_injective R hr.1 hs.1 hrs

theorem windowRadii_card_le (R : EndSaving.Interfaces.AdmissibleRadii)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (b : Set.Ioi (0 : ℝ)) :
    ((windowRadii_finite R hε b).toFinset.card : ℝ) ≤
      Real.logb 8 ε⁻¹ + 2 := by
  let s := (windowRadii_finite R hε b).toFinset
  let t : Finset ℤ := Finset.Icc ⌊Real.logb 8 (ε ^ 2 * (b : ℝ))⌋
    ⌊Real.logb 8 (ε * (b : ℝ))⌋
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn
      (fun r : Set.Ioi (0 : ℝ) => ⌊Real.logb 8 (r : ℝ)⌋)
    · intro r hr
      have hr' : r ∈ windowRadii R ε b := by simpa [s] using hr
      exact EndSaving.Choices.floor_logb_mem_box hε b.property hr'.2.1 hr'.2.2
    · intro r hr u hu hru
      have hr' : r ∈ windowRadii R ε b := by simpa [s] using hr
      have hu' : u ∈ windowRadii R ε b := by simpa [s] using hu
      apply Subtype.ext
      exact EndSaving.Choices.admissible_floor_injective R hr'.1 hu'.1 hru
  exact (Nat.cast_le.mpr hcard).trans (EndSaving.Choices.card_floor_box_le hε hε1 b.property)

def windowSizes (ξ Q ε : ℝ) : Finset ℤ :=
  Finset.Icc ⌈Real.logb 2 ((1 / 2) * ε ^ (2 * ξ * (Q + 3)))⌉
    ⌊Real.logb 2 (ε ^ (ξ * min (Q - 3) (2 * (Q - 3))))⌋

theorem dyadic_mem_windowSizes {ξ Q ε : ℝ} (hε : 0 < ε) {ℓ : ℤ}
    (hlo : (1 / 2) * ε ^ (2 * ξ * (Q + 3)) ≤ (2 : ℝ) ^ ℓ)
    (hhi : (2 : ℝ) ^ ℓ ≤ ε ^ (ξ * min (Q - 3) (2 * (Q - 3)))) :
    ℓ ∈ windowSizes ξ Q ε := by
  exact EndSaving.Choices.dyadic_exp_mem_box (by positivity) hlo hhi

def windowGrid (R : EndSaving.Interfaces.AdmissibleRadii) (ξ Q ε : ℝ)
    (hε : 0 < ε) (b : Set.Ioi (0 : ℝ)) :
    Finset (Set.Ioi (0 : ℝ) × ℤ) :=
  (windowRadii_finite R hε b).toFinset ×ˢ windowSizes ξ Q ε

theorem windowGrid_card_le (R : EndSaving.Interfaces.AdmissibleRadii)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (b : Set.Ioi (0 : ℝ)) :
    ((windowGrid R ξ Q ε hε b).card : ℝ) ≤ EndSaving.CorrectedChoices.mBox ξ Q ε := by
  rw [windowGrid, Finset.card_product, Nat.cast_mul]
  unfold EndSaving.CorrectedChoices.mBox
  apply mul_le_mul (windowRadii_card_le R hε hε1 b)
    (EndSaving.Choices.card_dyadic_box_le (by positivity)) (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.logb 8 ε⁻¹ :=
    Real.logb_nonneg (by norm_num) ((one_le_inv₀ hε).mpr hε1)
  linarith

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
