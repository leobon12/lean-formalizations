import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.ExcursionScale




 


set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling

theorem normalizer_addConst (ξ Q r a c : ℝ) :
    ENNReal.ofReal (r ^ (ξ * Q) * Real.exp (ξ * (a + c))) =
      ENNReal.ofReal (Real.exp (ξ * c)) *
        ENNReal.ofReal (r ^ (ξ * Q) * Real.exp (ξ * a)) := by
  rw [mul_add, Real.exp_add]
  have hreal : r ^ (ξ * Q) * (Real.exp (ξ * a) * Real.exp (ξ * c)) =
      Real.exp (ξ * c) * (r ^ (ξ * Q) * Real.exp (ξ * a)) := by ring
  rw [hreal, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem errorTerm_addConst (ξ Q q b a c : ℝ) :
    ENNReal.ofReal (q * b ^ (ξ * Q) * Real.exp (ξ * (a + c))) =
      ENNReal.ofReal (Real.exp (ξ * c)) *
        ENNReal.ofReal (q * b ^ (ξ * Q) * Real.exp (ξ * a)) := by
  rw [mul_add, Real.exp_add]
  have hreal : q * b ^ (ξ * Q) * (Real.exp (ξ * a) * Real.exp (ξ * c)) =
      Real.exp (ξ * c) * (q * b ^ (ξ * Q) * Real.exp (ξ * a)) := by ring
  rw [hreal, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem localSizeBin_addConst
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (r b q : Set.Ioi (0 : ℝ)) (hrz hbr c : ℝ)
    (hbin : EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q hrz hbr) :
    EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q (hrz + c) (hbr + c) := by
  change _ ∧ _ at hbin
  change _ ∧ _
  have hk : 0 ≤ Real.exp ((ξ : ℝ) * c) := (Real.exp_pos _).le
  have h1 := mul_le_mul_of_nonneg_right hbin.1 hk
  have h2 := mul_le_mul_of_nonneg_right hbin.2 hk
  constructor
  · simpa only [mul_add, Real.exp_add, mul_assoc] using h1
  · simpa only [mul_add, Real.exp_add, mul_assoc] using h2

theorem localSizeBin_addConst_iff
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (r b q : Set.Ioi (0 : ℝ)) (hrz hbr c : ℝ) :
    EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q (hrz + c) (hbr + c) ↔
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q hrz hbr := by
  constructor
  · intro h
    have h' := localSizeBin_addConst ξ Q r b q
      (hrz + c) (hbr + c) (-c) h
    simpa only [add_assoc, add_neg_cancel, add_zero] using h'
  · exact localSizeBin_addConst ξ Q r b q hrz hbr c

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
