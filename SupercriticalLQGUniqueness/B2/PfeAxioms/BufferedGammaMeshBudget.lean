import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaInnerRecovery

 







set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_uniform_mesh_budget {d r C : ℝ}
    (hd : 0 < d) (hr : 0 < r) (hC : d < C) :
    ∃ (N : ℕ) (q : ℝ), 0 < q ∧
      ∀ L : ℝ, d ≤ L → L < d + q →
        q ≤ L / (N + 1 : ℝ) ∧
        L / (N + 1 : ℝ) < r ∧
        L + 2 * q < C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (d / r)
  have ha : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hgap : d < (N + 1 : ℝ) * r := by
    have hN' : d < (N : ℝ) * r := (div_lt_iff₀ hr).mp hN
    nlinarith
  have hminpos :
      0 < min (d / (N + 1 : ℝ))
        (min ((N + 1 : ℝ) * r - d) ((C - d) / 3)) := by
    apply lt_min
    · exact div_pos hd ha
    · apply lt_min
      · linarith
      · linarith
  obtain ⟨q, hq0, hqmin⟩ := exists_between hminpos
  have hq1 : q < d / (N + 1 : ℝ) :=
    hqmin.trans_le (min_le_left _ _)
  have hq2 : q < (N + 1 : ℝ) * r - d :=
    hqmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hq3 : q < (C - d) / 3 :=
    hqmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨N, q, hq0, ?_⟩
  intro L hdL hL
  have hlow : q ≤ L / (N + 1 : ℝ) := by
    apply le_trans hq1.le
    exact div_le_div_of_nonneg_right hdL ha.le
  have hupp : L / (N + 1 : ℝ) < r := by
    apply (div_lt_iff₀ ha).mpr
    linarith
  refine ⟨hlow, hupp, ?_⟩
  linarith

theorem uniform_mesh_total_lt (N : ℕ) {L q C : ℝ}
    (hL : 0 ≤ L) (hq : 0 < q) (hC : L + 2 * q < C) :
    (N + 1) • ENNReal.ofReal ((L + q) / (N + 1 : ℝ)) +
      N • ENNReal.ofReal (q / (N + 1 : ℝ)) < ENNReal.ofReal C := by
  have ha : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hB : 0 ≤ (L + q) / (N + 1 : ℝ) :=
    div_nonneg (by linarith) ha.le
  have hδ : 0 ≤ q / (N + 1 : ℝ) := div_nonneg hq.le ha.le
  rw [← ENNReal.ofReal_nsmul, ← ENNReal.ofReal_nsmul,
    ← ENNReal.ofReal_add (nsmul_nonneg hB _) (nsmul_nonneg hδ _)]
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr
  rw [nsmul_eq_mul, nsmul_eq_mul]
  have hfirst : (N + 1 : ℝ) * ((L + q) / (N + 1 : ℝ)) = L + q := by
    field_simp
  have hlast : (N + 1 : ℝ) * (q / (N + 1 : ℝ)) = q := by
    field_simp
  have hN : (N : ℝ) ≤ (N + 1 : ℝ) := by exact_mod_cast Nat.le_succ N
  have hsecond : (N : ℝ) * (q / (N + 1 : ℝ)) ≤ q := by
    calc
      _ ≤ (N + 1 : ℝ) * (q / (N + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right hN hδ
      _ = q := hlast
  push_cast
  linarith

end SupercriticalLQGUniqueness.B2.PfeAxioms
