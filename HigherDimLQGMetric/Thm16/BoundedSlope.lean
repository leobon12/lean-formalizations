import Mathlib.Analysis.SpecificLimits.Basic

/-! A convergent average slope lies between eventual bounds on successive differences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology

namespace HigherDimLQGMetric

theorem l9c_limit_slope_of_bounded_steps {b : ℕ → ℝ} {lam low high : ℝ}
    (hb : Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 lam))
    (hstep : ∀ᶠ n : ℕ in atTop,
      low ≤ b (n + 1) - b n ∧ b (n + 1) - b n ≤ high) :
    low ≤ lam ∧ lam ≤ high := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hstep
  have hupper (k : ℕ) : b (N + k) ≤ b N + (k : ℝ) * high := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := (hN (N + k) (by omega)).2
      push_cast
      simp only [Nat.add_succ] at hs ⊢
      linarith
  have hlower (k : ℕ) : b N + (k : ℝ) * low ≤ b (N + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := (hN (N + k) (by omega)).1
      simp only [Nat.add_succ] at hs ⊢
      push_cast at hs ⊢
      linarith
  have htend (C : ℝ) : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlowT : Tendsto (fun n : ℕ => low + (b N - (N : ℝ) * low) / n)
      atTop (𝓝 low) := by
    simpa using (tendsto_const_nhds.add (htend (b N - (N : ℝ) * low)))
  have hhighT : Tendsto (fun n : ℕ => high + (b N - (N : ℝ) * high) / n)
      atTop (𝓝 high) := by
    simpa using (tendsto_const_nhds.add (htend (b N - (N : ℝ) * high)))
  have hlowEv : (fun n : ℕ => low + (b N - (N : ℝ) * low) / n) ≤ᶠ[atTop]
      (fun n : ℕ => b n / n) := by
    filter_upwards [Filter.Ici_mem_atTop (max N 1)] with n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
    have hsub : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by norm_cast
    have hbound := hlower (n - N)
    rw [Nat.add_sub_of_le hnN, hsub] at hbound
    apply (le_div_iff₀ hnpos).2
    field_simp
    nlinarith
  have hhighEv : (fun n : ℕ => b n / n) ≤ᶠ[atTop]
      (fun n : ℕ => high + (b N - (N : ℝ) * high) / n) := by
    filter_upwards [Filter.Ici_mem_atTop (max N 1)] with n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
    have hsub : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by norm_cast
    have hbound := hupper (n - N)
    rw [Nat.add_sub_of_le hnN, hsub] at hbound
    apply (div_le_iff₀ hnpos).2
    field_simp
    nlinarith
  exact ⟨le_of_tendsto_of_tendsto hlowT hb hlowEv,
    le_of_tendsto_of_tendsto hb hhighT hhighEv⟩

end HigherDimLQGMetric
