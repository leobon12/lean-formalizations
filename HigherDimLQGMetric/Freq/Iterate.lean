import HigherDimLQGMetric.Freq.Step

/-!
# Finite iteration of replacement steps

An advancing step of uniform positive time increment must cross a target time
after finitely many applications. The metric triangle inequality sums the
improved ratio on the processed interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The deterministic telescoping core of Proposition 5.4. -/
theorem s4c_iterate (E : ContMetric d) (P : ℝ → Rd d)
    {L a₀ b₀ δ K : ℝ} (hab : a₀ ≤ b₀) (hbL : b₀ ≤ L)
    (hδ : 0 < δ)
    (hstep : ∀ a ∈ Ico a₀ b₀, ∃ e ∈ Ioc a L,
      δ ≤ e - a ∧ E.1 (P a, P e) ≤ K * (e - a)) :
    ∃ e ∈ Icc b₀ L, E.1 (P a₀, P e) ≤ K * (e - a₀) := by
  have hmain : ∀ n : ℕ, ∀ a ∈ Icc a₀ b₀, b₀ - a ≤ (n : ℝ) * δ →
      ∃ e ∈ Icc b₀ L, E.1 (P a, P e) ≤ K * (e - a) := by
    intro n
    induction n with
    | zero =>
      intro a ha hn
      have heq : a = b₀ := by
        simp only [Nat.cast_zero, zero_mul] at hn
        linarith [ha.2]
      refine ⟨b₀, ⟨le_rfl, hbL⟩, ?_⟩
      rw [heq, sub_self, mul_zero, E.2.self_eq_zero]
    | succ n ih =>
      intro a ha hn
      by_cases hae : a = b₀
      · refine ⟨b₀, ⟨le_rfl, hbL⟩, ?_⟩
        rw [hae, sub_self, mul_zero, E.2.self_eq_zero]
      have halt : a < b₀ := lt_of_le_of_ne ha.2 hae
      obtain ⟨e, he, hadvance, hEae⟩ := hstep a ⟨ha.1, halt⟩
      by_cases hstop : b₀ ≤ e
      · exact ⟨e, ⟨hstop, he.2⟩, hEae⟩
      have heI : e ∈ Icc a₀ b₀ := ⟨ha.1.trans he.1.le, le_of_not_ge hstop⟩
      have hremain : b₀ - e ≤ (n : ℝ) * δ := by
        push_cast at hn
        nlinarith only [hn, hadvance]
      obtain ⟨f, hf, hEef⟩ := ih e heI hremain
      refine ⟨f, hf, ?_⟩
      have htri := E.2.triangle (P a) (P e) (P f)
      calc
        E.1 (P a, P f) ≤ E.1 (P a, P e) + E.1 (P e, P f) := htri
        _ ≤ K * (e - a) + K * (f - e) := add_le_add hEae hEef
        _ = K * (f - a) := by ring
  obtain ⟨n, hn⟩ := exists_nat_ge ((b₀ - a₀) / δ)
  exact hmain n a₀ ⟨le_rfl, hab⟩ (by
    rw [div_le_iff₀ hδ] at hn
    simpa only [mul_comm] using hn)

/-- Uniform continuity turns Euclidean progress along a compact path into a
uniform positive time increment. This avoids taking a minimum over shell
centers in the iteration. -/
theorem s4c_time_advance_of_spatial (P : ℝ → Rd d) {L η : ℝ}
    (hPc : ContinuousOn P (Icc 0 L)) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (0 : ℝ) L, ∀ e ∈ Icc (0 : ℝ) L,
      a ≤ e → η ≤ ‖P e - P a‖ → δ ≤ e - a := by
  have huc : UniformContinuousOn P (Icc 0 L) :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) L)).uniformContinuousOn_of_continuous hPc
  obtain ⟨δ, hδ, hsmall⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  refine ⟨δ, hδ, ?_⟩
  intro a ha e he hae hmove
  by_contra hbad
  have hdist : dist a e < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hae)]
    exact lt_of_not_ge hbad
  have hPdist := hsmall a ha e he hdist
  rw [dist_eq_norm] at hPdist
  have hsym : ‖P a - P e‖ = ‖P e - P a‖ := norm_sub_rev _ _
  rw [hsym] at hPdist
  exact not_lt_of_ge hmove hPdist

end HigherDimLQGMetric
