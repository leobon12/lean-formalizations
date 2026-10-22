import HigherDimLQGMetric.Determ.LengthBorel

/-! The conditional variance estimate forces each metric distance to be constant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_const_measure (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ D ∂ν, D.IsLength) (C : ℝ) (hC1 : 1 < C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim,
      p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    (hprod : ∀ n j : ℕ, ∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)),
      ν.map (determY (1 / ((j : ℝ) + 1)) θ
        (determFixedBox (d := dim) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1))) =
      Measure.pi fun k : determFixedBox (d := dim) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1) =>
        ν.map (determ_enc (determCube (1 / ((j : ℝ) + 1)) θ k)))
    (z w : Rd dim) :
    ∀ᵐ D ∂ν, D.1 (z, w) = ∫ E, E.1 (z, w) ∂ν := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max ‖z‖ ‖w‖)
  have hz : ‖z‖ < n₀ := (le_max_left _ _).trans_lt hn₀
  have hw : ‖w‖ < n₀ := (le_max_right _ _).trans_lt hn₀
  obtain ⟨B, hB⟩ := determ_F_bdd ν hL (zero_lt_one.trans hC1) hcopy hz hw
  have hprops : ∀ᵐ D ∂ν,
      (∀ m, 0 ≤ (determF (n₀ + m) z w D).toReal ∧
        (determF (n₀ + m) z w D).toReal ≤ (ENNReal.ofReal B).toReal) ∧
      (∀ m, (determF (n₀ + m + 1) z w D).toReal ≤
        (determF (n₀ + m) z w D).toReal) ∧
      Tendsto (fun m => (determF (n₀ + m) z w D).toReal) atTop (𝓝 (D.1 (z, w))) := by
    filter_upwards [hL, hB] with D hLD hBD
    refine LQGMetric.LM.t17_seq_props (D.nonneg z w) ENNReal.ofReal_ne_top ?_ ?_ ?_
    · intro m
      simpa only [Nat.add_assoc] using determ_chainInf_succ_le hLD (n₀ + m) z w
    · exact determ_iInf_F hLD n₀ z w
    · simpa only [Nat.add_zero] using hBD.1
  have hvar : ∀ m : ℕ,
      ∫ D, ((determF (n₀ + (m + 1)) z w D).toReal -
        ∫ E, (determF (n₀ + (m + 1)) z w E).toReal ∂ν) ^ 2 ∂ν ≤
      C ^ 4 * ∫ D, ((determF (n₀ + m) z w D).toReal -
        (determF (n₀ + (m + 1)) z w D).toReal) *
        (determF (n₀ + (m + 1)) z w D).toReal ∂ν := by
    intro m
    have hz' : ‖z‖ < (n₀ + m : ℕ) := hz.trans_le (by exact_mod_cast Nat.le_add_right n₀ m)
    have hw' : ‖w‖ < (n₀ + m : ℕ) := hw.trans_le (by exact_mod_cast Nat.le_add_right n₀ m)
    convert determ_var_measure ν hL C hC1 hcopy z w (n₀ + m) hz' hw' (hprod (n₀ + m)) using 1 <;>
      simp only [Nat.add_assoc]
  exact LQGMetric.LM.t17_var_limit
    (F := fun m D => (determF (n₀ + m) z w D).toReal)
    (G := fun D => D.1 (z, w)) (c := C ^ 4)
    (fun m => (determ_measurableF (n₀ + m) z w).ennreal_toReal)
    (hprops.mono fun D hD => hD.1)
    (hprops.mono fun D hD => hD.2.1)
    (hprops.mono fun D hD => hD.2.2) hvar

end HigherDimLQGMetric
