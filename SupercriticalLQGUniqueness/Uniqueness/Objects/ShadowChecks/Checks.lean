


 









import Mathlib

set_option autoImplicit false

open Set Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ShadowChecks

 

theorem excursion_unique {c : ℂ} {R : ℝ} {P : ℝ → ℂ} {α₁ β₁ α₂ β₂ : ℝ}
    (h1α : ‖P α₁ - c‖ = R) (h1β : ‖P β₁ - c‖ = R) (h1 : ∀ s ∈ Ioo α₁ β₁, R < ‖P s - c‖)
    (h2α : ‖P α₂ - c‖ = R) (h2β : ‖P β₂ - c‖ = R) (h2 : ∀ s ∈ Ioo α₂ β₂, R < ‖P s - c‖)
    (hne : (Ioo α₁ β₁ ∩ Ioo α₂ β₂).Nonempty) : α₁ = α₂ ∧ β₁ = β₂ := by
  obtain ⟨t, ⟨ht1a, ht1b⟩, ⟨ht2a, ht2b⟩⟩ := hne
  constructor
  · rcases lt_trichotomy α₁ α₂ with h | h | h
    · have := h1 α₂ ⟨h, ht2a.trans ht1b⟩; linarith
    · exact h
    · have := h2 α₁ ⟨h, ht1a.trans ht2b⟩; linarith
  · rcases lt_trichotomy β₁ β₂ with h | h | h
    · have := h2 β₁ ⟨ht2a.trans ht1b, h⟩; linarith
    · exact h
    · have := h1 β₂ ⟨ht1a.trans ht2b, h⟩; linarith

 
theorem sep_of_disjoint {s t : ℝ → ℝ} {q : ℝ} {i j : ℝ} (hq : 0 ≤ q)
    (hi : q ≤ t i - s i) (hj : q ≤ t j - s j) (hdisj : t i < s j ∨ t j < s i) :
    q ≤ |t i - t j| := by
  rcases hdisj with h | h
  · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

 

theorem spread_of_separated {ι : Type*} [DecidableEq ι] (t : ι → ℝ) {q : ℝ}
    (S : Finset ι) (hS : S.Nonempty)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → q ≤ |t i - t j|) :
    ∃ i ∈ S, ∃ j ∈ S, ((S.card : ℝ) - 1) * q ≤ t j - t i := by
  induction S using Finset.induction_on_max_value t with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha hmax ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self _ _, a, Finset.mem_insert_self _ _, ?_⟩
      simp
    · have hsep' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → q ≤ |t i - t j| := fun i hi j hj hij =>
        hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      obtain ⟨i, hi, j, hj, hij⟩ := ih hs hsep'
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      have hq : q ≤ |t a - t j| :=
        hsep a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hja.symm
      rw [abs_of_nonneg (sub_nonneg.2 (hmax j hj))] at hq
      refine ⟨i, Finset.mem_insert_of_mem hi, a, Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.card_insert_of_notMem ha]
      push_cast
      linarith

 

theorem geom_pigeonhole {r m₀ : ℝ} (hr0 : 0 ≤ r) (hm₀ : 0 < m₀) (n : ℕ)
    (m : ℕ → ℝ) (hsum : m₀ ≤ ∑ j ∈ Finset.range n, m j) :
    ∃ j ∈ Finset.range n, (1 - r) * r ^ j * m₀ ≤ m j := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.range_zero, Finset.sum_empty] at hsum
    linarith
  · have hlt : ∑ j ∈ Finset.range n, m j < ∑ j ∈ Finset.range n, (1 - r) * r ^ j * m₀ :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 hn⟩ hcon
    have hgeom : ∑ j ∈ Finset.range n, (1 - r) * r ^ j * m₀ = (1 - r ^ n) * m₀ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, mul_neg_geom_sum]
    have hle : (1 - r ^ n) * m₀ ≤ m₀ := by nlinarith [pow_nonneg hr0 n]
    linarith

 
theorem inv_sqrt_two_lt_one : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ ∧ (Real.sqrt 2)⁻¹ < 1 := by
  refine ⟨inv_nonneg.2 (Real.sqrt_nonneg _), inv_lt_one_of_one_lt₀ ?_⟩
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

 
theorem chord_ge {x : ℝ} (hx : |x| ≤ π) :
    2 / π * |x| ≤ ‖Complex.exp (x * Complex.I) - 1‖ := by
  rw [mul_comm (x : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have hx2 : |x / 2| ≤ π / 2 := by rw [abs_div, abs_two]; linarith
  have hx2' : |x / 2| ≤ π := hx2.trans (by linarith [Real.pi_pos])
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hx2']
  have := Real.mul_le_sin (abs_nonneg (x / 2)) hx2
  rw [abs_div, abs_two] at this ⊢
  linarith

 


theorem cap_angle_measure_le {R ρ ψ : ℝ} (hR : 0 < R) :
    MeasureTheory.volume {θ : ℝ | θ ∈ Icc (ψ - π) (ψ + π) ∧
      ‖(R : ℂ) * Complex.exp (θ * Complex.I) - R * Complex.exp (ψ * Complex.I)‖ < ρ}
      ≤ ENNReal.ofReal (π * ρ / R) := by
  have hsub : {θ : ℝ | θ ∈ Icc (ψ - π) (ψ + π) ∧
      ‖(R : ℂ) * Complex.exp (θ * Complex.I) - R * Complex.exp (ψ * Complex.I)‖ < ρ} ⊆
      Ioo (ψ - π * ρ / (2 * R)) (ψ + π * ρ / (2 * R)) := by
    rintro θ ⟨hθ, hlt⟩
    have hθψ : |θ - ψ| ≤ π := by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    have hfac : (R : ℂ) * Complex.exp (θ * Complex.I) - R * Complex.exp (ψ * Complex.I) =
        (R * Complex.exp (ψ * Complex.I)) * (Complex.exp (((θ - ψ : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
      congr 3; push_cast; ring
    have hnorm : ‖(R : ℂ) * Complex.exp (θ * Complex.I) - R * Complex.exp (ψ * Complex.I)‖ =
        R * ‖Complex.exp (((θ - ψ : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [hfac, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hch := chord_ge hθψ
    rw [hnorm] at hlt
    have hpi := Real.pi_pos
    have key : |θ - ψ| < π * ρ / (2 * R) := by
      rw [lt_div_iff₀ (by positivity)]
      have h1 : 2 / π * |θ - ψ| * R < ρ := by nlinarith
      have h2 : 2 / π * |θ - ψ| * R * π = 2 * R * |θ - ψ| := by field_simp
      nlinarith
    rw [abs_lt] at key
    constructor <;> linarith [key.1, key.2]
  calc MeasureTheory.volume _ ≤ MeasureTheory.volume
        (Ioo (ψ - π * ρ / (2 * R)) (ψ + π * ρ / (2 * R))) := MeasureTheory.measure_mono hsub
    _ = ENNReal.ofReal (π * ρ / R) := by
        rw [Real.volume_Ioo]; congr 1; field_simp; ring

 
theorem two_rpow_quarter_le : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 5 / 4 := by
  have h : ((5 / 4 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = 5 / 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ ((5 / 4 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 5 / 4 := h

 

theorem count_suff {c B x n : ℝ} (hx : 1 ≤ x) (hB : 0 < B) (h : 21 * B ≤ c * x)
    (hn : c * x ^ 2 ≤ n) :
    1 + 16 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * x) ≤ n / B := by
  have h4 := two_rpow_quarter_le
  have hxpos : 0 < x := by linarith
  rw [le_div_iff₀ hB]
  have h1 : 21 * B * x ≤ c * x ^ 2 := by nlinarith
  have h2 : 16 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * x) ≤ 20 * x := by nlinarith
  nlinarith

 
theorem rpow_succ_quarter (k : ℝ) :
    (2 : ℝ) ^ ((k + 1) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ (k / 4) := by
  rw [← Real.rpow_add (by norm_num)]; congr 1; ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.ShadowChecks

