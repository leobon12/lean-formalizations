import SmallGammaGeodesics.Probes.Basic
import SmallGammaGeodesics.Probes.Decay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Lemma 4.1, (4.6): the low-pass remainder (GA2 D4.5)

For `y` continuous on `[0,1]` with `y(0) = y(1) = 0`, `t ∈ [0,1]` and `J ≥ 0`:
`|y(t) - S_J(t)| ≤ C ω_y(ℓ_J)` (`lemma41_lowPass`).

The proof works on `[0,1]` directly, without the odd periodic extension:

* `lowPass_eq_integral`: `S_J(t) = ∫₀¹ y(u) (K_J(t-u) - K_J(t+u)) du`, where
  `K_J(s) = 1/2 + ∑_{k=1}^{2^{J+1}} χ(kℓ_J) cos(kπs)` (`lowKer`).
  This uses `2 sin(kπt) sin(kπu) = cos(kπ(t-u)) - cos(kπ(t+u))`.
* `integral_lowKer_add`: `∫₀¹ (K_J(t-u) + K_J(t+u)) du = 1`. Hence
  `y(t) - S_J(t) = ∫₀¹ [(y(t)-y(u)) K_J(t-u) + (y(t)+y(u)) K_J(t+u)] du`.
* `lowKer_decay`: `(1 + |s|/ℓ_J) |K_J(s)| ≤ C_K ℓ_J/(ℓ_J² + s²)` for `|s| ≤ 1`. This is the decay
  lemma with `p = 3` (`2K_J(s) = ∑_{|k| ≤ N} χ(k/2^J) e^{ikπs}`), and `K_J(s - 2) = K_J(s)`.
* `abs_sub_le_chain`: `|y(s) - y(t)| ≤ (1 + |s-t|/ℓ) ω_y(ℓ)`, by subadditivity of the modulus.
  With `y(0) = y(1) = 0` it also gives `|y(t) + y(u)| ≤ (2 + d/ℓ) ω_y(ℓ)`, where
  `d = min(t+u, 2-t-u)`.
* `integral_lorentz_le`: `∫_α^β ℓ²/(ℓ² + (x-c)²) dx ≤ πℓ` (arctan).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped Real

namespace SmallGammaGeodesics

/-! ### Lorentzian integrals -/

theorem continuous_lorentz {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) :
    Continuous fun x : ℝ => ℓ ^ 2 / (ℓ ^ 2 + (x - c) ^ 2) :=
  continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun x => by positivity)

/-- `∫_α^β ℓ²/(ℓ² + (x-c)²) dx ≤ πℓ`. -/
theorem integral_lorentz_le {ℓ : ℝ} (hℓ : 0 < ℓ) (c α β : ℝ) :
    ∫ x in α..β, ℓ ^ 2 / (ℓ ^ 2 + (x - c) ^ 2) ≤ π * ℓ := by
  have hderiv : ∀ x ∈ Set.uIcc α β, HasDerivAt (fun x => ℓ * Real.arctan ((x - c) / ℓ))
      (ℓ ^ 2 / (ℓ ^ 2 + (x - c) ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => (x - c) / ℓ) (1 / ℓ) x :=
      ((hasDerivAt_id x).sub_const c).div_const ℓ
    have h3 := ((Real.hasDerivAt_arctan ((x - c) / ℓ)).comp x h1).const_mul ℓ
    refine h3.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_lorentz hℓ c).intervalIntegrable α β)]
  have h1 := Real.arctan_lt_pi_div_two ((β - c) / ℓ)
  have h2 := Real.neg_pi_div_two_lt_arctan ((α - c) / ℓ)
  nlinarith

/-- `∫_α^β ℓ/(ℓ² + (x-c)²) dx ≤ π`. -/
theorem integral_lorentz_le' {ℓ : ℝ} (hℓ : 0 < ℓ) (c α β : ℝ) :
    ∫ x in α..β, ℓ / (ℓ ^ 2 + (x - c) ^ 2) ≤ π := by
  have h : (fun x : ℝ => ℓ / (ℓ ^ 2 + (x - c) ^ 2)) =
      fun x => ℓ⁻¹ * (ℓ ^ 2 / (ℓ ^ 2 + (x - c) ^ 2)) := by
    funext x
    field_simp
  rw [h, intervalIntegral.integral_const_mul]
  calc ℓ⁻¹ * ∫ x in α..β, ℓ ^ 2 / (ℓ ^ 2 + (x - c) ^ 2) ≤ ℓ⁻¹ * (π * ℓ) :=
        mul_le_mul_of_nonneg_left (integral_lorentz_le hℓ c α β) (inv_nonneg.mpr hℓ.le)
    _ = π := by field_simp

theorem continuous_lorentz' {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) :
    Continuous fun x : ℝ => ℓ / (ℓ ^ 2 + (x - c) ^ 2) :=
  continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun x => by positivity)

/-! ### The modulus of continuity -/

/-- `|y(s) - y(t)| ≤ ω_y(r)` for `s, t ∈ [0,1]` with `|s - t| ≤ r`. -/
theorem abs_sub_le_modulus {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1)) {r s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hst : |s - t| ≤ r) :
    |y s - y t| ≤ modulus y r := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hbd : ∀ s' t' : Set.Icc (0 : ℝ) 1,
      (⨆ (_ : |(s' : ℝ) - t'| ≤ r), |y s' - y t'|) ≤ 2 * B := by
    intro s' t'
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
    by_cases h : |(s' : ℝ) - t'| ≤ r
    · rw [ciSup_pos h]
      have h1 := hB s' s'.2
      have h2 := hB t' t'.2
      rw [Real.norm_eq_abs] at h1 h2
      calc |y s' - y t'| ≤ |y s'| + |y t'| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    · have : IsEmpty (|(s' : ℝ) - t'| ≤ r) := ⟨h⟩
      rw [Real.iSup_of_isEmpty]
      linarith
  have hbdd1 : ∀ s' : Set.Icc (0 : ℝ) 1, BddAbove (Set.range fun t' : Set.Icc (0 : ℝ) 1 =>
      ⨆ (_ : |(s' : ℝ) - t'| ≤ r), |y s' - y t'|) := by
    intro s'
    exact ⟨2 * B, by rintro _ ⟨t', rfl⟩; exact hbd s' t'⟩
  have hbdd2 : BddAbove (Set.range fun s' : Set.Icc (0 : ℝ) 1 => ⨆ t' : Set.Icc (0 : ℝ) 1,
      ⨆ (_ : |(s' : ℝ) - t'| ≤ r), |y s' - y t'|) := by
    refine ⟨2 * B, ?_⟩
    rintro _ ⟨s', rfl⟩
    exact ciSup_le fun t' => hbd s' t'
  unfold modulus
  calc |y s - y t| = ⨆ (_ : |((⟨s, hs⟩ : Set.Icc (0 : ℝ) 1) : ℝ) - (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1)|
        ≤ r), |y s - y t| := by
        rw [ciSup_pos (show |((⟨s, hs⟩ : Set.Icc (0 : ℝ) 1) : ℝ) -
          (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1)| ≤ r from hst)]
    _ ≤ ⨆ t' : Set.Icc (0 : ℝ) 1, ⨆ (_ : |((⟨s, hs⟩ : Set.Icc (0 : ℝ) 1) : ℝ) - t'| ≤ r),
          |y s - y t'| := le_ciSup (hbdd1 ⟨s, hs⟩) ⟨t, ht⟩
    _ ≤ _ := le_ciSup hbdd2 ⟨s, hs⟩

theorem modulus_nonneg {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1)) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ modulus y r := by
  have := abs_sub_le_modulus hy (r := r) (s := 0) (t := 0) ⟨le_rfl, zero_le_one⟩
    ⟨le_rfl, zero_le_one⟩ (by simpa using hr)
  simpa using this

/-- Subadditivity of the modulus: `|y(s) - y(t)| ≤ (1 + |s-t|/ℓ) ω_y(ℓ)` for `s, t ∈ [0,1]`. -/
theorem abs_sub_le_chain {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1)) {ℓ s t : ℝ}
    (hℓ : 0 < ℓ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |y s - y t| ≤ (1 + |s - t| / ℓ) * modulus y ℓ := by
  have hω := modulus_nonneg hy hℓ.le
  set n := ⌈|s - t| / ℓ⌉₊ with hn
  have hq : 0 ≤ |s - t| / ℓ := by positivity
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have h1 : |s - t| / ℓ ≤ 0 := Nat.ceil_eq_zero.mp h0
    have h2 : |s - t| = 0 := by
      have := div_nonpos_iff.mp h1
      rcases this with h | h
      · exact le_antisymm (by linarith [h.2, hℓ]) (abs_nonneg _)
      · exact le_antisymm h.1 (abs_nonneg _)
    have hst : s = t := by
      have := abs_eq_zero.mp h2
      linarith
    rw [hst, sub_self, abs_zero]
    positivity
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hpos
    let x : ℕ → ℝ := fun i => s + (i / n) * (t - s)
    have hx : ∀ i ≤ n, x i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i hi
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hc0 : 0 ≤ (i : ℝ) / n := by positivity
      have hc1 : (i : ℝ) / n ≤ 1 := (div_le_one hnr).mpr hi'
      obtain ⟨hs0, hs1⟩ := hs
      obtain ⟨ht0, ht1⟩ := ht
      constructor
      · show 0 ≤ s + (i / n) * (t - s)
        nlinarith
      · show s + (i / n) * (t - s) ≤ 1
        nlinarith
    have hstep : ∀ i, |x i - x (i + 1)| ≤ ℓ := by
      intro i
      have : x i - x (i + 1) = -((t - s) / n) := by
        simp only [x]
        push_cast
        field_simp
        ring
      rw [this, abs_neg, abs_div, abs_of_pos hnr, abs_sub_comm, div_le_iff₀ hnr]
      have := Nat.le_ceil (|s - t| / ℓ)
      rw [← hn, div_le_iff₀ hℓ] at this
      linarith
    have htel : y s - y t = ∑ i ∈ range n, (y (x i) - y (x (i + 1))) := by
      rw [sum_range_sub' (fun i => y (x i)) n]
      simp only [x, Nat.cast_zero, zero_div, zero_mul, add_zero]
      congr 1
      rw [div_self hnr.ne', one_mul]
      ring_nf
    have hceil : (n : ℝ) ≤ 1 + |s - t| / ℓ := by
      have := Nat.ceil_lt_add_one hq
      rw [← hn] at this
      linarith
    calc |y s - y t| = |∑ i ∈ range n, (y (x i) - y (x (i + 1)))| := by rw [htel]
      _ ≤ ∑ i ∈ range n, |y (x i) - y (x (i + 1))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range n, modulus y ℓ := by
          refine sum_le_sum fun i hi => ?_
          have hi' : i < n := mem_range.mp hi
          exact abs_sub_le_modulus hy (hx i hi'.le) (hx (i + 1) hi') (hstep i)
      _ = n * modulus y ℓ := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ (1 + |s - t| / ℓ) * modulus y ℓ := mul_le_mul_of_nonneg_right hceil hω

/-! ### The low-pass kernel -/

/-- `K_J(s) = 1/2 + ∑_{k=1}^{2^{J+1}} χ(kℓ_J) cos(kπs)`. -/
def lowKer (J : ℕ) (s : ℝ) : ℝ :=
  1 / 2 + ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)), chi ((k : ℝ) * ell J) * Real.cos ((k : ℝ) * π * s)

theorem continuous_lowKer (J : ℕ) : Continuous (lowKer J) := by
  unfold lowKer
  refine continuous_const.add (continuous_finsetSum _ fun k _ => ?_)
  exact continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

theorem lowKer_sub_two (J : ℕ) (s : ℝ) : lowKer J (s - 2) = lowKer J s := by
  unfold lowKer
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show (k : ℝ) * π * (s - 2) = (k : ℝ) * π * s - (k : ℕ) * (2 * π) by ring,
    Real.cos_sub_nat_mul_two_pi]

/-- `2 K_J(s) = ∑_{|k| ≤ N} χ(k/2^J) e^{ikπs}` for `N = 2^{J+1} + 3`. -/
theorem lowKer_eq_trigSum (J : ℕ) (s : ℝ) :
    (lowKer J s : ℂ) = (1 / 2 : ℂ) *
      trigSum (2 ^ J) (2 ^ (J + 1) + 3) (fun s => (chi s : ℂ)) (π * s) := by
  unfold lowKer trigSum
  rw [sum_Icc_int_eq]
  have hkell : ∀ k : ℕ, (k : ℝ) / ((2 ^ J : ℕ) : ℝ) = (k : ℝ) * ell J := by
    intro k
    unfold ell
    push_cast
    ring
  have hsub : Icc (1 : ℕ) (2 ^ (J + 1)) ⊆ Icc (1 : ℕ) (2 ^ (J + 1) + 3) := by
    intro k hk
    simp only [mem_Icc] at hk ⊢
    omega
  rw [← sum_subset hsub]
  · push_cast
    rw [mul_add, mul_sum]
    simp only [zero_div, chi_zero, Complex.ofReal_one, zero_mul, Complex.exp_zero, mul_one]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    have h1 : ((-(k : ℝ)) / ((2 ^ J : ℕ) : ℝ)) = -((k : ℝ) * ell J) := by
      rw [neg_div, hkell]
    simp only [Nat.cast_pow, Nat.cast_ofNat] at h1 hkell
    rw [h1, chi_neg, hkell k, Complex.cos]
    ring_nf
  · intro k hk hk'
    simp only [mem_Icc, not_and_or, not_le] at hk hk'
    have hq : chi ((k : ℝ) * ell J) = 0 :=
      chi_of_two_le (two_le_natCast_mul_ell (show 2 ^ (J + 1) ≤ k by omega))
    have hq' : chi ((k : ℝ) / ((2 ^ J : ℕ) : ℝ)) = 0 := by rw [hkell]; exact hq
    have hq'' : chi ((-(k : ℝ)) / ((2 ^ J : ℕ) : ℝ)) = 0 := by
      rw [neg_div, chi_neg]; exact hq'
    push_cast at hq' hq'' ⊢
    simp [hq', hq'']

/-- Real-variable bookkeeping for the kernel decay. -/
theorem lowKer_bookkeeping {n ℓ S σ M₃ : ℝ} (hn : 1 ≤ n) (hℓ : ℓ * n = 1) (hS : 0 ≤ S)
    (hσ : 0 ≤ σ) (hM : 0 ≤ M₃) (h1 : S ≤ (2 * (2 * n) + 1) * 1)
    (h2 : (2 * σ) ^ 3 * S ≤ (2 * (2 * n) + 3 + 1) * M₃ / n ^ 3) :
    (1 + σ / ℓ) * (S / 2) ≤ (10 + 2 * M₃) * (ℓ / (ℓ ^ 2 + σ ^ 2)) := by
  have hℓpos : 0 < ℓ := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hnℓ : n = ℓ⁻¹ := by field_simp; linarith
  have hD : 0 < ℓ ^ 2 + σ ^ 2 := by positivity
  rcases le_or_gt σ ℓ with hσℓ | hσℓ
  · -- `σ ≤ ℓ`: `(1 + σ/ℓ) S/2 ≤ 5/ℓ ≤ 10 ℓ/(ℓ² + σ²)`
    have hA : 1 + σ / ℓ ≤ 2 := by
      have := (div_le_one hℓpos).mpr hσℓ
      linarith
    have hB : S / 2 ≤ 5 / (2 * ℓ) := by
      rw [hnℓ] at h1
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : S ≤ 4 * ℓ⁻¹ + 1 := by linarith
      have hℓ1 : ℓ ≤ 1 := by
        rw [hnℓ] at hn
        exact (one_le_inv₀ hℓpos).mp hn
      calc S * (2 * ℓ) ≤ (4 * ℓ⁻¹ + 1) * (2 * ℓ) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = 8 + 2 * ℓ := by field_simp; ring
        _ ≤ 5 * 2 := by linarith
    have hC : 5 / ℓ ≤ 10 * (ℓ / (ℓ ^ 2 + σ ^ 2)) := by
      rw [div_le_iff₀ hℓpos, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hD]
      nlinarith
    calc (1 + σ / ℓ) * (S / 2) ≤ 2 * (5 / (2 * ℓ)) :=
          mul_le_mul hA hB (by positivity) (by norm_num)
      _ = 5 / ℓ := by field_simp
      _ ≤ 10 * (ℓ / (ℓ ^ 2 + σ ^ 2)) := hC
      _ ≤ (10 + 2 * M₃) * (ℓ / (ℓ ^ 2 + σ ^ 2)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- `σ > ℓ`: `S ≤ M₃ ℓ²/σ³`, so `(1 + σ/ℓ) S/2 ≤ M₃ ℓ/σ² ≤ 2 M₃ ℓ/(ℓ² + σ²)`
    have hσpos : 0 < σ := lt_trans hℓpos hσℓ
    have hS3 : S ≤ M₃ * ℓ ^ 2 / σ ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      have h2' : 8 * σ ^ 3 * S ≤ (4 * n + 4) * M₃ / n ^ 3 := by
        have e1 : (2 * σ) ^ 3 = 8 * σ ^ 3 := by ring
        have e2 : (2 * (2 * n) + 3 + 1) = 4 * n + 4 := by ring
        rw [e1, e2] at h2
        linarith
      have h3 : (4 * n + 4) * M₃ / n ^ 3 ≤ 8 * M₃ * ℓ ^ 2 := by
        rw [div_le_iff₀ (by positivity), hnℓ]
        field_simp
        rw [hnℓ] at hn
        have hℓ1 : ℓ ≤ 1 := (one_le_inv₀ hℓpos).mp hn
        nlinarith
      nlinarith
    have hA : 1 + σ / ℓ ≤ 2 * σ / ℓ := by
      rw [show 2 * σ / ℓ = σ / ℓ + σ / ℓ by ring]
      have : 1 ≤ σ / ℓ := (one_le_div hℓpos).mpr hσℓ.le
      linarith
    calc (1 + σ / ℓ) * (S / 2) ≤ (2 * σ / ℓ) * (M₃ * ℓ ^ 2 / σ ^ 3 / 2) :=
          mul_le_mul hA (by linarith) (by positivity) (by positivity)
      _ = M₃ * ℓ / σ ^ 2 := by field_simp
      _ ≤ 2 * M₃ * (ℓ / (ℓ ^ 2 + σ ^ 2)) := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hD]
          have : ℓ ^ 2 + σ ^ 2 ≤ 2 * σ ^ 2 := by nlinarith
          nlinarith [mul_nonneg hM hℓpos.le]
      _ ≤ (10 + 2 * M₃) * (ℓ / (ℓ ^ 2 + σ ^ 2)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Kernel decay**: `(1 + |s|/ℓ_J) |K_J(s)| ≤ C_K ℓ_J/(ℓ_J² + s²)` for `|s| ≤ 1`. -/
theorem lowKer_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : ℕ) (s : ℝ), |s| ≤ 1 →
      (1 + |s| / ell J) * |lowKer J s| ≤ C * (ell J / (ell J ^ 2 + s ^ 2)) := by
  have hchi : ∀ {n : ℕ∞}, ContDiff ℝ n fun s : ℝ => (chi s : ℂ) := fun {_} =>
    Complex.ofRealCLM.contDiff.comp contDiff_chi
  have hsupp0 : ∀ s : ℝ, 2 ≤ |s| → (chi s : ℂ) = 0 := by
    intro s hs
    rw [chi_eq_zero hs, Complex.ofReal_zero]
  obtain ⟨M₃, hM₃⟩ := exists_bound_iteratedDeriv hchi (hasCompactSupport_of_abs hsupp0) 3
  have hM₃0 : 0 ≤ M₃ := le_trans (norm_nonneg _) (hM₃ 0)
  refine ⟨10 + 2 * M₃, by positivity, fun J s hs => ?_⟩
  have hn : 0 < 2 ^ J := by positivity
  have hsupp : ∀ s : ℝ, ((2 ^ (J + 1) : ℕ) : ℝ) / ((2 ^ J : ℕ) : ℝ) < |s| → (chi s : ℂ) = 0 := by
    intro s' hs'
    refine hsupp0 s' ?_
    have : ((2 ^ (J + 1) : ℕ) : ℝ) / ((2 ^ J : ℕ) : ℝ) = 2 := by
      push_cast
      rw [pow_succ]
      field_simp
    linarith
  have hM₀ : ∀ s : ℝ, ‖(chi s : ℂ)‖ ≤ 1 := by
    intro s'
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chi_nonneg s')]
    exact chi_le_one s'
  have hθ : |π * s| ≤ π := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hdec := decay_lemma (p := 3) (R := 2 ^ (J + 1)) (N := 2 ^ (J + 1) + 3) hn le_rfl
    hchi hsupp hM₀ hM₃ hθ
  have hK : |lowKer J s| = ‖trigSum (2 ^ J) (2 ^ (J + 1) + 3) (fun s => (chi s : ℂ)) (π * s)‖ / 2 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, lowKer_eq_trigSum, norm_mul]
    norm_num
    ring
  have h1 := hdec.1
  have h2 := hdec.2
  have hθabs : 2 * |π * s| / π = 2 * |s| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hθabs] at h2
  push_cast at h1 h2
  have e : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by ring
  rw [e] at h1 h2
  have hℓn : ell J * 2 ^ J = 1 := ell_mul_pow J
  rw [hK, ← sq_abs s]
  exact lowKer_bookkeeping (one_le_pow₀ (by norm_num)) hℓn (norm_nonneg _) (abs_nonneg s) hM₃0
    h1 h2

/-! ### Integral representations -/

theorem intervalIntegrable_mul_cont {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1))
    {g : ℝ → ℝ} (hg : Continuous g) : IntervalIntegrable (fun u => y u * g u) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le zero_le_one]
  exact hy.mul hg.continuousOn

/-- `S_J(t) = ∫₀¹ y(u) (K_J(t-u) - K_J(t+u)) du`. -/
theorem lowPass_eq_integral {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1)) (J : ℕ) (t : ℝ) :
    lowPass y J t = ∫ u in (0 : ℝ)..1, y u * (lowKer J (t - u) - lowKer J (t + u)) := by
  have hpt : ∀ u, y u * (lowKer J (t - u) - lowKer J (t + u)) =
      ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)), (2 * chi ((k : ℝ) * ell J) * Real.sin ((k : ℝ) * π * t)) *
        (y u * Real.sin ((k : ℝ) * π * u)) := by
    intro u
    unfold lowKer
    rw [add_sub_add_left_eq_sub, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_sub, Real.cos_sub_cos]
    have h1 : ((k : ℝ) * π * (t - u) + (k : ℝ) * π * (t + u)) / 2 = (k : ℝ) * π * t := by ring
    have h2 : ((k : ℝ) * π * (t - u) - (k : ℝ) * π * (t + u)) / 2 = -((k : ℝ) * π * u) := by ring
    rw [h1, h2, Real.sin_neg]
    ring
  simp_rw [hpt]
  have hint : ∀ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)), IntervalIntegrable
      (fun u => (2 * chi ((k : ℝ) * ell J) * Real.sin ((k : ℝ) * π * t)) *
        (y u * Real.sin ((k : ℝ) * π * u))) volume 0 1 := by
    intro k _
    have hc : Continuous fun u : ℝ => Real.sin ((k : ℝ) * π * u) := by fun_prop
    exact (intervalIntegrable_mul_cont hy hc).const_mul _
  rw [intervalIntegral.integral_finsetSum hint]
  unfold lowPass sineCoef
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

theorem integral_cos_nat_mul_pi {k : ℕ} (hk : 1 ≤ k) :
    ∫ u in (0 : ℝ)..1, Real.cos ((k : ℝ) * π * u) = 0 := by
  have hkπ : (k : ℝ) * π ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega)) Real.pi_ne_zero
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun u => Real.sin ((k : ℝ) * π * u) /
      ((k : ℝ) * π)) (Real.cos ((k : ℝ) * π * u)) u := by
    intro u _
    have := (((hasDerivAt_id' u).const_mul ((k : ℝ) * π)).sin).div_const ((k : ℝ) * π)
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)]
  simp [Real.sin_nat_mul_pi]

/-- `∫₀¹ (K_J(t-u) + K_J(t+u)) du = 1`. -/
theorem integral_lowKer_add (J : ℕ) (t : ℝ) :
    ∫ u in (0 : ℝ)..1, (lowKer J (t - u) + lowKer J (t + u)) = 1 := by
  have hpt : ∀ u, lowKer J (t - u) + lowKer J (t + u) =
      1 + ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)), (2 * chi ((k : ℝ) * ell J) * Real.cos ((k : ℝ) * π * t)) *
        Real.cos ((k : ℝ) * π * u) := by
    intro u
    unfold lowKer
    rw [show ∀ a b c d : ℝ, a + b + (c + d) = (a + c) + (b + d) from fun a b c d => by ring,
      ← sum_add_distrib]
    congr 1
    · norm_num
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_add, Real.cos_add_cos]
    have h1 : ((k : ℝ) * π * (t - u) + (k : ℝ) * π * (t + u)) / 2 = (k : ℝ) * π * t := by ring
    have h2 : ((k : ℝ) * π * (t - u) - (k : ℝ) * π * (t + u)) / 2 = -((k : ℝ) * π * u) := by ring
    rw [h1, h2, Real.cos_neg]
    ring
  simp_rw [hpt]
  have hint : ∀ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)), IntervalIntegrable
      (fun u => (2 * chi ((k : ℝ) * ell J) * Real.cos ((k : ℝ) * π * t)) *
        Real.cos ((k : ℝ) * π * u)) volume 0 1 := fun k _ =>
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1).const_mul _
  have hsum : IntervalIntegrable (fun u => ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)),
      (2 * chi ((k : ℝ) * ell J) * Real.cos ((k : ℝ) * π * t)) * Real.cos ((k : ℝ) * π * u))
      volume 0 1 := by
    have : Continuous (fun u => ∑ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)),
        (2 * chi ((k : ℝ) * ell J) * Real.cos ((k : ℝ) * π * t)) * Real.cos ((k : ℝ) * π * u)) := by
      fun_prop
    exact this.intervalIntegrable 0 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hsum,
    intervalIntegral.integral_finsetSum hint]
  have hzero : ∀ k ∈ Icc (1 : ℕ) (2 ^ (J + 1)), ∫ u in (0 : ℝ)..1,
      (2 * chi ((k : ℝ) * ell J) * Real.cos ((k : ℝ) * π * t)) * Real.cos ((k : ℝ) * π * u) = 0 := by
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_cos_nat_mul_pi (mem_Icc.mp hk).1, mul_zero]
  rw [sum_eq_zero hzero]
  simp

/-! ### Lemma 4.1, (4.6) -/

/-- `|y(t) + y(u)| ≤ (2 + d/ℓ) ω_y(ℓ)` with `d = t + u` (using `y(0) = 0`). -/
theorem abs_add_le_of_zero {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1)) (hy0 : y 0 = 0)
    {ℓ t u : ℝ} (hℓ : 0 < ℓ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |y t + y u| ≤ 2 * (1 + (t + u) / ℓ) * modulus y ℓ := by
  have hω := modulus_nonneg hy hℓ.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 := abs_sub_le_chain hy hℓ ht h0
  have h2 := abs_sub_le_chain hy hℓ hu h0
  rw [hy0, sub_zero, sub_zero, abs_of_nonneg ht.1] at h1
  rw [hy0, sub_zero, sub_zero, abs_of_nonneg hu.1] at h2
  calc |y t + y u| ≤ |y t| + |y u| := abs_add_le _ _
    _ ≤ (1 + t / ℓ) * modulus y ℓ + (1 + u / ℓ) * modulus y ℓ := add_le_add h1 h2
    _ = (2 + (t + u) / ℓ) * modulus y ℓ := by ring
    _ ≤ 2 * (1 + (t + u) / ℓ) * modulus y ℓ := by
        refine mul_le_mul_of_nonneg_right ?_ hω
        have : 0 ≤ (t + u) / ℓ := div_nonneg (by linarith [ht.1, hu.1]) hℓ.le
        linarith

/-- `|y(t) + y(u)| ≤ (2 + d/ℓ) ω_y(ℓ)` with `d = 2 - t - u` (using `y(1) = 0`). -/
theorem abs_add_le_of_one {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 1)) (hy1 : y 1 = 0)
    {ℓ t u : ℝ} (hℓ : 0 < ℓ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |y t + y u| ≤ 2 * (1 + (2 - t - u) / ℓ) * modulus y ℓ := by
  have hω := modulus_nonneg hy hℓ.le
  have h1' : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h1 := abs_sub_le_chain hy hℓ ht h1'
  have h2 := abs_sub_le_chain hy hℓ hu h1'
  have e1 : |t - 1| = 1 - t := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [ht.2])
  have e2 : |u - 1| = 1 - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [hu.2])
  rw [hy1, sub_zero, e1] at h1
  rw [hy1, sub_zero, e2] at h2
  calc |y t + y u| ≤ |y t| + |y u| := abs_add_le _ _
    _ ≤ (1 + (1 - t) / ℓ) * modulus y ℓ + (1 + (1 - u) / ℓ) * modulus y ℓ := add_le_add h1 h2
    _ = (2 + (2 - t - u) / ℓ) * modulus y ℓ := by ring
    _ ≤ 2 * (1 + (2 - t - u) / ℓ) * modulus y ℓ := by
        refine mul_le_mul_of_nonneg_right ?_ hω
        have : 0 ≤ (2 - t - u) / ℓ := div_nonneg (by linarith [ht.2, hu.2]) hℓ.le
        linarith

/-- **Lemma 4.1, (4.6)**: `|y(t) - S_J(t)| ≤ C ω_y(ℓ_J)` for `y` continuous on `[0,1]` with
`y(0) = y(1) = 0`. -/
theorem lemma41_lowPass :
    ∃ C : ℝ, ∀ y : ℝ → ℝ, ContinuousOn y (Set.Icc 0 1) → y 0 = 0 → y 1 = 0 →
      ∀ J : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1, |y t - lowPass y J t| ≤ C * modulus y (ell J) := by
  obtain ⟨CK, hCK0, hCK⟩ := lowKer_decay
  refine ⟨5 * π * CK, fun y hy hy0 hy1 J t ht => ?_⟩
  set ℓ := ell J with hℓdef
  have hℓ : 0 < ℓ := ell_pos J
  set ω := modulus y ℓ with hωdef
  have hω : 0 ≤ ω := modulus_nonneg hy hℓ.le
  have hKc := continuous_lowKer J
  have hKm : Continuous fun u => lowKer J (t - u) := hKc.comp (continuous_const.sub continuous_id)
  have hKp : Continuous fun u => lowKer J (t + u) := hKc.comp (continuous_const.add continuous_id)
  -- the integral representation of the remainder
  have hrep : y t - lowPass y J t = ∫ u in (0 : ℝ)..1,
      ((y t - y u) * lowKer J (t - u) + (y t + y u) * lowKer J (t + u)) := by
    have hI1 : IntervalIntegrable (fun u => y t * (lowKer J (t - u) + lowKer J (t + u))) volume 0 1 :=
      ((hKm.add hKp).intervalIntegrable 0 1).const_mul _
    have hI2 : IntervalIntegrable (fun u => y u * (lowKer J (t - u) - lowKer J (t + u))) volume 0 1 :=
      intervalIntegrable_mul_cont hy (hKm.sub hKp)
    have : y t = ∫ u in (0 : ℝ)..1, y t * (lowKer J (t - u) + lowKer J (t + u)) := by
      rw [intervalIntegral.integral_const_mul, integral_lowKer_add, mul_one]
    rw [lowPass_eq_integral hy J t]
    conv_lhs => rw [this]
    rw [← intervalIntegral.integral_sub hI1 hI2]
    congr 1
    funext u
    ring
  -- pointwise domination
  set G : ℝ → ℝ := fun u => ω * CK * (ℓ / (ℓ ^ 2 + (u - t) ^ 2) +
      2 * (ℓ / (ℓ ^ 2 + (u - -t) ^ 2)) + 2 * (ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2))) with hG
  have hGc : Continuous G :=
    continuous_const.mul (((continuous_lorentz' hℓ t).add
      (continuous_const.mul (continuous_lorentz' hℓ (-t)))).add
        (continuous_const.mul (continuous_lorentz' hℓ (2 - t))))
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖(y t - y u) * lowKer J (t - u) + (y t + y u) * lowKer J (t + u)‖ ≤ G u := by
    intro u hu
    have hL1 : 0 ≤ ℓ / (ℓ ^ 2 + (u - t) ^ 2) := by positivity
    have hL2 : 0 ≤ ℓ / (ℓ ^ 2 + (u - -t) ^ 2) := by positivity
    have hL3 : 0 ≤ ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2) := by positivity
    -- first term
    have hA : |y t - y u| * |lowKer J (t - u)| ≤ ω * CK * (ℓ / (ℓ ^ 2 + (u - t) ^ 2)) := by
      have hch := abs_sub_le_chain hy hℓ ht hu
      have hs : |t - u| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
      have hdec := hCK J (t - u) hs
      rw [show (t - u) ^ 2 = (u - t) ^ 2 by ring] at hdec
      calc |y t - y u| * |lowKer J (t - u)| ≤ ((1 + |t - u| / ℓ) * ω) * |lowKer J (t - u)| :=
            mul_le_mul_of_nonneg_right hch (abs_nonneg _)
        _ = ω * ((1 + |t - u| / ℓ) * |lowKer J (t - u)|) := by ring
        _ ≤ ω * (CK * (ℓ / (ℓ ^ 2 + (u - t) ^ 2))) := mul_le_mul_of_nonneg_left hdec hω
        _ = ω * CK * (ℓ / (ℓ ^ 2 + (u - t) ^ 2)) := by ring
    -- second term
    have hB : |y t + y u| * |lowKer J (t + u)| ≤
        ω * CK * (2 * (ℓ / (ℓ ^ 2 + (u - -t) ^ 2)) + 2 * (ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2))) := by
      rcases le_total (t + u) 1 with h | h
      · have hadd := abs_add_le_of_zero hy hy0 hℓ ht hu
        have hs : |t + u| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [ht.1, hu.1]
        have hdec := hCK J (t + u) hs
        rw [abs_of_nonneg (by linarith [ht.1, hu.1] : 0 ≤ t + u),
          show (t + u) ^ 2 = (u - -t) ^ 2 by ring] at hdec
        calc |y t + y u| * |lowKer J (t + u)|
            ≤ (2 * (1 + (t + u) / ℓ) * ω) * |lowKer J (t + u)| :=
              mul_le_mul_of_nonneg_right hadd (abs_nonneg _)
          _ = 2 * ω * ((1 + (t + u) / ℓ) * |lowKer J (t + u)|) := by ring
          _ ≤ 2 * ω * (CK * (ℓ / (ℓ ^ 2 + (u - -t) ^ 2))) :=
              mul_le_mul_of_nonneg_left hdec (by positivity)
          _ ≤ ω * CK * (2 * (ℓ / (ℓ ^ 2 + (u - -t) ^ 2)) +
                2 * (ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2))) := by
              have : 0 ≤ ω * CK * (2 * (ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2))) := by positivity
              nlinarith
      · have hadd := abs_add_le_of_one hy hy1 hℓ ht hu
        have hs : |t + u - 2| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [ht.2, hu.2]
        have hdec := hCK J (t + u - 2) hs
        rw [lowKer_sub_two, abs_of_nonpos (by linarith [ht.2, hu.2] : t + u - 2 ≤ 0),
          show (t + u - 2) ^ 2 = (u - (2 - t)) ^ 2 by ring,
          show -(t + u - 2) = 2 - t - u by ring] at hdec
        calc |y t + y u| * |lowKer J (t + u)|
            ≤ (2 * (1 + (2 - t - u) / ℓ) * ω) * |lowKer J (t + u)| :=
              mul_le_mul_of_nonneg_right hadd (abs_nonneg _)
          _ = 2 * ω * ((1 + (2 - t - u) / ℓ) * |lowKer J (t + u)|) := by ring
          _ ≤ 2 * ω * (CK * (ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2))) :=
              mul_le_mul_of_nonneg_left hdec (by positivity)
          _ ≤ ω * CK * (2 * (ℓ / (ℓ ^ 2 + (u - -t) ^ 2)) +
                2 * (ℓ / (ℓ ^ 2 + (u - (2 - t)) ^ 2))) := by
              have : 0 ≤ ω * CK * (2 * (ℓ / (ℓ ^ 2 + (u - -t) ^ 2))) := by positivity
              nlinarith
    calc ‖(y t - y u) * lowKer J (t - u) + (y t + y u) * lowKer J (t + u)‖
        ≤ |y t - y u| * |lowKer J (t - u)| + |y t + y u| * |lowKer J (t + u)| := by
          rw [Real.norm_eq_abs, ← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ G u := by
          rw [hG]
          linarith
  -- integrate
  have hInt : ∫ u in (0 : ℝ)..1, G u ≤ 5 * π * CK * ω := by
    have i1 := integral_lorentz_le' hℓ t 0 1
    have i2 := integral_lorentz_le' hℓ (-t) 0 1
    have i3 := integral_lorentz_le' hℓ (2 - t) 0 1
    have c1 := (continuous_lorentz' hℓ t).intervalIntegrable (μ := volume) 0 1
    have c2 := (continuous_lorentz' hℓ (-t)).intervalIntegrable (μ := volume) 0 1
    have c3 := (continuous_lorentz' hℓ (2 - t)).intervalIntegrable (μ := volume) 0 1
    rw [hG, intervalIntegral.integral_const_mul, intervalIntegral.integral_add (c1.add (c2.const_mul 2))
      (c3.const_mul 2), intervalIntegral.integral_add c1 (c2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hωCK : 0 ≤ ω * CK := mul_nonneg hω hCK0
    calc ω * CK * ((∫ x in (0 : ℝ)..1, ℓ / (ℓ ^ 2 + (x - t) ^ 2)) +
          2 * (∫ x in (0 : ℝ)..1, ℓ / (ℓ ^ 2 + (x - -t) ^ 2)) +
          2 * ∫ x in (0 : ℝ)..1, ℓ / (ℓ ^ 2 + (x - (2 - t)) ^ 2))
        ≤ ω * CK * (π + 2 * π + 2 * π) := by
          refine mul_le_mul_of_nonneg_left ?_ hωCK
          linarith
      _ = 5 * π * CK * ω := by ring
  rw [hrep]
  calc |∫ u in (0 : ℝ)..1, ((y t - y u) * lowKer J (t - u) + (y t + y u) * lowKer J (t + u))|
      = ‖∫ u in (0 : ℝ)..1, ((y t - y u) * lowKer J (t - u) + (y t + y u) * lowKer J (t + u))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in (0 : ℝ)..1, G u := by
        refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_
          (hGc.intervalIntegrable 0 1)
        filter_upwards with u hu
        exact hpt u ⟨le_of_lt hu.1, hu.2⟩
    _ ≤ 5 * π * CK * ω := hInt

end SmallGammaGeodesics
