import HigherDimLQGMetric.Kernel.ConvKernelNearZero
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Uniform derivative bounds for the A2.4 square-root step

These finite-order bounds prepare the application of Mathlib's composition
estimate on a small punctured ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem finite_uniform_bound {X : Type} (b : ℕ → X → ℝ) (s : Set X)
    (h : ∀ i : ℕ, ∃ C : ℝ, ∀ x ∈ s, b i x ≤ C) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ x ∈ s, b i x ≤ A := by
  let C : ℕ → ℝ := fun i => max (Classical.choose (h i)) 0
  let A : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), C i
  have hC0 (i : ℕ) : 0 ≤ C i := le_max_right _ _
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), C i :=
    Finset.sum_nonneg (fun i _ => hC0 i)
  refine ⟨A, by dsimp [A]; linarith, fun i hi x hx => ?_⟩
  have hCi : b i x ≤ C i :=
    (Classical.choose_spec (h i) x hx).trans (le_max_left _ _)
  have himem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hle := Finset.single_le_sum (fun j _ => hC0 j) himem
  dsimp [A]
  linarith

theorem finite_uniform_weighted_bound {X : Type} (b : ℕ → X → ℝ)
    (w : X → ℝ) (s : Set X) (hw : ∀ x ∈ s, 0 ≤ w x)
    (h : ∀ i : ℕ, ∃ C : ℝ, ∀ x ∈ s, b i x ≤ C * w x) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ x ∈ s, b i x ≤ A * w x := by
  let C : ℕ → ℝ := fun i => max (Classical.choose (h i)) 0
  let A : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), C i
  have hC0 (i : ℕ) : 0 ≤ C i := le_max_right _ _
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), C i :=
    Finset.sum_nonneg (fun i _ => hC0 i)
  refine ⟨A, by dsimp [A]; linarith, fun i hi x hx => ?_⟩
  have hCi : b i x ≤ C i * w x :=
    (Classical.choose_spec (h i) x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw x hx))
  have himem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hle := Finset.single_le_sum (fun j _ => hC0 j) himem
  have hCA : C i ≤ A := by dsimp [A]; linarith
  exact hCi.trans (mul_le_mul_of_nonneg_right hCA (hw x hx))

/-- The square-root outer function is smooth below its branch point. -/
theorem sqrt_one_sub_contDiffOn :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.sqrt (1 - t)) (Iio 1) := by
  intro t ht
  have hpos : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  exact ((contDiffAt_const.sub contDiffAt_id).sqrt hpos).contDiffWithinAt

/-- Finitely many derivatives of the outer function are uniformly bounded near zero. -/
theorem sqrt_one_sub_deriv_bounded (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ i (fun s : ℝ => Real.sqrt (1 - s)) t‖ ≤ A := by
  have hs : Icc (-(1 / 2 : ℝ)) (1 / 2) ⊆ Iio 1 := by
    intro t ht
    exact lt_of_le_of_lt ht.2 (by norm_num)
  have hc (i : ℕ) : ContinuousOn
      (iteratedFDeriv ℝ i (fun s : ℝ => Real.sqrt (1 - s)))
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (ContinuousOn.continuousOn_iteratedFDeriv sqrt_one_sub_contDiffOn
      isOpen_Iio (by simp)).mono hs
  have hb (i : ℕ) : ∃ C : ℝ, ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2),
      ‖iteratedFDeriv ℝ i (fun s : ℝ => Real.sqrt (1 - s)) t‖ ≤ C := by
    have hbd : Bornology.IsBounded
        ((iteratedFDeriv ℝ i (fun s : ℝ => Real.sqrt (1 - s))) ''
          Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
      ((isCompact_Icc).image_of_continuousOn (hc i)).isBounded
    obtain ⟨C, hC⟩ := hbd.exists_norm_le
    exact ⟨C, fun t ht => hC _ ⟨t, ht, rfl⟩⟩
  obtain ⟨A, hA, hAi⟩ := finite_uniform_bound
    (fun i t => ‖iteratedFDeriv ℝ i (fun s : ℝ => Real.sqrt (1 - s)) t‖)
    (Icc (-(1 / 2 : ℝ)) (1 / 2)) hb n
  refine ⟨A, hA, fun i hi t ht => hAi i hi t ?_⟩
  exact abs_le.mp ht

theorem symbolPerturb_deriv_uniform {d : ℕ} {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ ζ : Rd d, ζ ≠ 0 → ‖ζ‖ ≤ 1 →
      ‖ζ‖ ^ i * ‖iteratedFDeriv ℝ i
        (fun z : Rd d => ‖z‖ ^ d * symbolAux κ z) ζ‖ ≤ A * ‖ζ‖ ^ d := by
  have h := finite_uniform_weighted_bound
    (fun (i : ℕ) (ζ : Rd d) => ‖ζ‖ ^ i * ‖iteratedFDeriv ℝ i
      (fun z : Rd d => ‖z‖ ^ d * symbolAux κ z) ζ‖)
    (fun ζ : Rd d => ‖ζ‖ ^ d)
    ({ζ : Rd d | ζ ≠ 0 ∧ ‖ζ‖ ≤ 1})
    (fun ζ _ => pow_nonneg (norm_nonneg _) _)
    (fun i => by
      obtain ⟨C, hC⟩ := symbolPerturb_iteratedFDeriv_weighted hκ i
      exact ⟨C, fun ζ hζ => hC ζ hζ.1 hζ.2⟩) n
  obtain ⟨A, hA, hAi⟩ := h
  exact ⟨A, hA, fun i hi ζ hζ hζ1 => hAi i hi ζ ⟨hζ, hζ1⟩⟩

theorem symbolPerturb_scaled_deriv_bounded {d : ℕ} {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i ≤ n, ∀ (r : ℝ) (u : Rd d),
      0 < r → r ≤ 1 → ‖u‖ = 1 →
      ‖iteratedFDeriv ℝ i
        (fun y : Rd d => ‖r • y‖ ^ d * symbolAux κ (r • y)) u‖ ≤ A * r ^ d := by
  obtain ⟨A, hA, hAi⟩ := symbolPerturb_deriv_uniform hκ n
  refine ⟨A, hA, fun i hi r u hr hr1 hu => ?_⟩
  let p : Rd d → ℝ := fun z => ‖z‖ ^ d * symbolAux κ z
  have hru : ‖r • u‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]
  have hru0 : r • u ≠ 0 := by
    intro he
    have := hru
    simp [he] at this
    linarith
  have hscale := congrFun (iteratedFDeriv_comp_const_smul_any r p i) u
  have hb := hAi i hi (r • u) hru0 (by simpa only [hru] using hr1)
  rw [hru] at hb
  rw [hscale]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] using hb

/-- A common scale factor dominates all derivative orders up to `n`. -/
theorem scale_factor_bound {d n i : ℕ} (hn : 0 < n) (hi : 0 < i)
    (hin : i ≤ n) {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1) :
    A * r ^ d ≤ (A * r ^ ((d : ℝ) / (n : ℝ))) ^ i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hiR : (i : ℝ) ≤ n := by exact_mod_cast hin
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hExp : (d : ℝ) / (n : ℝ) * (i : ℝ) ≤ (d : ℝ) := by
    calc
      (d : ℝ) / (n : ℝ) * (i : ℝ) = (d * i : ℝ) / (n : ℝ) := by ring
      _ ≤ d := (div_le_iff₀ hnR).mpr (by
        nlinarith only [mul_nonneg hdR (sub_nonneg.mpr hiR)])
  have hp : r ^ d ≤ (r ^ ((d : ℝ) / (n : ℝ))) ^ i := by
    rw [← Real.rpow_mul_natCast hr.le]
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_ge hr hr1 hExp
  calc
    A * r ^ d ≤ A * (r ^ ((d : ℝ) / (n : ℝ))) ^ i :=
      mul_le_mul_of_nonneg_left hp (by linarith)
    _ ≤ A ^ i * (r ^ ((d : ℝ) / (n : ℝ))) ^ i :=
      mul_le_mul_of_nonneg_right (le_self_pow₀ hA hi.ne') (pow_nonneg (by positivity) _)
    _ = (A * r ^ ((d : ℝ) / (n : ℝ))) ^ i := by rw [mul_pow]

end HigherDimLQGMetric
