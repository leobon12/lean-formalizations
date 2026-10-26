import Mathlib

/-! Real arithmetic for the contraction iteration in Proposition 5.1. -/

set_option autoImplicit false
noncomputable section

namespace SupercriticalLFPPAS.Iteration

/-- The affine contraction factor from (4.1). -/
def contractionFactor (C K lam d₀ : ℝ) : ℝ :=
  (1 - lam) * max C K + (lam + 3 * d₀) * K

theorem contractionFactor_mono_left {C₁ C₂ K lam d₀ : ℝ}
    (hC : C₁ ≤ C₂) (hlam : lam ≤ 1) :
    contractionFactor C₁ K lam d₀ ≤ contractionFactor C₂ K lam d₀ := by
  unfold contractionFactor
  gcongr

theorem contractionFactor_mono_right {C K₁ K₂ lam d₀ : ℝ}
    (hK : K₁ ≤ K₂) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) (hd₀ : 0 ≤ d₀) :
    contractionFactor C K₁ lam d₀ ≤ contractionFactor C K₂ lam d₀ := by
  unfold contractionFactor
  have hm : max C K₁ ≤ max C K₂ := max_le_max_left C hK
  have hcoef : 0 ≤ lam + 3 * d₀ := by positivity
  have hleft : (1 - lam) * max C K₁ ≤ (1 - lam) * max C K₂ :=
    mul_le_mul_of_nonneg_left hm (by linarith)
  have hright : (lam + 3 * d₀) * K₁ ≤ (lam + 3 * d₀) * K₂ :=
    mul_le_mul_of_nonneg_left hK hcoef
  linarith

/-- The fixed point of the affine branch `C ≥ k` of the contraction map. -/
def contractionFixedPoint (k lam d₀ : ℝ) : ℝ := (1 + 3 * d₀ / lam) * k

theorem contractionFixedPoint_ge {k lam d₀ : ℝ}
    (hk : 0 ≤ k) (hlam : 0 < lam) (hd₀ : 0 ≤ d₀) :
    k ≤ contractionFixedPoint k lam d₀ := by
  unfold contractionFixedPoint
  have : 0 ≤ 3 * d₀ / lam := by positivity
  nlinarith [mul_nonneg hk this]

theorem contractionFixedPoint_is_fixed {k lam d₀ : ℝ}
    (hk : 0 ≤ k) (hlam : 0 < lam) (hd₀ : 0 ≤ d₀) :
    contractionFactor (contractionFixedPoint k lam d₀) k lam d₀ =
      contractionFixedPoint k lam d₀ := by
  have hmax : max (contractionFixedPoint k lam d₀) k = contractionFixedPoint k lam d₀ :=
    max_eq_left (contractionFixedPoint_ge hk hlam hd₀)
  unfold contractionFactor
  rw [hmax]
  unfold contractionFixedPoint
  field_simp
  ring

theorem contractionFactor_le_fixedPoint {C k lam d₀ : ℝ}
    (hk : 0 ≤ k) (hlam : 0 < lam) (hlam' : lam ≤ 1) (hd₀ : 0 ≤ d₀)
    (hC : C ≤ contractionFixedPoint k lam d₀) :
    contractionFactor C k lam d₀ ≤ contractionFixedPoint k lam d₀ := by
  calc
    contractionFactor C k lam d₀ ≤
        contractionFactor (contractionFixedPoint k lam d₀) k lam d₀ :=
      contractionFactor_mono_left hC hlam'
    _ = contractionFixedPoint k lam d₀ := contractionFixedPoint_is_fixed hk hlam hd₀

/-- One recursion step, with all scale parameters explicit. -/
theorem contractionFactor_step_bound {C Kbar lam d₀ x : ℝ}
    (hlam : 0 < lam) (hlam' : lam ≤ 1) (hd₀ : 0 ≤ d₀) (hK : 0 ≤ Kbar)
    (hx : 0 ≤ x) (hC : C ≤ (1 + 3 * d₀ / lam) * Kbar + x)
    {K : ℝ} (hKhi : K ≤ Kbar) :
    contractionFactor C K lam d₀ ≤
      (1 + 3 * d₀ / lam) * Kbar + (1 - lam) * x := by
  let T := (1 + 3 * d₀ / lam) * Kbar
  have hT : Kbar ≤ T := by
    dsimp [T]
    have hratio : 0 ≤ 3 * d₀ / lam := by positivity
    nlinarith [mul_nonneg hK hratio]
  have hmax : max C K ≤ T + x := max_le hC (by dsimp [T]; linarith)
  have hcoef : 0 ≤ 1 - lam := by linarith
  have hcoefK : 0 ≤ lam + 3 * d₀ := by positivity
  change C ≤ T + x at hC
  have hleft := contractionFactor_mono_left (C₁ := C) (C₂ := T + x)
    (K := K) (lam := lam) (d₀ := d₀) hC hlam'
  have hright := contractionFactor_mono_right (C := T + x) (K₁ := K) (K₂ := Kbar)
    (d₀ := d₀) hKhi (le_of_lt hlam) hlam' hd₀
  have hmaxT : max (T + x) Kbar = T + x := max_eq_left (by dsimp [T] at hT ⊢; linarith)
  have hfixed : contractionFactor (T + x) Kbar lam d₀ = T + (1 - lam) * x := by
    unfold contractionFactor
    rw [hmaxT]
    have hTidentity : (1 - lam) * T + (lam + 3 * d₀) * Kbar = T := by
      dsimp [T]
      have hlamne : lam ≠ 0 := ne_of_gt hlam
      field_simp
      ring
    calc
      (1 - lam) * (T + x) + (lam + 3 * d₀) * Kbar =
          ((1 - lam) * T + (lam + 3 * d₀) * Kbar) + (1 - lam) * x := by ring
      _ = T + (1 - lam) * x := by rw [hTidentity]
  calc
    (1 - lam) * max C K + (lam + 3 * d₀) * K ≤
        contractionFactor (T + x) Kbar lam d₀ := hleft.trans hright
    _ = T + (1 - lam) * x := hfixed
    _ = (1 + 3 * d₀ / lam) * Kbar + (1 - lam) * x := by rfl

/-- The variable-scale recursion is bounded by the affine fixed point plus the decaying
initial error, as in (5.5). -/
theorem contraction_recursion_bound {N : ℕ} {lam d₀ Kbar Cinit : ℝ}
    (hlam : 0 < lam) (hlam' : lam ≤ 1) (hd₀ : 0 ≤ d₀) (hKbar : 0 ≤ Kbar)
    (hCinit : 0 ≤ Cinit) {C K : ℕ → ℝ}
    (hC0 : C 0 = Cinit)
    (hrec : ∀ j < N, C (j + 1) = contractionFactor (C j) (K j) lam d₀)
    (_hKlo : ∀ j < N, 0 ≤ K j) (hKhi : ∀ j < N, K j ≤ Kbar) :
    C N ≤ (1 + 3 * d₀ / lam) * Kbar + (1 - lam) ^ N * Cinit := by
  have hiter : ∀ j ≤ N,
      C j ≤ (1 + 3 * d₀ / lam) * Kbar + (1 - lam) ^ j * Cinit := by
    intro j hj
    induction j with
    | zero => simp [hC0]; positivity
    | succ j ih =>
        have hjN : j < N := by omega
        have ihj := ih (by omega)
        have hxj : 0 ≤ (1 - lam) ^ j * Cinit :=
          mul_nonneg (pow_nonneg (by linarith : 0 ≤ 1 - lam) j) hCinit
        have hstep := contractionFactor_step_bound hlam hlam' hd₀ hKbar hxj
          ihj (hKhi j hjN)
        rw [hrec j hjN]
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hstep
  exact hiter N le_rfl

/-- Explicit constants and a finite iteration count make both the contracted and upper
comparison constants as close to one as required in Proposition 5.1. -/
theorem exists_iteration_constants {u lam Cinit : ℝ}
    (hu : 0 < u) (hlam : 0 < lam) (hlam' : lam ≤ 1) (_hCinit : 0 ≤ Cinit) :
    ∃ v d₀ : ℝ, ∃ N : ℕ,
      0 < v ∧ v ≤ 1 ∧ d₀ = lam * v / 6 ∧
      contractionFixedPoint (1 / (1 + v)) lam d₀ < 1 ∧
      contractionFixedPoint (1 / (1 + v)) lam d₀ + (1 - lam) ^ N * Cinit <
        (1 + contractionFixedPoint (1 / (1 + v)) lam d₀) / 2 ∧
      (1 + 3 * d₀ / lam) * (1 + v) + (1 - lam) ^ N * Cinit < 1 + u := by
  let v := min 1 (u / 8)
  let d₀ := lam * v / 6
  have hv : 0 < v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := min_le_left _ _
  have hsmall : 3 * v < u / 2 := by
    by_cases h : u / 8 ≤ 1
    · have hv_eq : v = u / 8 := by simp [v, h]
      rw [hv_eq]
      nlinarith
    · have hv_eq : v = 1 := by simp [v, min_eq_left (le_of_not_ge h)]
      rw [hv_eq]
      linarith
  have hTk : contractionFixedPoint (1 / (1 + v)) lam d₀ < 1 := by
    unfold contractionFixedPoint
    dsimp [d₀]
    have hvden : 0 < 1 + v := by linarith
    field_simp
    nlinarith
  have hbase : 0 ≤ 1 - lam := by linarith
  have hpowlim : Filter.Tendsto (fun n : ℕ => (1 - lam) ^ n * Cinit)
      Filter.atTop (nhds 0) := by
    have hlt : 1 - lam < 1 := by linarith
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hbase hlt).mul_const Cinit
  have hgap1 : 0 < (1 - contractionFixedPoint (1 / (1 + v)) lam d₀) / 2 := by linarith
  have hgap2 : 0 < u / 2 := by linarith
  have hgap : 0 < min ((1 - contractionFixedPoint (1 / (1 + v)) lam d₀) / 2) (u / 2 : ℝ) :=
    lt_min hgap1 hgap2
  obtain ⟨N, hN⟩ := (hpowlim.eventually (Iio_mem_nhds hgap)).exists
  have hpow : (1 - lam) ^ N * Cinit <
      min ((1 - contractionFixedPoint (1 / (1 + v)) lam d₀) / 2) (u / 2) := hN
  refine ⟨v, d₀, N, hv, hv1, rfl, hTk, ?_, ?_⟩
  · have := (lt_of_lt_of_le hpow (min_le_left _ _))
    linarith
  · have hmul : (1 + 3 * d₀ / lam) * (1 + v) = 1 + (3 / 2) * v + v ^ 2 / 2 := by
      dsimp [d₀]
      have hlamne : lam ≠ 0 := ne_of_gt hlam
      field_simp
      ring
    rw [hmul]
    have hp : (1 - lam) ^ N * Cinit < u / 2 := lt_of_lt_of_le hpow (min_le_right _ _)
    nlinarith [mul_le_mul_of_nonneg_left hv1 hv.le]

end SupercriticalLFPPAS.Iteration
