import Mathlib

/-!
# Rate estimates and the first Borel–Cantelli lemma

The following analytic facts are useful for probabilistic growth arguments: Cesàro averages preserve
limits, exponential sequences are summable, and summable event probabilities imply eventual
avoidance almost surely.
-/

set_option autoImplicit false

open Filter MeasureTheory Topology

namespace MatedCRTHarmonic.Growth

/-- The sum of weights at times `1, …, n`. -/
def shiftedPartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, a (t + 1)

/-- The power sum over times `1, …, n`, bounded by the corresponding integral estimate. -/
theorem sum_natCast_rpow_neg_le {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (n : ℕ) :
    (∑ t ∈ Finset.range n, ((t + 1 : ℕ) : ℝ) ^ (-θ)) ≤
      (n : ℝ) ^ (1 - θ) / (1 - θ) := by
  induction n with
  | zero =>
      have hq : 0 < 1 - θ := by linarith
      simp [Real.zero_rpow (ne_of_gt hq)]
  | succ n ih =>
      let f : ℝ → ℝ := fun x => x ^ (-θ)
      have hanti : AntitoneOn f (Set.Icc 1 (1 + (n : ℝ))) := by
        intro x hx y hy hxy
        dsimp [f]
        exact Real.rpow_le_rpow_of_nonpos (x := x) (y := y) (z := -θ)
          (by linarith [hx.1]) hxy (by linarith)
      have hsum := hanti.sum_le_integral
      have hInt : (∫ x in (1 : ℝ)..(1 + (n : ℝ)), f x) =
          (((1 + (n : ℝ)) ^ (1 - θ) - 1) / (1 - θ)) := by
        change (∫ x in (1 : ℝ)..(1 + (n : ℝ)), x ^ (-θ)) = _
        rw [integral_rpow (a := 1) (b := 1 + (n : ℝ))
          (r := -θ) (Or.inl (by linarith))]
        simp [sub_eq_add_neg, add_comm]
      have hq : 0 < 1 - θ := by linarith
      have hqle : 1 - θ ≤ 1 := by linarith
      have hsum' :
          (∑ t ∈ Finset.range n, ((t + 2 : ℕ) : ℝ) ^ (-θ)) ≤
            (((1 + (n : ℝ)) ^ (1 - θ) - 1) / (1 - θ)) := by
        calc
          _ = ∑ t ∈ Finset.range n, f (1 + (t + 1 : ℕ)) := by
            apply Finset.sum_congr rfl
            intro t ht
            dsimp [f]
            congr 1
            push_cast
            ring
          _ ≤ ∫ x in (1 : ℝ)..(1 + (n : ℝ)), f x := hsum
          _ = _ := hInt
      rw [Finset.sum_range_succ']
      have hqne : (1 - θ) ≠ 0 := ne_of_gt hq
      have hfinal :
          1 + (((1 + (n : ℝ)) ^ (1 - θ) - 1) / (1 - θ)) ≤
            (1 + (n : ℝ)) ^ (1 - θ) / (1 - θ) := by
        calc
          _ = (1 - θ) / (1 - θ) +
                (((1 + (n : ℝ)) ^ (1 - θ) - 1) / (1 - θ)) := by
                  rw [div_self hqne]
          _ = ((1 - θ) + ((1 + (n : ℝ)) ^ (1 - θ) - 1)) / (1 - θ) := by ring
          _ ≤ (1 + (n : ℝ)) ^ (1 - θ) / (1 - θ) := by
            exact div_le_div_of_nonneg_right (by nlinarith [hqle]) hq.le
      calc
        _ = (∑ t ∈ Finset.range n, ((t + 2 : ℕ) : ℝ) ^ (-θ)) + 1 := by
          simp [Nat.cast_add, add_comm, add_left_comm]
        _ ≤ 1 + (((1 + (n : ℝ)) ^ (1 - θ) - 1) / (1 - θ)) := by
          linarith [hsum']
        _ ≤ (1 + (n : ℝ)) ^ (1 - θ) / (1 - θ) := by
          simpa [add_comm] using hfinal
        _ = (n + 1 : ℕ) ^ (1 - θ) / (1 - θ) := by
          congr 2
          push_cast
          ring

/-- Cesàro averaging: if the weights tend to zero, their shifted partial sums are sublinear. -/
theorem tendsto_shiftedPartialSum_div_of_tendsto_zero {a : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => shiftedPartialSum a n / (n : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => a (n + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.add_comm] using
      ha.comp (tendsto_add_atTop_nat 1)
  have hc := hs.cesaro
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [shiftedPartialSum, div_eq_mul_inv, mul_comm]

/-- Exponential tails `2^(-c n)` are summable for every positive rate `c`. -/
theorem summable_two_neg_linear {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (-c * (n : ℝ))) := by
  let q : ℝ := (2 : ℝ) ^ (-c)
  have hqpos : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq : q < 1 := by
    have hpow : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
    dsimp [q]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ hpow
  have heq : ∀ n : ℕ, (2 : ℝ) ^ (-c * (n : ℝ)) = q ^ n := by
    intro n
    calc
      (2 : ℝ) ^ (-c * (n : ℝ)) = ((2 : ℝ) ^ (-c)) ^ (n : ℝ) := Real.rpow_mul (by norm_num) _ _
      _ = q ^ n := by simp [q, Real.rpow_natCast]
  exact (summable_geometric_of_lt_one hqpos.le hq).congr (fun n => (heq n).symm)

/-- Stretched exponential tails with a positive power are summable. -/
theorem summable_two_neg_nat_rpow {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => (2 : ℝ) ^ (-((n : ℝ) ^ α))) := by
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by
    dsimp [c]
    exact half_pos (Real.log_pos (by norm_num))
  have hlog := (isLittleO_log_rpow_atTop hα).def hc
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ c * (n : ℝ) ^ α :=
    ((hcast.eventually hlog).and (eventually_gt_atTop 0)).mono fun n ⟨hn, hnpos⟩ => by
      have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
      have hlogpos : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos))
      have hpowpos : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hnpos'.le _
      simpa [Real.norm_eq_abs, abs_of_nonneg hlogpos, abs_of_nonneg hpowpos] using hn
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hlarge
  let N := max N₀ 1
  have hN : ∀ m : ℕ, N ≤ m → Real.log (m : ℝ) ≤ c * (m : ℝ) ^ α := by
    intro m hm
    exact hN₀ m (le_trans (le_max_left _ _) hm)
  have htail : Summable (fun n : ℕ => (2 : ℝ) ^ (-((n + N : ℕ) : ℝ) ^ α)) := by
    have hpoly : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ (2 : ℝ))) := by
      convert (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num : 1 < (2 : ℝ)) using 1
      funext n
      simp [abs_of_pos (by positivity : 0 < ((n : ℝ) + 1))]
    apply hpoly.of_norm_bounded
    intro n
    let x : ℝ := ((n + N : ℕ) : ℝ)
    let y : ℝ := ((n + 1 : ℕ) : ℝ)
    have hx : 0 < x := by positivity
    have hy : 0 < y := by positivity
    have hbound : Real.log x ≤ c * x ^ α := by
      exact hN (n + N) (by dsimp [N]; omega)
    have hlogineq : 2 * Real.log x ≤ Real.log 2 * x ^ α := by
      calc
        2 * Real.log x ≤ 2 * (c * x ^ α) := mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = Real.log 2 * x ^ α := by dsimp [c]; ring
    have hcmp : -Real.log 2 * x ^ α ≤ -2 * Real.log x := by
      nlinarith [hlogineq]
    have hpow : x ^ (-2 : ℝ) = 1 / x ^ (2 : ℝ) := by
      rw [Real.rpow_neg hx.le]
      simp [div_eq_mul_inv]
    have hden : 1 / x ^ (2 : ℝ) ≤ 1 / y ^ (2 : ℝ) := by
      have hxy : y ≤ x := by
        dsimp [x, y]
        exact_mod_cast (show n + 1 ≤ n + N by dsimp [N]; omega)
      have hsq : y ^ (2 : ℝ) ≤ x ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hxy (by norm_num)
      exact one_div_le_one_div_of_le (by positivity) hsq
    have hle : (2 : ℝ) ^ (-x ^ α) ≤ 1 / y ^ (2 : ℝ) := by
      calc
        (2 : ℝ) ^ (-x ^ α) = Real.exp (Real.log 2 * (-x ^ α)) :=
          Real.rpow_def_of_pos (by norm_num) _
        _ ≤ Real.exp (-2 * Real.log x) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hlogineq]
        _ = x ^ (-2 : ℝ) := by
          rw [Real.rpow_def_of_pos hx]
          congr 1
          ring
        _ = 1 / x ^ (2 : ℝ) := hpow
        _ ≤ 1 / y ^ (2 : ℝ) := hden
    have hnonneg : 0 ≤ (2 : ℝ) ^ (-x ^ α) := Real.rpow_nonneg (by norm_num) _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [x, y] using hle
  exact (summable_nat_add_iff (f := fun n : ℕ =>
    (2 : ℝ) ^ (-((n : ℝ) ^ α))) N).mp htail

/-- First Borel–Cantelli in its eventual-avoidance form. -/
theorem ae_eventually_notMem_of_summable_events {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (hE : ∑' n, μ (E n) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n :=
  MeasureTheory.ae_eventually_notMem hE

end MatedCRTHarmonic.Growth
