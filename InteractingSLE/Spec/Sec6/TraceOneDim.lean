/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-dimensional inequalities behind the disk trace estimate (PU1)

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
`#id-PU1`, p. 164): "For `n ≠ 0`, completing the square gives
`|n| |a_n(1)|² ≤ ∫₀¹ (|a_n'(r)|² + n²/r² |a_n(r)|²) r dr`. The zero coefficient is controlled by
the one-dimensional trace inequality on `[1/2, 1]`, using both its squared value and squared
derivative on that interval."

* `InteractingSLE.Sec6.ofReal_mul_norm_sq_le_lintegral`: for `g` of class `C¹` on `(0, 1)`,
  continuous at `0⁺` with limit `0`, and `k ≥ 0`, `0 < R < 1`:
  `k ‖g(R)‖² ≤ ∫₀^R (s ‖g'(s)‖² + k² ‖g(s)‖²/s) ds` (as lower integrals);
* `InteractingSLE.Sec6.norm_sq_le_trace_one_dim`: for `g` of class `C¹` on `[a, b]`,
  `‖g(b)‖² ≤ 2/(b − a) ∫_a^b ‖g‖² + (b − a) ∫_a^b ‖g'‖²`.

Pitfall (ruling R28): the body of `∫ s in a..b, …` extends as far right as possible, so the first
integral in the statement is parenthesized; `∑' n, f n + c` is `(∑' n, f n) + c`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace InteractingSLE.Sec6

/-- The derivative of `‖g‖²` is bounded by `‖g‖² / c + c ‖g'‖²` (AM–GM), for every `c > 0`. -/
theorem two_mul_inner_le {x y : ℂ} {k s : ℝ} (hk : 0 ≤ k) (hs : 0 < s) :
    k * (2 * inner ℝ x y) ≤ s * ‖y‖ ^ 2 + k ^ 2 * ‖x‖ ^ 2 / s := by
  have h1 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have h2 : 0 ≤ (s * ‖y‖ - k * ‖x‖) ^ 2 / s := by positivity
  have h3 : (s * ‖y‖ - k * ‖x‖) ^ 2 / s = s * ‖y‖ ^ 2 + k ^ 2 * ‖x‖ ^ 2 / s - 2 * k * (‖x‖ * ‖y‖) := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 hk]

/-- **The weighted radial inequality** (PU1, `n ≠ 0` part). -/
theorem ofReal_mul_norm_sq_le_lintegral {g g' : ℝ → ℂ} (hg : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' s) s)
    (hg' : ContinuousOn g' (Ioo 0 1)) (hg0 : Tendsto g (𝓝[>] 0) (𝓝 0)) {k R : ℝ} (hk : 0 ≤ k)
    (hR0 : 0 < R) (hR1 : R < 1) :
    ENNReal.ofReal (k * ‖g R‖ ^ 2) ≤
      ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal (s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s) := by
  have hgc : ContinuousOn g (Ioo 0 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  -- the estimate on `[ε, R]`
  have hstep : ∀ ε ∈ Ioo (0 : ℝ) R, ENNReal.ofReal (k * ‖g R‖ ^ 2 - k * ‖g ε‖ ^ 2) ≤
      ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal (s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s) := by
    intro ε hε
    have hsub : Icc ε R ⊆ Ioo (0 : ℝ) 1 := fun s hs => ⟨lt_of_lt_of_le hε.1 hs.1, lt_of_le_of_lt hs.2 hR1⟩
    have hderiv : ∀ s ∈ uIcc ε R, HasDerivAt (fun s => k * ‖g s‖ ^ 2) (k * (2 * inner ℝ (g s) (g' s))) s := by
      intro s hs
      rw [uIcc_of_le hε.2.le] at hs
      exact ((hg s (hsub hs)).norm_sq).const_mul k
    have hcont1 : ContinuousOn (fun s => k * (2 * inner ℝ (g s) (g' s))) (Icc ε R) :=
      continuousOn_const.mul (continuousOn_const.mul
        ((hgc.mono hsub).inner (hg'.mono hsub)))
    have hcont2 : ContinuousOn (fun s => s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s) (Icc ε R) := by
      refine (continuousOn_id.mul ((hg'.mono hsub).norm.pow 2)).add
        ((continuousOn_const.mul ((hgc.mono hsub).norm.pow 2)).div continuousOn_id ?_)
      intro s hs; exact (lt_of_lt_of_le hε.1 hs.1).ne'
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont1.intervalIntegrable_of_Icc hε.2.le)
    have hle : ∫ s in ε..R, k * (2 * inner ℝ (g s) (g' s)) ≤
        ∫ s in ε..R, (s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s) := by
      refine intervalIntegral.integral_mono_on hε.2.le (hcont1.intervalIntegrable_of_Icc hε.2.le)
        (hcont2.intervalIntegrable_of_Icc hε.2.le) fun s hs => ?_
      exact two_mul_inner_le hk (lt_of_lt_of_le hε.1 hs.1)
    rw [hftc] at hle
    calc ENNReal.ofReal (k * ‖g R‖ ^ 2 - k * ‖g ε‖ ^ 2)
        ≤ ENNReal.ofReal (∫ s in ε..R, (s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s)) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ∫⁻ s in Ioc ε R, ENNReal.ofReal (s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s) := by
          rw [intervalIntegral.integral_of_le hε.2.le]
          refine ofReal_integral_eq_lintegral_ofReal
            ((hcont2.integrableOn_Icc).mono_set Ioc_subset_Icc_self) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          have : 0 < s := lt_of_lt_of_le hε.1 hs.1.le
          positivity
      _ ≤ ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal (s * ‖g' s‖ ^ 2 + k ^ 2 * ‖g s‖ ^ 2 / s) := by
          refine lintegral_mono_set' ?_
          -- `Ioc ε R ⊆ Ioo 0 R ∪ {R}` up to the null point `R`
          have : Ioc ε R ⊆ Ioo 0 R ∪ {R} := fun s hs => by
            rcases eq_or_lt_of_le hs.2 with h | h
            · exact Or.inr h
            · exact Or.inl ⟨lt_trans hε.1 hs.1, h⟩
          refine (this.eventuallyLE).trans ?_
          rw [union_singleton]
          exact (insert_ae_eq_self _ _).le
  -- `ε → 0⁺`
  have hlim : Tendsto (fun ε => ENNReal.ofReal (k * ‖g R‖ ^ 2 - k * ‖g ε‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (k * ‖g R‖ ^ 2 - k * ‖(0 : ℂ)‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds.sub ((hg0.norm.pow 2).const_mul k))
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hR0] with ε hε using hstep ε hε

/-- **The one-dimensional trace inequality** (PU1, zero coefficient):
`‖g(b)‖² ≤ 2/(b − a) ∫_a^b ‖g‖² + (b − a) ∫_a^b ‖g'‖²`. -/
theorem norm_sq_le_trace_one_dim {g g' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hg : ∀ s ∈ Icc a b, HasDerivAt g (g' s) s) (hg' : ContinuousOn g' (Icc a b)) :
    ‖g b‖ ^ 2 ≤ 2 / (b - a) * (∫ s in a..b, ‖g s‖ ^ 2) + (b - a) * ∫ s in a..b, ‖g' s‖ ^ 2 := by
  set L := b - a with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hgc : ContinuousOn g (Icc a b) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hc1 : ContinuousOn (fun s => ‖g s‖ ^ 2) (Icc a b) := hgc.norm.pow 2
  have hc2 : ContinuousOn (fun s => ‖g' s‖ ^ 2) (Icc a b) := hg'.norm.pow 2
  set Q := ∫ s in a..b, (‖g s‖ ^ 2 / L + L * ‖g' s‖ ^ 2) with hQ
  have hQint : ContinuousOn (fun s => ‖g s‖ ^ 2 / L + L * ‖g' s‖ ^ 2) (Icc a b) :=
    (hc1.div_const L).add (continuousOn_const.mul hc2)
  have hpt : ∀ s ∈ Icc a b, ‖g b‖ ^ 2 ≤ ‖g s‖ ^ 2 + Q := by
    intro s hs
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left hs.1
    have hderiv : ∀ τ ∈ uIcc s b, HasDerivAt (fun τ => ‖g τ‖ ^ 2) (2 * inner ℝ (g τ) (g' τ)) τ := by
      intro τ hτ
      rw [uIcc_of_le hs.2] at hτ
      exact (hg τ (hsub hτ)).norm_sq
    have hcont : ContinuousOn (fun τ => 2 * inner ℝ (g τ) (g' τ)) (Icc s b) :=
      continuousOn_const.mul ((hgc.mono hsub).inner (hg'.mono hsub))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc hs.2)
    have h1 : ∫ τ in s..b, 2 * inner ℝ (g τ) (g' τ) ≤
        ∫ τ in s..b, (‖g τ‖ ^ 2 / L + L * ‖g' τ‖ ^ 2) := by
      refine intervalIntegral.integral_mono_on hs.2 (hcont.intervalIntegrable_of_Icc hs.2)
        ((hQint.mono hsub).intervalIntegrable_of_Icc hs.2) fun τ _ => ?_
      have := two_mul_inner_le (x := g τ) (y := g' τ) zero_le_one hL0
      have h2 : (L * ‖g' τ‖ ^ 2 + 1 ^ 2 * ‖g τ‖ ^ 2 / L) = ‖g τ‖ ^ 2 / L + L * ‖g' τ‖ ^ 2 := by ring
      linarith
    have h2 : ∫ τ in s..b, (‖g τ‖ ^ 2 / L + L * ‖g' τ‖ ^ 2) ≤ Q := by
      rw [hQ, ← intervalIntegral.integral_add_adjacent_intervals
        ((hQint.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)
        ((hQint.mono hsub).intervalIntegrable_of_Icc hs.2)]
      have : 0 ≤ ∫ τ in a..s, (‖g τ‖ ^ 2 / L + L * ‖g' τ‖ ^ 2) :=
        intervalIntegral.integral_nonneg hs.1 fun τ _ => by positivity
      linarith
    rw [hftc] at h1
    linarith
  -- average over `s ∈ [a, b]`
  have havg : ∫ s in a..b, ‖g b‖ ^ 2 ≤ ∫ s in a..b, (‖g s‖ ^ 2 + Q) :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      ((hc1.add continuousOn_const).intervalIntegrable_of_Icc hab.le) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hc1.intervalIntegrable_of_Icc hab.le) intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul, smul_eq_mul] at havg
  have hi1 : IntervalIntegrable (fun s => ‖g s‖ ^ 2 / L) volume a b :=
    (hc1.div_const L).intervalIntegrable_of_Icc hab.le
  have hi2 : IntervalIntegrable (fun s => L * ‖g' s‖ ^ 2) volume a b :=
    (show ContinuousOn (fun s => L * ‖g' s‖ ^ 2) (Icc a b) from
      continuousOn_const.mul hc2).intervalIntegrable_of_Icc hab.le
  have hQeq : Q = (∫ s in a..b, ‖g s‖ ^ 2) / L + L * ∫ s in a..b, ‖g' s‖ ^ 2 := by
    rw [hQ, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
  rw [← hL, hQeq] at havg
  have hX : L * ((∫ s in a..b, ‖g s‖ ^ 2) / L) = ∫ s in a..b, ‖g s‖ ^ 2 := by field_simp
  have h3 : L * ‖g b‖ ^ 2 ≤ L * (2 / L * (∫ s in a..b, ‖g s‖ ^ 2) +
      L * ∫ s in a..b, ‖g' s‖ ^ 2) := by
    have h4 : L * (2 / L * (∫ s in a..b, ‖g s‖ ^ 2) + L * ∫ s in a..b, ‖g' s‖ ^ 2) =
        (∫ s in a..b, ‖g s‖ ^ 2) + L * ((∫ s in a..b, ‖g s‖ ^ 2) / L +
          L * ∫ s in a..b, ‖g' s‖ ^ 2) := by
      field_simp; ring
    rw [h4]; exact havg
  exact le_of_mul_le_mul_left h3 hL0

end InteractingSLE.Sec6
