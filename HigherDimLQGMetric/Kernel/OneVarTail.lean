import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import HigherDimLQGMetric.Kernel.OneVarLandau

/-!
# Tail integrals `G(x) = ∫_x^∞ f` of rapidly decreasing functions

Packet L1b (block B1), audit MA5 Details (a) A2.2 (the function `G` there). For a continuous
`f : ℝ → ℝ` with `s² |f s| ≤ C` for `s ≥ 1`:

* `integrableOn_Ioi_of_decay` — `f` is integrable on every `Ioi a`;
* `hasDerivAt_integral_Ioi` — `G' = -f` everywhere (fundamental theorem of calculus);
* `contDiff_integral_Ioi`, `iteratedDeriv_succ_integral_Ioi` — `G` is smooth with
  `G^{(j+1)} = -f^{(j)}` when `f` is;
* `integral_Ioi_le_integral_Ioi`, `integral_Ioi_nonneg` — monotonicity and sign when `f ≥ 0` on `(0, ∞)`;
* `integral_Ioi_le_of_decay` — `G(x) ≤ C / x^{K+1}` when `s^{K+2} |f s| ≤ C` (`x ≥ 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

/-- Pointwise form of a decay bound: `s^N |u s| ≤ C` gives `|u s| ≤ C / s^N` (`s ≥ 1`). -/
lemma abs_le_div_pow_of_decay {u : ℝ → ℝ} {N : ℕ} {C : ℝ} (hC : ∀ s, 1 ≤ s → s ^ N * |u s| ≤ C)
    {s : ℝ} (hs : 1 ≤ s) : |u s| ≤ C / s ^ N := by
  have hpos : 0 < s ^ N := pow_pos (lt_of_lt_of_le one_pos hs) N
  rw [le_div_iff₀ hpos, mul_comm]
  exact hC s hs

/-- A continuous function with `s² |f s| ≤ C` for `s ≥ 1` is integrable on every `Ioi a`. -/
theorem integrableOn_Ioi_of_decay {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ s, 1 ≤ s → s ^ 2 * |f s| ≤ C) (a : ℝ) : IntegrableOn f (Ioi a) := by
  have h1 : IntegrableOn f (Ioi 1) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      one_pos).const_mul C) hf.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    rw [Real.norm_eq_abs, Real.rpow_neg hs0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← div_eq_mul_inv]
    exact abs_le_div_pow_of_decay hC hs1
  have h2 : IntegrableOn f (Icc (min a 1) 1) := hf.integrableOn_Icc
  refine (h2.union h1).mono_set fun s hs => ?_
  by_cases hs1 : s ≤ 1
  · exact Or.inl ⟨(min_le_left a 1).trans (le_of_lt hs), hs1⟩
  · exact Or.inr (lt_of_not_ge hs1)

/-- `G(x) = ∫_{(x,∞)} f` has derivative `-f(y)` at every `y`. -/
theorem hasDerivAt_integral_Ioi {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ a, IntegrableOn f (Ioi a)) (y : ℝ) :
    HasDerivAt (fun x => ∫ s in Ioi x, f s) (-f y) y := by
  have heq : (fun x => ∫ s in Ioi x, f s) =
      fun x => (∫ s in Ioi (0 : ℝ), f s) - ∫ s in (0 : ℝ)..x, f s := by
    funext x
    rw [← intervalIntegral.integral_interval_add_Ioi (hint 0) (hint x)]
    ring
  rw [heq]
  exact (hf.integral_hasStrictDerivAt 0 y).hasDerivAt.const_sub _

/-- `G` is smooth when `f` is, with `G' = -f`. -/
theorem deriv_integral_Ioi {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ a, IntegrableOn f (Ioi a)) :
    deriv (fun x => ∫ s in Ioi x, f s) = fun y => -f y :=
  funext fun y => (hasDerivAt_integral_Ioi hf hint y).deriv

theorem contDiff_integral_Ioi {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hint : ∀ a, IntegrableOn f (Ioi a)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ s in Ioi x, f s) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun y => (hasDerivAt_integral_Ioi hf.continuous hint y)
    |>.differentiableAt, ?_⟩
  rw [deriv_integral_Ioi hf.continuous hint]
  exact hf.neg

/-- `G^{(j+1)} = -f^{(j)}`. -/
theorem iteratedDeriv_succ_integral_Ioi {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ a, IntegrableOn f (Ioi a)) (j : ℕ) :
    iteratedDeriv (j + 1) (fun x => ∫ s in Ioi x, f s) = fun y => -iteratedDeriv j f y := by
  rw [iteratedDeriv_succ', deriv_integral_Ioi hf hint]
  funext y
  exact iteratedDeriv_neg j f y

/-- If `f ≥ 0` on `(0, ∞)`, then `G` is nonincreasing on `(0, ∞)`. -/
theorem integral_Ioi_le_integral_Ioi {f : ℝ → ℝ} (hint : ∀ a, IntegrableOn f (Ioi a)) (hnn : ∀ s, 0 < s → 0 ≤ f s) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) : ∫ s in Ioi y, f s ≤ ∫ s in Ioi x, f s := by
  have h := intervalIntegral.integral_interval_add_Ioi (hint x) (hint y)
  have h2 : 0 ≤ ∫ s in x..y, f s :=
    intervalIntegral.integral_nonneg hxy fun s hs => hnn s (lt_of_lt_of_le hx hs.1)
  linarith

/-- If `s^{K+2} |f s| ≤ C` for `s ≥ 1`, then `G(x) ≤ C / x^{K+1}` for `x ≥ 1`. -/
theorem integral_Ioi_le_of_decay {f : ℝ → ℝ} (hf : Continuous f) {K : ℕ} {C : ℝ}
    (hC : ∀ s, 1 ≤ s → s ^ (K + 2) * |f s| ≤ C) {x : ℝ} (hx : 1 ≤ x) :
    ∫ s in Ioi x, f s ≤ C / x ^ (K + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ 1 ^ (K + 2) * |f 1|).trans (hC 1 le_rfl)
  have hC2 : ∀ s, 1 ≤ s → s ^ 2 * |f s| ≤ C := fun s hs => by
    have h1 : s ^ 2 ≤ s ^ (K + 2) := pow_le_pow_right₀ hs (by omega)
    have := hC s hs
    nlinarith [abs_nonneg (f s)]
  have hint := integrableOn_Ioi_of_decay hf hC2 x
  have ha : -((K : ℝ) + 2) < -1 := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hgint : IntegrableOn (fun s : ℝ => C * s ^ (-((K : ℝ) + 2))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt ha hx0).const_mul C
  have hmono : ∫ s in Ioi x, f s ≤ ∫ s in Ioi x, C * s ^ (-((K : ℝ) + 2)) := by
    refine setIntegral_mono_on hint hgint measurableSet_Ioi fun s hs => ?_
    have hs1 : (1 : ℝ) ≤ s := hx.trans (le_of_lt hs)
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    have hcast : s ^ (-((K : ℝ) + 2)) = (s ^ (K + 2))⁻¹ := by
      rw [Real.rpow_neg hs0.le, show ((K : ℝ) + 2) = ((K + 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hcast, ← div_eq_mul_inv]
    exact (le_abs_self _).trans (abs_le_div_pow_of_decay hC hs1)
  have hcalc : ∫ s in Ioi x, C * s ^ (-((K : ℝ) + 2)) = C * (x ^ (K + 1))⁻¹ / ((K : ℝ) + 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hx0]
    have e1 : -((K : ℝ) + 2) + 1 = -((K : ℝ) + 1) := by ring
    rw [e1, Real.rpow_neg hx0.le, show ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    field_simp
  rw [hcalc] at hmono
  refine hmono.trans ?_
  have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hxp : 0 < x ^ (K + 1) := pow_pos hx0 _
  rw [div_eq_mul_inv C]
  calc C * (x ^ (K + 1))⁻¹ / ((K : ℝ) + 1) ≤ C * (x ^ (K + 1))⁻¹ :=
        div_le_self (by positivity) hK1
    _ = C * (x ^ (K + 1))⁻¹ := rfl

end HigherDimLQGMetric
