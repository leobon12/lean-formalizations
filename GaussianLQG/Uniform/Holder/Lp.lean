import GaussianLQG.Uniform.Holder.Moments
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# U12, analysis helpers: Minkowski for `[0,∞]`-valued functions and the dyadic series

Phase B, packet PB-U12 (ledger U12, Finding `fd:U12`, change (iii): Minkowski in `L^q` in place of
the linearity of the mean in `S6P28U.mean_RK`).

* `lpN P p f = (∫⁻ f^p)^{1/p}`: `lpN_add_le`, `lpN_sum_le` (Minkowski,
  `ENNReal.lintegral_Lp_add_le`), `lpN_const_mul`, `lpN_le_of_lintegral_le`,
  `lintegral_eq_lpN_rpow`;
* `exp_sqrt_le`, `sum_exp_sqrt_le`: `e^{-a x + D√x} ≤ e^{D²/(2a)} e^{-a x/2}` and the geometric sum,
  so that `Σ_k e^{-a k + D √k} ≤ e^{D²/(2a)} / (1 − e^{-a/2})` over any finite set of indices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Holder

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The `L^p` seminorm of `[0,∞]`-valued functions -/

/-- `(∫⁻ f^p)^{1/p}` -/
def lpN (P : Measure Ω) (p : ℝ) (f : Ω → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ ω, f ω ^ p ∂P) ^ (1 / p)

lemma lpN_add_le {p : ℝ} (hp : 1 ≤ p) {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    (hg : AEMeasurable g P) : lpN P p (fun ω => f ω + g ω) ≤ lpN P p f + lpN P p g :=
  ENNReal.lintegral_Lp_add_le hf hg hp

lemma lpN_zero {p : ℝ} (hp : 0 < p) : lpN P p (fun _ => 0) = 0 := by
  simp [lpN, ENNReal.zero_rpow_of_pos hp, hp]

/-- **Minkowski for finite sums** -/
lemma lpN_sum_le {p : ℝ} (hp : 1 ≤ p) {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ≥0∞}
    (hf : ∀ i ∈ s, AEMeasurable (f i) P) :
    lpN P p (fun ω => ∑ i ∈ s, f i ω) ≤ ∑ i ∈ s, lpN P p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [lpN_zero (by linarith)]
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have hs : AEMeasurable (fun ω => ∑ i ∈ s, f i ω) P := by
      exact (Finset.aemeasurable_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)).congr
        (Filter.Eventually.of_forall fun ω => Finset.sum_apply ω s f)
    calc lpN P p (fun ω => f a ω + ∑ i ∈ s, f i ω)
        ≤ lpN P p (f a) + lpN P p (fun ω => ∑ i ∈ s, f i ω) :=
          lpN_add_le hp (hf a (Finset.mem_insert_self a s)) hs
      _ ≤ lpN P p (f a) + ∑ i ∈ s, lpN P p (f i) :=
          add_le_add le_rfl (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma lpN_const_mul {p : ℝ} (hp : 0 < p) {c : ℝ≥0∞} (hc : c ≠ ⊤) (f : Ω → ℝ≥0∞) :
    lpN P p (fun ω => c * f ω) = c * lpN P p f := by
  unfold lpN
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hp.ne']

lemma lintegral_eq_lpN_rpow {p : ℝ} (hp : 0 < p) (f : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω ^ p ∂P = lpN P p f ^ p := by
  rw [lpN, one_div, ENNReal.rpow_inv_rpow hp.ne']

/-- `lpN f ≤ c^{1/p} e^{y}` from `∫⁻ f^p ≤ c e^{p y}` -/
lemma lpN_le_of_lintegral_le {p : ℕ} (hp : p ≠ 0) {f : Ω → ℝ≥0∞} {c y : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, f ω ^ p ∂P ≤ ENNReal.ofReal (c * Real.exp (p * y))) :
    lpN P p f ≤ ENNReal.ofReal (c ^ ((p : ℝ)⁻¹) * Real.exp y) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  unfold lpN
  simp_rw [ENNReal.rpow_natCast]
  refine (ENNReal.rpow_le_rpow h (by positivity)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.mul_rpow hc (Real.exp_pos _).le, ← Real.exp_mul, one_div]
  congr 3
  field_simp

/-! ### The dyadic series -/

/-- `-a x + D √x ≤ -(a/2) x + D²/(2a)` -/
lemma exp_sqrt_le {a : ℝ} (ha : 0 < a) (D : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    -a * x + D * √x ≤ -(a / 2) * x + D ^ 2 / (2 * a) := by
  have hs := Real.sq_sqrt hx
  have key : D * √x ≤ a / 2 * x + D ^ 2 / (2 * a) := by
    have h2 : 2 * a * (a / 2 * x + D ^ 2 / (2 * a)) = a ^ 2 * x + D ^ 2 := by field_simp
    have h3 : 2 * a * (D * √x) ≤ 2 * a * (a / 2 * x + D ^ 2 / (2 * a)) := by
      rw [h2]; nlinarith [sq_nonneg (a * √x - D), hs]
    exact le_of_mul_le_mul_left h3 (by positivity)
  linarith

/-- the series bound: `Σ_{k ∈ s} e^{-a k + D √k} ≤ e^{D²/(2a)} / (1 − e^{-a/2})` -/
lemma sum_exp_sqrt_le {a : ℝ} (ha : 0 < a) (D : ℝ) (s : Finset ℕ) :
    ∑ k ∈ s, Real.exp (-a * k + D * √(k : ℝ)) ≤
      Real.exp (D ^ 2 / (2 * a)) / (1 - Real.exp (-(a / 2))) := by
  set u := Real.exp (-(a / 2)) with hu
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hterm : ∀ k : ℕ, Real.exp (-a * k + D * √(k : ℝ)) ≤ Real.exp (D ^ 2 / (2 * a)) * u ^ k := by
    intro k
    rw [hu, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := exp_sqrt_le ha D (Nat.cast_nonneg k)
    linarith
  set N := s.sup id + 1
  have hsub : s ⊆ Finset.range N := fun k hk =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hgeo : ∑ k ∈ s, u ^ k ≤ 1 / (1 - u) := by
    calc ∑ k ∈ s, u ^ k ≤ ∑ k ∈ Finset.range N, u ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hu0 _
      _ = ∑ k ∈ Finset.Ico 0 N, u ^ k := by rw [Finset.range_eq_Ico]
      _ ≤ u ^ 0 / (1 - u) := geom_sum_Ico_le_of_lt_one hu0 hu1
      _ = 1 / (1 - u) := by rw [pow_zero]
  calc ∑ k ∈ s, Real.exp (-a * k + D * √(k : ℝ))
      ≤ ∑ k ∈ s, Real.exp (D ^ 2 / (2 * a)) * u ^ k := Finset.sum_le_sum fun k _ => hterm k
    _ = Real.exp (D ^ 2 / (2 * a)) * ∑ k ∈ s, u ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.exp (D ^ 2 / (2 * a)) * (1 / (1 - u)) := by gcongr
    _ = Real.exp (D ^ 2 / (2 * a)) / (1 - u) := by ring

/-- one term is at most the series bound -/
lemma exp_sqrt_le_sum_bound {a : ℝ} (ha : 0 < a) (D : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-a * x + D * √x) ≤ Real.exp (D ^ 2 / (2 * a)) / (1 - Real.exp (-(a / 2))) := by
  have hu1 : Real.exp (-(a / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hu0 : 0 < Real.exp (-(a / 2)) := Real.exp_pos _
  calc Real.exp (-a * x + D * √x) ≤ Real.exp (D ^ 2 / (2 * a)) := by
        refine Real.exp_le_exp.2 ?_
        have := exp_sqrt_le ha D hx
        have : 0 ≤ (a / 2) * x := by positivity
        linarith
    _ ≤ Real.exp (D ^ 2 / (2 * a)) / (1 - Real.exp (-(a / 2))) := by
        rw [le_div_iff₀ (by linarith)]
        have : 0 < Real.exp (D ^ 2 / (2 * a)) := Real.exp_pos _
        nlinarith

end Holder
end Uniform
end GaussianLQG
