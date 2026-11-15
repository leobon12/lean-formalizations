/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsSemigroup
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Positivity of the Jacobi semigroup (maximum principle)

Packet PROVE-YW-JACOBI. For `κ, a, b ≥ 0` the semigroup `semi κ a b t = exp (t L)` of
`JacobiExistsSemigroup.lean` maps polynomials that are nonnegative on `[0, 1]` to polynomials that are
nonnegative on `[0, 1]`, for every `t ≥ 0` (`semi_eval_nonneg`). Consequently it is monotone and a
contraction for the sup norm on `[0, 1]` (`abs_semi_eval_le`).

Proof (the parabolic maximum principle). Let `v(t, x) = (semi t p).eval x + ε (1 + t)`. If `v ≤ 0`
somewhere in `[0, T] × [0, 1]`, let `t*` be the first such time and `x*` a point with
`v(t*, x*) ≤ 0`. Then `t* > 0`, `x*` minimizes `v(t*, ·)` on `[0, 1]`, so `L v(t*, ·)(x*) ≥ 0`
(`genL_eval_nonneg_of_isMinOn`: at an interior minimum `g' = 0` and `g'' ≥ 0`; at `0` the generator is
`(a/2) g'(0)` with `g'(0) ≥ 0`; at `1` it is `-(b/2) g'(1)` with `g'(1) ≤ 0`), hence
`∂ₜ v(t*, x*) = L v(t*, ·)(x*) + ε > 0`; but `v(·, x*) > 0` before `t*` forces `∂ₜ v(t*, x*) ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

open Polynomial Filter Topology Set

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

/-! ### One-dimensional calculus at a minimum -/

/-- A function with a minimum on `[x, x + d]` at its left endpoint has nonnegative derivative there. -/
theorem hasDerivAt_nonneg_of_isMinOn_Icc_left {g : ℝ → ℝ} {g' x d : ℝ} (hd : 0 < d)
    (hmin : IsMinOn g (Icc x (x + d)) x) (hg : HasDerivAt g g' x) : 0 ≤ g' := by
  have hloc : IsLocalMinOn g (Icc x (x + d)) x := hmin.isLocalMinOn
  have hcone : d ∈ posTangentConeAt (Icc x (x + d)) x :=
    mem_posTangentConeAt_of_segment_subset (by rw [segment_eq_Icc (by linarith)])
  have h := hloc.hasFDerivWithinAt_nonneg hg.hasDerivWithinAt.hasFDerivWithinAt hcone
  rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  exact nonneg_of_mul_nonneg_right h hd

/-- A function with a minimum on `[x - d, x]` at its right endpoint has nonpositive derivative. -/
theorem hasDerivAt_nonpos_of_isMinOn_Icc_right {g : ℝ → ℝ} {g' x d : ℝ} (hd : 0 < d)
    (hmin : IsMinOn g (Icc (x - d) x) x) (hg : HasDerivAt g g' x) : g' ≤ 0 := by
  have hloc : IsLocalMinOn g (Icc (x - d) x) x := hmin.isLocalMinOn
  have hcone : -d ∈ posTangentConeAt (Icc (x - d) x) x :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [segment_symm, segment_eq_Icc (by linarith)]
      exact Icc_subset_Icc (by linarith) le_rfl)
  have h := hloc.hasFDerivWithinAt_nonneg hg.hasDerivWithinAt.hasFDerivWithinAt hcone
  rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  nlinarith

/-- At an interior minimum of a polynomial, the second derivative is nonnegative. -/
theorem eval_derivative_derivative_nonneg_of_isMinOn {g : ℝ[X]} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hmin : IsMinOn (fun y => g.eval y) (Icc 0 1) x) :
    0 ≤ (derivative (derivative g)).eval x := by
  by_contra hneg
  push Not at hneg
  have hloc : IsLocalMin (fun y => g.eval y) x :=
    hmin.isLocalMin (Icc_mem_nhds hx.1 hx.2)
  have h1 : (derivative g).eval x = 0 := by
    have := hloc.hasDerivAt_eq_zero (g.hasDerivAt x)
    exact this
  -- `g'' < 0` near `x`
  have hev : ∀ᶠ y in 𝓝 x, (derivative (derivative g)).eval y < 0 :=
    (derivative (derivative g)).continuous.continuousAt.eventually_lt continuousAt_const hneg
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set h := min (δ / 2) ((1 - x) / 2) with hh
  have hpos : 0 < h := lt_min (by linarith) (by linarith [hx.2])
  have hlt : ∀ y ∈ Icc x (x + h), (derivative (derivative g)).eval y < 0 := by
    intro y hy
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2, min_le_left (δ / 2) ((1 - x) / 2)]
  -- mean value theorem twice
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun y => g.eval y)
    (fun y => (derivative g).eval y) (by linarith : x < x + h) g.continuous.continuousOn
    (fun y _ => g.hasDerivAt y)
  obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope (fun y => (derivative g).eval y)
    (fun y => (derivative (derivative g)).eval y) hξ.1 (derivative g).continuous.continuousOn
    (fun y _ => (derivative g).hasDerivAt y)
  have hη' : (derivative (derivative g)).eval η < 0 :=
    hlt η ⟨hη.1.le, (hη.2.trans hξ.2).le⟩
  have hgξ : (derivative g).eval ξ < 0 := by
    have hpos' : 0 < ξ - x := by linarith [hξ.1]
    rw [h1, sub_zero, eq_div_iff hpos'.ne'] at hηeq
    nlinarith
  have hdec : g.eval (x + h) < g.eval x := by
    have hpos' : 0 < x + h - x := by linarith
    rw [eq_div_iff hpos'.ne'] at hξeq
    nlinarith
  have hmem : x + h ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [min_le_right (δ / 2) ((1 - x) / 2)]⟩
  exact absurd (hmin hmem) (not_le.2 hdec)

variable {κ a b : ℝ}

/-- **The generator at a minimum.** If `x` minimizes the polynomial `g` on `[0, 1]`, then
`(L g)(x) ≥ 0`. -/
theorem genL_eval_nonneg_of_isMinOn (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {g : ℝ[X]} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hmin : IsMinOn (fun y => g.eval y) (Icc 0 1) x) :
    0 ≤ (genL κ a b g).eval x := by
  rw [eval_genL]
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · -- left endpoint
    subst h0
    have hd : 0 ≤ (derivative g).eval 0 := by
      refine hasDerivAt_nonneg_of_isMinOn_Icc_left (d := 1) one_pos ?_ (g.hasDerivAt 0)
      simpa using hmin
    simp only [sub_zero, mul_zero, zero_mul, zero_add, mul_one]
    positivity
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · -- right endpoint
    subst h1
    have hd : (derivative g).eval 1 ≤ 0 := by
      refine hasDerivAt_nonpos_of_isMinOn_Icc_right (d := 1) one_pos ?_ (g.hasDerivAt 1)
      simpa using hmin
    simp only [sub_self, mul_zero, zero_mul, zero_add, mul_one]
    nlinarith
  · -- interior
    have hloc : IsLocalMin (fun y => g.eval y) x := hmin.isLocalMin (Icc_mem_nhds h0 h1)
    have hd : (derivative g).eval x = 0 := hloc.hasDerivAt_eq_zero (g.hasDerivAt x)
    have hdd := eval_derivative_derivative_nonneg_of_isMinOn ⟨h0, h1⟩ hmin
    rw [hd, mul_zero, add_zero]
    have : 0 ≤ x * (1 - x) := mul_nonneg h0.le (by linarith)
    positivity

/-! ### The maximum principle -/

/-- The strict form: `(semi t p).eval x + ε (1 + t) > 0` on `[0, ∞) × [0, 1]`. -/
theorem semi_eval_add_pos (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ[X]}
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ p.eval x) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) : 0 < (semi κ a b T p).eval x₀ + ε * (1 + T) := by
  set v : ℝ × ℝ → ℝ := fun z => (semi κ a b z.1 p).eval z.2 + ε * (1 + z.1) with hv
  have hvc : Continuous v :=
    (continuous_eval_semi_uncurry κ a b p).add (continuous_const.mul (continuous_const.add
      continuous_fst))
  by_contra hcon
  push Not at hcon
  set K := (Icc 0 T ×ˢ Icc (0 : ℝ) 1) ∩ {z | v z ≤ 0} with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le hvc continuous_const)
  set S := Prod.fst '' K with hS
  have hSc : IsCompact S := hKc.image continuous_fst
  have hSne : S.Nonempty := ⟨T, (T, x₀), ⟨⟨⟨hT, le_rfl⟩, hx₀⟩, hcon⟩, rfl⟩
  set ts := sInf S with hts
  have htsS : ts ∈ S := hSc.sInf_mem hSne
  obtain ⟨z, ⟨⟨htK', hxs'⟩, hvs'⟩, hz⟩ := htsS
  set t' := ts
  set xs := z.2
  have hzeq : z = (t', xs) := Prod.ext hz rfl
  have htK : t' ∈ Icc 0 T := hz ▸ htK'
  have hxs : xs ∈ Icc (0 : ℝ) 1 := hxs'
  have hvs : v (t', xs) ≤ 0 := hzeq ▸ hvs'
  -- before `ts`, `v > 0`
  have hbefore : ∀ t ∈ Icc 0 T, t < t' → ∀ y ∈ Icc (0 : ℝ) 1, 0 < v (t, y) := by
    intro t ht htt y hy
    by_contra hle
    push Not at hle
    have : t ∈ S := ⟨(t, y), ⟨⟨ht, hy⟩, hle⟩, rfl⟩
    have := csInf_le hSc.bddBelow this
    linarith
  -- `ts > 0`
  have hts0 : 0 < t' := by
    rcases eq_or_lt_of_le htK.1 with h | h
    · exfalso
      have : 0 < v (t', xs) := by
        rw [← h]
        simp only [hv, semi_zero_time, add_zero, mul_one]
        linarith [hp xs hxs]
      linarith
    · exact h
  -- `v (ts, ·) ≥ 0` on `[0, 1]`
  have hge : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ v (t', y) := by
    intro y hy
    have hcont : ContinuousWithinAt (fun t => v (t, y)) (Iio t') t' :=
      (hvc.comp (continuous_id.prodMk continuous_const)).continuousWithinAt
    have hev : ∀ᶠ t in 𝓝[<] t', 0 ≤ v (t, y) := by
      have : Ioo 0 t' ∈ 𝓝[<] t' := Ioo_mem_nhdsLT hts0
      filter_upwards [this] with t ht
      exact (hbefore t ⟨ht.1.le, ht.2.le.trans htK.2⟩ ht.2 y hy).le
    exact ge_of_tendsto hcont hev
  -- the polynomial `g = v (ts, ·)` is minimized at `xs`
  set g : ℝ[X] := semi κ a b t' p + C (ε * (1 + t')) with hg
  have hgeval : ∀ y, g.eval y = v (t', y) := fun y => by simp [hg, hv]
  have hgmin : IsMinOn (fun y => g.eval y) (Icc 0 1) xs := by
    intro y hy
    simp only [mem_ofPred_eq, hgeval]
    exact le_trans hvs (hge y hy)
  have hLg := genL_eval_nonneg_of_isMinOn hκ ha hb hxs hgmin
  have hLg' : genL κ a b g = genL κ a b (semi κ a b t' p) := by
    rw [hg, map_add, genL_C, add_zero]
  rw [hLg'] at hLg
  -- time derivative at `ts`
  have hder : HasDerivAt (fun t => v (t, xs)) ((genL κ a b (semi κ a b t' p)).eval xs + ε) t' := by
    have h1 := hasDerivAt_eval_semi κ a b p xs t'
    have h2 : HasDerivAt (fun t : ℝ => ε * (1 + t)) ε t' := by
      simpa using ((hasDerivAt_id t').const_add 1).const_mul ε
    exact h1.add h2
  have hmin_t : IsMinOn (fun t => v (t, xs)) (Icc (t' - t') t') t' := by
    intro t ht
    simp only [mem_ofPred_eq]
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
    · rw [sub_self] at ht
      exact hvs.trans (hbefore t ⟨ht.1, ht.2.trans htK.2⟩ h xs hxs).le
  have := hasDerivAt_nonpos_of_isMinOn_Icc_right hts0 hmin_t hder
  linarith

/-- **Positivity of the Jacobi semigroup**: if `p ≥ 0` on `[0, 1]` then `semi t p ≥ 0` on `[0, 1]`
for every `t ≥ 0`. -/
theorem semi_eval_nonneg (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ[X]}
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ p.eval x) {t : ℝ} (ht : 0 ≤ t) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ (semi κ a b t p).eval x := by
  by_contra hneg
  push Not at hneg
  set ε := -(semi κ a b t p).eval x / (2 * (1 + t)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have h := semi_eval_add_pos hκ ha hb hp hε0 ht hx
  have : ε * (1 + t) = -(semi κ a b t p).eval x / 2 := by
    rw [hε]; field_simp
  linarith

/-- Monotonicity. -/
theorem semi_eval_le_semi_eval (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {p q : ℝ[X]}
    (hpq : ∀ x ∈ Icc (0 : ℝ) 1, p.eval x ≤ q.eval x) {t : ℝ} (ht : 0 ≤ t) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : (semi κ a b t p).eval x ≤ (semi κ a b t q).eval x := by
  have h := semi_eval_nonneg hκ ha hb (p := q - p) (fun y hy => by
    simp only [eval_sub]; linarith [hpq y hy]) ht hx
  have e : semi κ a b t (q - p) = semi κ a b t q - semi κ a b t p := by
    rw [sub_eq_add_neg, semi_add, ← neg_one_smul ℝ p, semi_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [e, eval_sub] at h
  linarith

/-- **Contraction** for the sup norm on `[0, 1]`. -/
theorem abs_semi_eval_le (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ[X]} {M : ℝ}
    (hp : ∀ x ∈ Icc (0 : ℝ) 1, |p.eval x| ≤ M) {t : ℝ} (ht : 0 ≤ t) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : |(semi κ a b t p).eval x| ≤ M := by
  have h1 := semi_eval_le_semi_eval hκ ha hb (p := p) (q := C M)
    (fun y hy => by simp only [eval_C]; exact (le_abs_self _).trans (hp y hy)) ht hx
  have h2 := semi_eval_le_semi_eval hκ ha hb (p := C (-M)) (q := p)
    (fun y hy => by simp only [eval_C]; linarith [neg_abs_le (p.eval y), hp y hy]) ht hx
  rw [semi_C, eval_C] at h1 h2
  exact abs_le.2 ⟨by linarith, h1⟩

end JacobiExists

end Sec2

end InteractingSLE
