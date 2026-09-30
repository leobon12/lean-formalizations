import QuantumZipper.Proofs.Complex.BasicsReflection
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Schwarz reflection for holomorphic maps (task FL3-REFL)

Foundation for the conformal transport of the excursion-flux symmetry (Field–Lawler,
`FLImageSumBoundStmt`).

* **(R1)** `fl3Refl_real`: `F` holomorphic on `ℍ ∩ B(x, r)`, continuous on `ℍ̄ ∩ B(x, r)`, real on
  `ℝ ∩ B(x, r)` extends to a holomorphic `G` on `B(x, r)` with `G ∘ conj = conj ∘ G`, and `G'` is
  real on `ℝ ∩ B(x, r)`. If moreover `Im F > 0` on `ℍ ∩ B(x, r)` then `G'(x) ≠ 0`
  (`fl3Refl_real_pos`).
* **(R2)** `fl3Refl_arc`, `fl3Refl_arc_pos`: the same for `F ∘ ψ`, where `ψ` is holomorphic on
  `B(x, r)`, maps `ℍ ∩ B(x, r)` into the domain `Ω` of `F`, and `F` is real on the arc
  `ψ(ℝ ∩ B(x, r))`.

Sources. The extension is the Schwarz reflection principle (Ahlfors, *Complex Analysis*, 3rd ed.
1979, Ch. 4 §6.5, Theorem 24, p. 172), already proved in the repository as
`CA.exists_reflection_extension` (`Proofs/Complex/BasicsReflection.lean`, via Morera). The reality
of `G'` on `ℝ` is differentiation of `G(z̄) = conj G(z)`. For `G'(x) ≠ 0` we use the local normal
form `G(z) - G(x) = (z - x)^k g(z)`, `g(x) ≠ 0` (Ahlfors Ch. 4 §3.3, p. 131 ff., mathlib
`AnalyticAt.analyticOrderAt_eq_natCast`): if `k ≥ 2` a ray from `x` into `ℍ` with suitable angle
`θ ∈ (0, π)` (possible since `kθ` sweeps `(0, 2π)`) has `Im G < 0` near `x` (own elementary proof
of this standard step).

Note. Injectivity of `F` on the `Ω`-side alone does **not** give `G'(x) ≠ 0`: `F(z) = z²` is
injective on `ℍ`, real on `ℝ`, and `F'(0) = 0`. We use `Im F > 0` on the `Ω`-side instead, which
holds for a conformal map onto `ℍ`.
-/

noncomputable section

open Set Metric Filter Topology Complex Real
open scoped ComplexConjugate

namespace QuantumZipper.FieldLawler

/-- A conj-symmetric holomorphic function on `B(x, r)` has real derivative at `x`. -/
theorem fl3Refl_deriv_real {G : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (ball (x : ℂ) r))
    (hsym : ∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z)) :
    (deriv G x).im = 0 := by
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hd : HasDerivAt G (deriv G x) x :=
    (hG.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt
  have h2 := hd.conj_conj
  rw [conj_ofReal] at h2
  have heq : G =ᶠ[𝓝 (x : ℂ)] (conj ∘ G ∘ conj) := by
    filter_upwards [isOpen_ball.mem_nhds hxB] with z hz
    simp only [Function.comp_apply, hsym z hz, conj_conj]
  have := (h2.congr_of_eventuallyEq heq).unique hd
  exact conj_eq_iff_im.1 this

/-- Direction lemma: for `c ≠ 0` and `k ≥ 2` there is `u ∈ ℍ` with `Im (u^k c) < 0`. -/
theorem fl3Refl_dir (c : ℂ) (hc : c ≠ 0) (k : ℕ) (hk : 2 ≤ k) :
    ∃ u : ℂ, 0 < u.im ∧ (u ^ k * c).im < 0 := by
  -- a nonzero `w`, not on `[0, ∞)`, with `Im (w c) < 0`
  obtain ⟨w, hw0, hwarg, hwc⟩ : ∃ w : ℂ, w ≠ 0 ∧ arg w ≠ 0 ∧ (w * c).im < 0 := by
    by_cases hcase : c.re = 0 ∧ c.im < 0
    · refine ⟨1 + I, ?_, ?_, ?_⟩
      · intro h; have := congrArg Complex.im h; simp at this
      · rw [Ne, arg_eq_zero_iff]; simp
      · simp [hcase.1, hcase.2]
    · refine ⟨-I * conj c, ?_, ?_, ?_⟩
      · simpa using hc
      · rw [Ne, arg_eq_zero_iff]
        simp only [neg_mul, neg_re, mul_re, I_re, conj_re, zero_mul, I_im, conj_im, one_mul,
          zero_sub, neg_neg, neg_im, mul_im, not_and]
        intro h1 h2
        refine hcase ⟨by linarith, ?_⟩
        rcases lt_or_eq_of_le (show c.im ≤ 0 by linarith) with h | h
        · exact h
        · exact absurd (Complex.ext (by simp only [zero_re]; linarith) (by simpa using h)) hc
      · have hn : 0 < c.re ^ 2 + c.im ^ 2 := by
          rcases (ne_or_eq c.re 0) with h | h
          · positivity
          · have : c.im ≠ 0 := fun h' => hc (Complex.ext h h')
            positivity
        simp only [neg_mul, neg_im, mul_im, mul_re, I_re, conj_re, zero_mul, I_im, conj_im,
          one_mul, zero_sub]
        nlinarith
  -- the angle
  set α : ℝ := if 0 < arg w then arg w else arg w + 2 * π with hα
  have hα0 : 0 < α := by
    rw [hα]; split_ifs with h
    · exact h
    · linarith [neg_pi_lt_arg w, Real.pi_pos]
  have hα2 : α < 2 * π := by
    rw [hα]; split_ifs with h
    · linarith [arg_le_pi w, Real.pi_pos]
    · have : arg w < 0 := lt_of_le_of_ne (not_lt.1 h) hwarg
      linarith
  have hαexp : exp (α * I) = exp (arg w * I) := by
    rw [hα]; split_ifs with h
    · rfl
    · push_cast
      rw [add_mul, Complex.exp_add, exp_two_pi_mul_I, mul_one]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  set θ : ℝ := α / k with hθ
  have hθ0 : 0 < θ := div_pos hα0 hkpos
  have hθπ : θ < π := by
    rw [hθ, div_lt_iff₀ hkpos]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  refine ⟨exp (θ * I), ?_, ?_⟩
  · rw [exp_ofReal_mul_I_im]; exact Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  · have hpow : exp (θ * I) ^ k = w * ((‖w‖ : ℂ))⁻¹ := by
      rw [← Complex.exp_nat_mul, show (k : ℂ) * (θ * I) = (α : ℂ) * I by
        rw [hθ]; push_cast
        have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
        field_simp, hαexp]
      have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw0)
      have := norm_mul_exp_arg_mul_I w
      field_simp
      rw [mul_comm]; exact this
    rw [hpow, mul_comm w, mul_assoc, ← ofReal_inv, im_ofReal_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (norm_pos_iff.2 hw0)) hwc

/-- **Nonvanishing derivative.** A holomorphic `G` on `B(x, r)`, real at `x`, with `Im G > 0` on
`ℍ ∩ B(x, r)`, has `G'(x) ≠ 0`. -/
theorem fl3Refl_deriv_ne_zero {G : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (ball (x : ℂ) r)) (hx : (G x).im = 0)
    (hpos : ∀ z ∈ H ∩ ball (x : ℂ) r, 0 < (G z).im) :
    deriv G x ≠ 0 := by
  intro h0
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hA : AnalyticAt ℂ G x := (hG.analyticOnNhd isOpen_ball) x hxB
  have hT : ∀ u : ℂ, Tendsto (fun t : ℝ => (x : ℂ) + t * u) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    intro u
    have : Tendsto (fun t : ℝ => (x : ℂ) + t * u) (𝓝 0) (𝓝 ((x : ℂ) + ((0 : ℝ) : ℂ) * u)) :=
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hray : ∀ u : ℂ, 0 < u.im →
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ (x : ℂ) + t * u ∈ H ∩ ball (x : ℂ) r := by
    intro u hu
    filter_upwards [hT u (isOpen_ball.mem_nhds hxB), self_mem_nhdsWithin] with t ht htpos
    have htpos : 0 < t := htpos
    refine ⟨htpos, ?_, ht⟩
    show 0 < ((x : ℂ) + t * u).im
    simp only [add_im, ofReal_im, im_ofReal_mul, zero_add]
    positivity
  have hsum := AnalyticAt.analyticOrderAt_deriv_add_one hA
  have hord1 : analyticOrderAt (deriv G) x ≠ 0 := analyticOrderAt_ne_zero.2 ⟨hA.deriv, h0⟩
  have hA' : AnalyticAt ℂ (fun z => G z - G x) x := hA.sub analyticAt_const
  cases hk : analyticOrderAt (fun z => G z - G x) x with
  | top =>
    rw [analyticOrderAt_eq_top] at hk
    obtain ⟨t, ⟨-, ht1⟩, ht2⟩ := ((hray I (by simp)).and ((hT I).eventually hk)).exists
    have := hpos _ ht1
    rw [sub_eq_zero.1 ht2, hx] at this
    exact lt_irrefl _ this
  | coe k =>
    have hk2 : 2 ≤ k := by
      have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv G) x := Order.one_le_iff_ne_zero.2 hord1
      have h2 : ((2 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
        rw [← hk, ← hsum]
        calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ analyticOrderAt (deriv G) x + 1 := add_le_add h1 le_rfl
      exact_mod_cast h2
    obtain ⟨g, hga, hg0, hgeq⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hA').1 hk
    obtain ⟨u, hu, huc⟩ := fl3Refl_dir (g x) hg0 k hk2
    have hneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (u ^ k * g ((x : ℂ) + t * u)).im < 0 := by
      have h1 : Tendsto (fun t : ℝ => (u ^ k * g ((x : ℂ) + t * u)).im) (𝓝[>] 0)
          (𝓝 (u ^ k * g x).im) :=
        (continuous_im.tendsto _).comp (tendsto_const_nhds.mul (hga.continuousAt.tendsto.comp (hT u)))
      exact h1.eventually_lt_const huc
    obtain ⟨t, ⟨htpos, ht1⟩, ht2, ht3⟩ :=
      ((hray u hu).and (((hT u).eventually hgeq).and hneg)).exists
    have hzx : (x : ℂ) + t * u - x = t * u := by ring
    have he : G ((x : ℂ) + t * u) = G x + (((t ^ k : ℝ)) : ℂ) * (u ^ k * g ((x : ℂ) + t * u)) := by
      have := ht2
      simp only [hzx, smul_eq_mul] at this
      push_cast
      linear_combination this
    have := hpos _ ht1
    rw [he, add_im, hx, zero_add, im_ofReal_mul] at this
    exact absurd this (not_lt.2 (mul_neg_of_pos_of_neg (pow_pos htpos k) ht3).le)

/-- **(R1) Schwarz reflection across a real interval.** -/
theorem fl3Refl_real {F : ℂ → ℂ} {x r : ℝ}
    (hd : DifferentiableOn ℂ F (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn F (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (F z).im = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (x : ℂ) r) ∧ EqOn G F (Hbar ∩ ball (x : ℂ) r) ∧
      (∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z)) ∧
      ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → (deriv G t).im = 0 := by
  obtain ⟨G, hG, hGF, hsym⟩ := CA.exists_reflection_extension hd hc hreal
  refine ⟨G, hG, hGF, hsym, fun t ht => ?_⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 isOpen_ball (t : ℂ) ht
  exact fl3Refl_deriv_real hρ (hG.mono hsub) fun z hz => hsym z (hsub hz)

/-- **(R1) with nonvanishing derivative**: if moreover `Im F > 0` on `ℍ ∩ B(x, r)`, the
extension has `G'(x) ≠ 0`. -/
theorem fl3Refl_real_pos {F : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ F (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn F (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (F z).im = 0)
    (hpos : ∀ z ∈ H ∩ ball (x : ℂ) r, 0 < (F z).im) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (x : ℂ) r) ∧ EqOn G F (Hbar ∩ ball (x : ℂ) r) ∧
      (∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z)) ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → (deriv G t).im = 0) ∧ deriv G x ≠ 0 := by
  obtain ⟨G, hG, hGF, hsym, hder⟩ := fl3Refl_real hd hc hreal
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  refine ⟨G, hG, hGF, hsym, hder, fl3Refl_deriv_ne_zero hr hG ?_ ?_⟩
  · rw [hGF ⟨show (0 : ℝ) ≤ (x : ℂ).im by simp, hxB⟩]
    exact hreal _ hxB (by simp)
  · intro z hz
    rw [hGF ⟨show (0 : ℝ) ≤ z.im from le_of_lt hz.1, hz.2⟩]
    exact hpos z hz

/-- **(R2) with nonvanishing derivative**, when `Im F > 0` on `ψ(ℍ ∩ B(x, r))`. -/
theorem fl3Refl_arc_pos {F ψ : ℂ → ℂ} {Ω : Set ℂ} {x r : ℝ} (hr : 0 < r)
    (hψ : DifferentiableOn ℂ ψ (ball (x : ℂ) r))
    (hψΩ : MapsTo ψ (H ∩ ball (x : ℂ) r) Ω) (hF : DifferentiableOn ℂ F Ω)
    (hFc : ContinuousOn F (ψ '' (Hbar ∩ ball (x : ℂ) r)))
    (hreal : ∀ w ∈ ψ '' {z | z ∈ ball (x : ℂ) r ∧ z.im = 0}, (F w).im = 0)
    (hpos : ∀ z ∈ H ∩ ball (x : ℂ) r, 0 < (F (ψ z)).im) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (x : ℂ) r) ∧
      EqOn G (F ∘ ψ) (Hbar ∩ ball (x : ℂ) r) ∧
      (∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z)) ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → (deriv G t).im = 0) ∧ deriv G x ≠ 0 :=
  fl3Refl_real_pos hr (hF.comp (hψ.mono inter_subset_right) hψΩ)
    (hFc.comp (hψ.continuousOn.mono inter_subset_right) (mapsTo_image _ _))
    (fun z hz hz0 => hreal _ ⟨z, ⟨hz, hz0⟩, rfl⟩) hpos

end QuantumZipper.FieldLawler
