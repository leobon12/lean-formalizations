/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Topology.SimplyConnected
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Aux. lemma 57, abstract part: continuous logarithms on a square and secant functions

Packet PROVE-PRIMEEND (specification Aux. lemma 57, `source/spec/p241-288.md#aux-57`, pp. 254–256).

The proof of Aux. 57 in `Aux57.lean` compares the canonical logarithm of `g′` along a path `γ` with the
**secant function** `S(z, w) = (g(z) − g(w))/(z − w)` (`= g′(z)` on the diagonal) on the square
`(t, s) ↦ S(γ(t), γ(s))`: a continuous logarithm of `S` on the square restricts on the diagonal to a logarithm
of `g′ ∘ γ`, and on the two edges through the corner `(1, 0)` it is the principal logarithm when `S` stays in
the slit plane there. This file proves the abstract ingredients:

* `exists_int_eqOn_of_exp_eq` : two continuous logarithms of one function on a preconnected set differ by one
  constant `2πin`;
* `div_mem_slitPlane_of_mem_H` : the quotient of two points of `ℍ` lies in the slit plane;
* `exists_log_square` (**the square lemma**) : a continuous nonvanishing `F` on `[0, 1]²` has a continuous
  logarithm `Λ`; if `F(t, 0)` and `F(1, s)` lie in the slit plane, then `Λ(1, 1) − Λ(0, 0) = Log F(1, 1) −
  Log F(0, 0)`;
* `continuousAt_dslope_prod` : the difference quotient `(z, w) ↦ dslope f w z` of a holomorphic function is
  jointly continuous (mean value inequality near the diagonal).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

/-! ### Continuous logarithms -/

/-- **Two continuous logarithms of one function on a preconnected set differ by one constant `2πin`.** -/
theorem exists_int_eqOn_of_exp_eq {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {f₁ f₂ : X → ℂ} (h₁ : ContinuousOn f₁ s) (h₂ : ContinuousOn f₂ s)
    (he : ∀ x ∈ s, exp (f₁ x) = exp (f₂ x)) : ∃ n : ℤ, ∀ x ∈ s, f₁ x = f₂ x + n * (2 * π * I) := by
  have hn : ∀ x ∈ s, ∃ n : ℤ, f₁ x = f₂ x + n * (2 * π * I) := fun x hx =>
    exp_eq_exp_iff_exists_int.1 (he x hx)
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx => hx.elim⟩
  set f : X → ℝ := fun x => (f₁ x - f₂ x).im / (2 * π) with hf_def
  have hfn : ∀ x ∈ s, ∀ n : ℤ, f₁ x = f₂ x + n * (2 * π * I) → f x = n := by
    intro x _ n hxn
    simp only [hf_def, hxn, add_sub_cancel_left, mul_im, intCast_re, intCast_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    field_simp
    ring
  have hfc : ContinuousOn f s := (continuous_im.comp_continuousOn (h₁.sub h₂)).div_const _
  have hmaps : MapsTo f s (range ((↑) : ℤ → ℝ)) := by
    intro x hx
    obtain ⟨n, hxn⟩ := hn x hx
    exact ⟨n, (hfn x hx n hxn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  obtain ⟨n₀, hn₀⟩ := hn x₀ hx₀
  refine ⟨n₀, fun x hx => ?_⟩
  obtain ⟨n, hxn⟩ := hn x hx
  have hconst := hs.constant_of_mapsTo hdisc hfc hmaps hx hx₀
  rw [hfn x hx n hxn, hfn x₀ hx₀ n₀ hn₀, Int.cast_inj] at hconst
  rw [hxn, hconst]

/-- A continuous logarithm of a function with values in the slit plane is the principal logarithm up to one
constant `2πin`. -/
theorem exists_int_eqOn_log {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {Λ F : X → ℂ} (hΛ : ContinuousOn Λ s) (hF : ContinuousOn F s) (hFs : ∀ x ∈ s, F x ∈ slitPlane)
    (he : ∀ x ∈ s, exp (Λ x) = F x) : ∃ n : ℤ, ∀ x ∈ s, Λ x = log (F x) + n * (2 * π * I) := by
  refine exists_int_eqOn_of_exp_eq hs hΛ (fun x hx => ?_) fun x hx => ?_
  · exact ((hF x hx).clog (hFs x hx))
  · rw [he x hx, exp_log (slitPlane_ne_zero (hFs x hx))]

/-! ### Quotients of points of the upper half-plane -/

/-- The quotient of two points of `ℍ` lies in the slit plane (its argument is in `(−π, π)`). -/
theorem div_mem_slitPlane_of_mem_H {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) : a / b ∈ slitPlane := by
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_im] at hb; exact lt_irrefl _ hb
  rw [mem_slitPlane_iff]
  by_contra hcon
  obtain ⟨hre', him'⟩ := not_or.1 hcon
  have hre : (a / b).re ≤ 0 := not_lt.1 hre'
  have him : (a / b).im = 0 := not_not.1 him'
  have hab : a = a / b * b := by field_simp
  have him2 : a.im = (a / b).re * b.im := by
    conv_lhs => rw [hab]
    rw [mul_im, him, zero_mul, add_zero]
  have : (a / b).re * b.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hre hb.le
  linarith

/-- The quotient of two points of the lower half-plane lies in the slit plane. -/
theorem div_mem_slitPlane_of_im_neg {a b : ℂ} (ha : a.im < 0) (hb : b.im < 0) : a / b ∈ slitPlane := by
  have := div_mem_slitPlane_of_mem_H (a := -a) (b := -b) (by simpa using ha) (by simpa using hb)
  rwa [neg_div_neg_eq] at this

/-! ### The square lemma -/

/-- The clamp `t ↦ max 0 (min t 1)` onto `[0, 1]`. -/
def clampUnit (t : ℝ) : ℝ := max 0 (min t 1)

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampUnit_mem (t : ℝ) : clampUnit t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clampUnit_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampUnit t = t := by
  simp [clampUnit, ht.1, ht.2]

/-- **A continuous nonvanishing function on the square `[0, 1]²` has a continuous logarithm** (the plane is simply
connected; extend `F` by clamping). -/
theorem exists_continuous_log_square {F : ℝ → ℝ → ℂ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hF0 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F t s ≠ 0) :
    ∃ Λ : ℝ → ℝ → ℂ, Continuous (fun p : ℝ × ℝ => Λ p.1 p.2) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, exp (Λ t s) = F t s := by
  set c : ℂ → ℝ × ℝ := fun z => (clampUnit z.re, clampUnit z.im) with hc
  have hcc : Continuous c :=
    (continuous_clampUnit.comp continuous_re).prodMk (continuous_clampUnit.comp continuous_im)
  have hcm : ∀ z, c z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun z => ⟨clampUnit_mem _, clampUnit_mem _⟩
  set G : ℂ → ℂ := fun z => F (c z).1 (c z).2 with hG
  have hGc : ContinuousOn G univ := by
    rw [continuousOn_univ]
    exact hF.comp_continuous hcc hcm
  have hG0 : (0 : ℂ) ∉ G '' univ := by
    rintro ⟨z, -, hz⟩
    exact hF0 _ (hcm z).1 _ (hcm z).2 hz
  obtain ⟨f, hfc, hf⟩ := exists_continuousOn_eqOn_exp_comp isSimplyConnected_univ isOpen_univ hGc hG0
  have hfc' : Continuous f := continuousOn_univ.1 hfc
  refine ⟨fun t s => f (t + s * I), hfc'.comp (by fun_prop), fun t ht s hs => ?_⟩
  have h : exp (f ((t : ℂ) + s * I)) = G ((t : ℂ) + s * I) := hf (mem_univ ((t : ℂ) + s * I))
  rw [h]
  simp [hG, hc, clampUnit_of_mem ht, clampUnit_of_mem hs]

/-- **The square lemma.** Let `F` be continuous and nonvanishing on `[0, 1]²`, with values in the slit plane on
the bottom edge `s = 0` and on the right edge `t = 1`. Then `F` has a continuous logarithm `Λ` on the square, and
`Λ(1, 1) − Λ(0, 0) = Log F(1, 1) − Log F(0, 0)` (follow the two edges through `(1, 0)`, where `Λ` is the principal
logarithm up to one constant). -/
theorem exists_log_square {F : ℝ → ℝ → ℂ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hF0 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F t s ≠ 0)
    (hbot : ∀ t ∈ Icc (0 : ℝ) 1, F t 0 ∈ slitPlane) (hright : ∀ s ∈ Icc (0 : ℝ) 1, F 1 s ∈ slitPlane) :
    ∃ Λ : ℝ → ℝ → ℂ, Continuous (fun p : ℝ × ℝ => Λ p.1 p.2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, exp (Λ t s) = F t s) ∧
      Λ 1 1 - Λ 0 0 = log (F 1 1) - log (F 0 0) := by
  obtain ⟨Λ, hΛc, hΛ⟩ := exists_continuous_log_square hF hF0
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- the bottom edge
  have hb1 : ContinuousOn (fun t => Λ t 0) (Icc 0 1) :=
    (hΛc.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hb2 : ContinuousOn (fun t => F t 0) (Icc 0 1) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht => ⟨ht, h01⟩
  obtain ⟨n₁, hn₁⟩ := exists_int_eqOn_log isPreconnected_Icc hb1 hb2 hbot fun t ht => hΛ t ht 0 h01
  -- the right edge
  have hr1 : ContinuousOn (fun s => Λ 1 s) (Icc 0 1) :=
    (hΛc.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hr2 : ContinuousOn (fun s => F 1 s) (Icc 0 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨h11, hs⟩
  obtain ⟨n₂, hn₂⟩ := exists_int_eqOn_log isPreconnected_Icc hr1 hr2 hright fun s hs => hΛ 1 h11 s hs
  have e₁ := hn₁ 1 h11
  have e₂ := hn₂ 0 h01
  have e₀ := hn₁ 0 h01
  have e₃ := hn₂ 1 h11
  have hn : (n₁ : ℂ) * (2 * π * I) = n₂ * (2 * π * I) := by
    have := e₁.symm.trans e₂
    linear_combination this
  refine ⟨Λ, hΛc, hΛ, ?_⟩
  rw [e₃, e₀]
  linear_combination (-1 : ℂ) * hn

/-! ### The secant function -/

/-- **Joint continuity of the difference quotient**: for `f` holomorphic on an open `Ω`, the map
`(z, w) ↦ dslope f w z` (`= (f z − f w)/(z − w)`, `= f′(z)` on the diagonal) is continuous at every point of
`Ω × Ω`. Off the diagonal it is a quotient of continuous functions; at `(c, c)` the mean value inequality for
`f − f′(c) · id` on a small ball gives `|dslope f w z − f′(c)| ≤ sup |f′ − f′(c)|`. -/
theorem continuousAt_dslope_prod {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {a b : ℂ} (ha : a ∈ Ω) (hb : b ∈ Ω) : ContinuousAt (fun q : ℂ × ℂ => dslope f q.2 q.1) (a, b) := by
  rcases ne_or_eq a b with hab | rfl
  · -- off the diagonal
    have hne : ∀ᶠ p : ℂ × ℂ in 𝓝 (a, b), p.1 ≠ p.2 :=
      (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hab
    have hfa : ContinuousAt f a := ((hf a ha).differentiableAt (hΩ.mem_nhds ha)).continuousAt
    have hfb : ContinuousAt f b := ((hf b hb).differentiableAt (hΩ.mem_nhds hb)).continuousAt
    have hcont : ContinuousAt (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹ * (f p.1 - f p.2)) (a, b) := by
      refine ((continuous_fst.sub continuous_snd).continuousAt.inv₀ (sub_ne_zero.2 hab)).mul ?_
      exact (hfa.comp continuous_fst.continuousAt).sub (hfb.comp continuous_snd.continuousAt)
    refine hcont.congr ?_
    filter_upwards [hne] with p hp
    rw [dslope_of_ne _ hp, slope_def_field, div_eq_inv_mul]
  · -- on the diagonal
    have hd : DifferentiableOn ℂ (deriv f) Ω := hf.deriv hΩ
    have hdc : ContinuousAt (deriv f) a := ((hd a ha).differentiableAt (hΩ.mem_nhds ha)).continuousAt
    rw [ContinuousAt, dslope_same, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hδ₀Ω⟩ := Metric.isOpen_iff.1 hΩ a ha
    obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.continuousAt_iff.1 hdc (ε / 2) (half_pos hε)
    set δ := min δ₀ δ₁ with hδ
    have hδpos : 0 < δ := lt_min hδ₀ hδ₁
    have hball : ∀ u ∈ ball a δ, u ∈ Ω ∧ ‖deriv f u - deriv f a‖ < ε / 2 := fun u hu => by
      have hu' : dist u a < δ := hu
      refine ⟨hδ₀Ω (mem_ball.2 (hu'.trans_le (min_le_left _ _))), ?_⟩
      rw [← dist_eq_norm]
      exact hδ₁c (hu'.trans_le (min_le_right _ _))
    refine Filter.mem_of_superset (ball_mem_nhds (a, a) hδpos) fun p hp => ?_
    have hp1 : p.1 ∈ ball a δ := by
      have := (Prod.dist_eq (x := p) (y := (a, a))) ▸ (mem_ball.1 hp)
      exact mem_ball.2 (lt_of_le_of_lt (le_max_left _ _) this)
    have hp2 : p.2 ∈ ball a δ := by
      have := (Prod.dist_eq (x := p) (y := (a, a))) ▸ (mem_ball.1 hp)
      exact mem_ball.2 (lt_of_le_of_lt (le_max_right _ _) this)
    show dist (dslope f p.2 p.1) (deriv f a) < ε
    rw [dist_eq_norm]
    rcases eq_or_ne p.1 p.2 with heq | hne
    · rw [heq, dslope_same]
      exact (hball p.2 hp2).2.trans (half_lt_self hε)
    · -- the mean value inequality for `f − f′(a) · id` on the ball
      set h : ℂ → ℂ := fun u => f u - deriv f a * u with hh
      have hdiff : ∀ u ∈ ball a δ, DifferentiableAt ℂ h u := fun u hu =>
        ((hf u (hball u hu).1).differentiableAt (hΩ.mem_nhds (hball u hu).1)).sub
          ((differentiableAt_id).const_mul _)
      have hderiv : ∀ u ∈ ball a δ, ‖deriv h u‖ ≤ ε / 2 := fun u hu => by
        have hfu : DifferentiableAt ℂ f u := (hf u (hball u hu).1).differentiableAt
          (hΩ.mem_nhds (hball u hu).1)
        have : HasDerivAt h (deriv f u - deriv f a * 1) u :=
          hfu.hasDerivAt.sub ((hasDerivAt_id u).const_mul (deriv f a))
        rw [this.deriv, mul_one]; exact (hball u hu).2.le
      have hmv := (convex_ball a δ).norm_image_sub_le_of_norm_deriv_le hdiff hderiv hp2 hp1
      have hz : p.1 - p.2 ≠ 0 := sub_ne_zero.2 hne
      have hslope : dslope f p.2 p.1 - deriv f a = (h p.1 - h p.2) / (p.1 - p.2) := by
        rw [dslope_of_ne _ hne, slope_def_field, hh]
        field_simp
        ring
      rw [hslope, norm_div]
      calc ‖h p.1 - h p.2‖ / ‖p.1 - p.2‖ ≤ ε / 2 * ‖p.1 - p.2‖ / ‖p.1 - p.2‖ := by
            gcongr
        _ = ε / 2 := by field_simp [norm_ne_zero_iff.2 hz]
        _ < ε := half_lt_self hε

/-- `continuousAt_dslope_prod` on `Ω × Ω`. -/
theorem continuousOn_dslope_prod {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.2 p.1) (Ω ×ˢ Ω) := fun _ hp =>
  (continuousAt_dslope_prod hΩ hf hp.1 hp.2).continuousWithinAt

/-- **The mean value bound for the secant on a convex set**: if `‖f′ − c‖ ≤ ε` on a convex open `U` where `f` is
holomorphic, then `‖dslope f w z − c‖ ≤ ε` for `z, w ∈ U`. -/
theorem norm_dslope_sub_le {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : DifferentiableOn ℂ f U) {c : ℂ} {ε : ℝ} (hε : ∀ u ∈ U, ‖deriv f u - c‖ ≤ ε) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) : ‖dslope f w z - c‖ ≤ ε := by
  rcases eq_or_ne z w with rfl | hne
  · rw [dslope_same]; exact hε z hz
  set h : ℂ → ℂ := fun u => f u - c * u with hh
  have hdiff : ∀ u ∈ U, DifferentiableAt ℂ h u := fun u hu =>
    ((hf u hu).differentiableAt (hU.mem_nhds hu)).sub ((differentiableAt_id).const_mul _)
  have hderiv : ∀ u ∈ U, ‖deriv h u‖ ≤ ε := fun u hu => by
    have hfu : DifferentiableAt ℂ f u := (hf u hu).differentiableAt (hU.mem_nhds hu)
    have : HasDerivAt h (deriv f u - c * 1) u := hfu.hasDerivAt.sub ((hasDerivAt_id u).const_mul c)
    rw [this.deriv, mul_one]; exact hε u hu
  have hmv := hUc.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hw hz
  have hzw : z - w ≠ 0 := sub_ne_zero.2 hne
  have hslope : dslope f w z - c = (h z - h w) / (z - w) := by
    rw [dslope_of_ne _ hne, slope_def_field, hh]
    field_simp
    ring
  rw [hslope, norm_div]
  rw [div_le_iff₀ (norm_pos_iff.2 hzw)]
  exact hmv

end Sec7

end InteractingSLE
