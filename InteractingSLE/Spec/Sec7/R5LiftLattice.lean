/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.Pushforward
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# Lemma R.5's common phase: lattice limits of lift differences

Packet PROVE-R5-LIFT. Lemma R.5's proof (spec p. 475) reads a reference germ in the current chart through a
transition that "reflects across the base with positive derivative"; the inherited logarithm is then transported
exactly, up to `2π`-multiples. This file proves the analytic core of that step, for arbitrary charts:

* `nhdsWithin_H_neBot`, **`continuousOn_of_tendsto_nhdsWithin_H`**: a function with a limit within `ℍ` at every point
  of a real set `J` has a continuous limit function on `J`;
* **`exists_int_eq_of_isPreconnected`**: a continuous `2πℤ`-valued function on a preconnected set is constant;
* **`exists_int_tendsto_im_of_exp_mul_eq_one`**: if `exp φ · D = 1` near a real point `ξ` and `D → c > 0`, then
  `Im φ → 2πn` for an integer `n`;
* **`exists_int_tendsto_lift_sub`**: for a conformal chart `cur` with an analytic derivative logarithm and any map `g`
  with an analytic derivative logarithm `Lg`, if the transition `g ∘ cur⁻¹` has a positive reflected derivative at
  `ξ` (its derivative tends to `c > 0` within `ℍ`), then the lift difference `lift_cur − Im Lg` read through `cur⁻¹`
  tends to `2πn`;
* **`exists_int_forall_tendsto_lift_sub`**: on a preconnected real set at every point of which the transition has a
  positive reflected derivative, the integer is the same at every point (the common phase on one connected interval).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H isOpen_H)

namespace InteractingSLE.Sec7.R5Lift

/-! ### Boundary limits on real sets -/

theorem nhdsWithin_H_neBot (ξ : ℝ) : (𝓝[H] (ξ : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 ?_
  have h : closure H = {z : ℂ | 0 ≤ z.im} := Complex.closure_setOfPred_lt_im 0
  rw [h]
  simp

/-- **A boundary-limit function is continuous**: if `f` has the limit `Lf ξ` within `ℍ` at every point `ξ` of a real
set `J`, then `Lf` is continuous on `J`. -/
theorem continuousOn_of_tendsto_nhdsWithin_H {f : ℂ → ℝ} {Lf : ℝ → ℝ} {J : Set ℝ}
    (hf : ∀ ξ ∈ J, Tendsto f (𝓝[H] (ξ : ℂ)) (𝓝 (Lf ξ))) : ContinuousOn Lf J := by
  intro ξ₀ hξ₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hf ξ₀ hξ₀) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {ξ} hξ hdist => ?_⟩
  have := nhdsWithin_H_neBot ξ
  have hball : ball (ξ : ℂ) (δ - dist ξ ξ₀) ∈ 𝓝 (ξ : ℂ) := ball_mem_nhds _ (sub_pos.2 hdist)
  have hev : ∀ᶠ y in 𝓝[H] (ξ : ℂ), dist (f y) (Lf ξ₀) ≤ ε / 2 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with y hyH hyb
    have hy : dist y (ξ₀ : ℂ) < δ := by
      have h1 := dist_triangle y (ξ : ℂ) (ξ₀ : ℂ)
      have h2 : dist (ξ : ℂ) (ξ₀ : ℂ) = dist ξ ξ₀ := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
      rw [mem_ball] at hyb
      linarith
    exact (hδf hyH hy).le
  have hle := le_of_tendsto ((hf ξ hξ).dist tendsto_const_nhds) hev
  linarith

/-- **A continuous `2πℤ`-valued function on a preconnected set is constant.** -/
theorem exists_int_eq_of_isPreconnected {g : ℝ → ℝ} {J : Set ℝ} (hJ : IsPreconnected J) (hg : ContinuousOn g J)
    (hint : ∀ ξ ∈ J, ∃ n : ℤ, g ξ = 2 * Real.pi * n) : ∃ n : ℤ, ∀ ξ ∈ J, g ξ = 2 * Real.pi * n := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, fun ξ hξ => hξ.elim⟩
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  set f : ℝ → ℝ := fun ξ => g ξ / (2 * Real.pi) with hf
  have hfn : ∀ ξ (n : ℤ), g ξ = 2 * Real.pi * n → f ξ = n := fun ξ n h => by
    rw [hf]; simp only; rw [h]; field_simp
  have hfc : ContinuousOn f J := hg.div_const _
  have hmaps : MapsTo f J (range ((↑) : ℤ → ℝ)) := fun ξ hξ => by
    obtain ⟨n, hn⟩ := hint ξ hξ
    exact ⟨n, (hfn ξ n hn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  obtain ⟨n₀, hn₀⟩ := hint ξ₀ hξ₀
  refine ⟨n₀, fun ξ hξ => ?_⟩
  obtain ⟨n, hn⟩ := hint ξ hξ
  have hconst := hJ.constant_of_mapsTo hdisc hfc hmaps hξ hξ₀
  rw [hfn ξ n hn, hfn ξ₀ n₀ hn₀, Int.cast_inj] at hconst
  rw [hn, hconst]

/-! ### The lattice limit at a positive reflected derivative -/

/-- **The lattice limit**: if `exp φ · D = 1` on `ℍ ∩ B(ξ, r)` with `φ, D` continuous there and `D → c > 0` within
`ℍ` at `ξ`, then `Im φ → 2πn` for some integer `n` (a continuous logarithm of `1/D` near a positive value). -/
theorem exists_int_tendsto_im_of_exp_mul_eq_one {φ D : ℂ → ℂ} {ξ : ℂ} {r c : ℝ} (hr : 0 < r)
    (hφ : ContinuousOn φ (H ∩ ball ξ r)) (hD : ContinuousOn D (H ∩ ball ξ r))
    (hexp : ∀ y ∈ H ∩ ball ξ r, exp (φ y) * D y = 1)
    (hlim : Tendsto D (𝓝[H] ξ) (𝓝 (c : ℂ))) (hc : 0 < c) :
    ∃ n : ℤ, Tendsto (fun y => (φ y).im) (𝓝[H] ξ) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨ρ, hρ, hρD⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim c hc
  set ρ' := min ρ r with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ hr
  set V := H ∩ ball ξ ρ' with hV
  have hVsub : V ⊆ H ∩ ball ξ r := inter_subset_inter_right _ (ball_subset_ball (min_le_right _ _))
  have hVmem : V ∈ 𝓝[H] ξ := inter_mem_nhdsWithin H (ball_mem_nhds ξ hρ'0)
  -- on `V`, `D` lies in the right half-plane
  have hDre : ∀ y ∈ V, 0 < (D y).re := fun y hy => by
    have h1 : dist (D y) (c : ℂ) < c :=
      hρD hy.1 (lt_of_lt_of_le (mem_ball.1 hy.2) (min_le_left _ _))
    have h2 : |(D y).re - c| < c := by
      have := Complex.abs_re_le_norm (D y - c)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      rw [dist_eq_norm] at h1
      linarith
    linarith [abs_lt.1 h2]
  have hslit : ∀ y ∈ V, D y ∈ slitPlane := fun y hy => Or.inl (hDre y hy)
  have hD0 : ∀ y ∈ V, D y ≠ 0 := fun y hy h => by
    have := hDre y hy; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
  -- the continuous logarithm `ψ = φ + log D` is `2πi`-valued
  set ψ : ℂ → ℂ := fun y => φ y + log (D y) with hψ
  have hψexp : ∀ y ∈ V, ∃ n : ℤ, ψ y = n * (2 * Real.pi * I) := fun y hy => by
    refine Complex.exp_eq_one_iff.1 ?_
    rw [hψ]; simp only
    rw [exp_add, exp_log (hD0 y hy)]
    exact hexp y (hVsub hy)
  have hψc : ContinuousOn ψ V := (hφ.mono hVsub).add ((hD.mono hVsub).clog hslit)
  -- `V` is preconnected
  have hVconv : Convex ℝ V := by
    refine Convex.inter ?_ (convex_ball ξ ρ')
    exact convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0
  rcases V.eq_empty_or_nonempty with hVe | ⟨y₀, hy₀⟩
  · refine ⟨0, ?_⟩
    have hbot : 𝓝[H] ξ = ⊥ := empty_mem_iff_bot.1 (hVe ▸ hVmem)
    rw [hbot]; exact tendsto_bot
  -- the imaginary part of `ψ` over `2π` is a continuous integer-valued function on `V`
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  set f : ℂ → ℝ := fun y => (ψ y).im / (2 * Real.pi) with hf
  have hfn : ∀ y (n : ℤ), ψ y = n * (2 * Real.pi * I) → f y = n := fun y n h => by
    rw [hf]; simp only; rw [h]
    simp only [mul_im, intCast_re, intCast_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    field_simp
    ring
  have hfc : ContinuousOn f V := (continuous_im.comp_continuousOn hψc).div_const _
  have hmaps : MapsTo f V (range ((↑) : ℤ → ℝ)) := fun y hy => by
    obtain ⟨n, hn⟩ := hψexp y hy
    exact ⟨n, (hfn y n hn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  obtain ⟨n₀, hn₀⟩ := hψexp y₀ hy₀
  have hall : ∀ y ∈ V, ψ y = n₀ * (2 * Real.pi * I) := fun y hy => by
    obtain ⟨n, hn⟩ := hψexp y hy
    have hconst := hVconv.isPreconnected.constant_of_mapsTo hdisc hfc hmaps hy hy₀
    rw [hfn y n hn, hfn y₀ n₀ hn₀, Int.cast_inj] at hconst
    rw [hn, hconst]
  refine ⟨n₀, ?_⟩
  have hev : ∀ᶠ y in 𝓝[H] ξ, 2 * Real.pi * n₀ - arg (D y) = (φ y).im := by
    filter_upwards [hVmem] with y hy
    have h := congrArg Complex.im (hall y hy)
    rw [hψ] at h
    simp only [add_im, log_im, mul_im, intCast_re, intCast_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
      im_ofNat] at h
    linarith
  have hcslit : (c : ℂ) ∈ slitPlane := Or.inl (by simpa using hc)
  have harg : Tendsto (fun y => arg (D y)) (𝓝[H] ξ) (𝓝 (arg (c : ℂ))) :=
    (Complex.continuousAt_arg hcslit).tendsto.comp hlim
  rw [Complex.arg_ofReal_of_nonneg hc.le] at harg
  have := (tendsto_const_nhds (x := 2 * Real.pi * (n₀ : ℝ))).sub harg
  rw [sub_zero] at this
  exact this.congr' hev

/-- A map with an analytic derivative logarithm on `D` is differentiable at every point of `D`. -/
theorem differentiableAt_of_isDerivLog {g L : ℂ → ℂ} {D : Set ℂ} (hL : IsDerivLog g L D) {z : ℂ} (hz : z ∈ D) :
    DifferentiableAt ℂ g z := by
  by_contra h
  have h0 := deriv_zero_of_not_differentiableAt h
  rw [← hL.2 z hz] at h0
  exact exp_ne_zero _ h0

/-- **The lift difference at a positive reflected derivative.** Let `cur` be a conformal chart whose lift is the
imaginary part of an analytic logarithm `Lc` of `cur.fwd′`, and `g` a map with an analytic logarithm `Lg` of `g′` on
an open set `D`. If `cur⁻¹` maps `ℍ ∩ B(ξ, r)` into `D` and the transition `g ∘ cur⁻¹` has derivative tending to
`c > 0` within `ℍ` at `ξ`, then `lift_cur − Im Lg`, read through `cur⁻¹`, tends to `2πn` for an integer `n`. -/
theorem exists_int_tendsto_lift_sub {cur : Chart} (hcur : cur.IsConformal) {Lc : ℂ → ℂ}
    (hLc : IsDerivLog cur.1 Lc cur.dom) (hlift : ∀ z ∈ cur.dom, cur.2.2 z = (Lc z).im)
    {g Lg : ℂ → ℂ} {D : Set ℂ} (hLg : IsDerivLog g Lg D) {ξ : ℂ} {r c : ℝ} (hr : 0 < r)
    (hmaps : ∀ y ∈ H ∩ ball ξ r, cur.2.1 y ∈ D)
    (hderiv : Tendsto (deriv fun y => g (cur.2.1 y)) (𝓝[H] ξ) (𝓝 (c : ℂ))) (hc : 0 < c) :
    ∃ n : ℤ, Tendsto (fun y => cur.2.2 (cur.2.1 y) - (Lg (cur.2.1 y)).im) (𝓝[H] ξ)
      (𝓝 (2 * Real.pi * n)) := by
  set U := H ∩ ball ξ r with hU
  have hUo : IsOpen U := isOpen_H.inter isOpen_ball
  have hinvU : MapsTo cur.2.1 U cur.dom := fun y hy => hcur.inv_mem_dom hy.1
  have hgD : DifferentiableOn ℂ g D := fun z hz => (differentiableAt_of_isDerivLog hLg hz).differentiableWithinAt
  have hSd : DifferentiableOn ℂ (fun y => g (cur.2.1 y)) U :=
    hgD.comp (hcur.1.mono inter_subset_left) (fun y hy => hmaps y hy)
  have hexp : ∀ y ∈ U, exp (Lc (cur.2.1 y) - Lg (cur.2.1 y)) * deriv (fun y => g (cur.2.1 y)) y = 1 := by
    intro y hy
    have hdom := hinvU hy
    have hdinv : DifferentiableAt ℂ cur.2.1 y := hcur.1.differentiableAt (isOpen_H.mem_nhds hy.1)
    have hdfwd : DifferentiableAt ℂ cur.1 (cur.2.1 y) := differentiableAt_of_isDerivLog hLc hdom
    have hdg : DifferentiableAt ℂ g (cur.2.1 y) := differentiableAt_of_isDerivLog hLg (hmaps y hy)
    have hid : deriv cur.1 (cur.2.1 y) * deriv cur.2.1 y = 1 := by
      have hev : (cur.1 ∘ cur.2.1) =ᶠ[𝓝 y] id :=
        Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hy.1) fun w hw => hcur.2.2 w hw
      rw [← deriv_comp y hdfwd hdinv, hev.deriv_eq, deriv_id]
    have hS : deriv (fun y => g (cur.2.1 y)) y = deriv g (cur.2.1 y) * deriv cur.2.1 y :=
      deriv_comp (h := cur.2.1) (h₂ := g) y hdg hdinv
    have hg0 : deriv g (cur.2.1 y) ≠ 0 := by rw [← hLg.2 _ (hmaps y hy)]; exact exp_ne_zero _
    rw [hS, exp_sub, hLc.2 _ hdom, hLg.2 _ (hmaps y hy)]
    field_simp
    rw [mul_comm] at hid
    linear_combination hid
  have hφc : ContinuousOn (fun y => Lc (cur.2.1 y) - Lg (cur.2.1 y)) U :=
    (hLc.1.continuousOn.comp (hcur.1.continuousOn.mono inter_subset_left) hinvU).sub
      (hLg.1.continuousOn.comp (hcur.1.continuousOn.mono inter_subset_left) fun y hy => hmaps y hy)
  have hDc : ContinuousOn (deriv fun y => g (cur.2.1 y)) U := (hSd.deriv hUo).continuousOn
  obtain ⟨n, hn⟩ := exists_int_tendsto_im_of_exp_mul_eq_one hr hφc hDc hexp hderiv hc
  refine ⟨n, hn.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Complex.sub_im]
  rw [hlift _ (hcur.inv_mem_dom hy)]

/-- **The common phase on one connected interval.** If at every point `ξ` of a preconnected real set `J` the
transition `g ∘ cur⁻¹` has a positive reflected derivative (on some half-disc mapped into `D` by `cur⁻¹`), then one
integer `n` serves at every point: `lift_cur − Im Lg → 2πn` within `ℍ` at every `ξ ∈ J`. -/
theorem exists_int_forall_tendsto_lift_sub {cur : Chart} (hcur : cur.IsConformal) {Lc : ℂ → ℂ}
    (hLc : IsDerivLog cur.1 Lc cur.dom) (hlift : ∀ z ∈ cur.dom, cur.2.2 z = (Lc z).im)
    {g Lg : ℂ → ℂ} {D : Set ℂ} (hLg : IsDerivLog g Lg D) {J : Set ℝ} (hJ : IsPreconnected J)
    (hrefl : ∀ ξ ∈ J, ∃ r > 0, (∀ y ∈ H ∩ ball (ξ : ℂ) r, cur.2.1 y ∈ D) ∧
      ∃ c : ℝ, 0 < c ∧ Tendsto (deriv fun y => g (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (c : ℂ))) :
    ∃ n : ℤ, ∀ ξ ∈ J, Tendsto (fun y => cur.2.2 (cur.2.1 y) - (Lg (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ))
      (𝓝 (2 * Real.pi * n)) := by
  have hex : ∀ ξ ∈ J, ∃ n : ℤ, Tendsto (fun y => cur.2.2 (cur.2.1 y) - (Lg (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ))
      (𝓝 (2 * Real.pi * n)) := fun ξ hξ => by
    obtain ⟨r, hr, hmaps, c, hc, hderiv⟩ := hrefl ξ hξ
    exact exists_int_tendsto_lift_sub hcur hLc hlift hLg hr hmaps hderiv hc
  classical
  set N : ℝ → ℤ := fun ξ => if h : ξ ∈ J then Classical.choose (hex ξ h) else 0 with hN
  have hNspec : ∀ ξ ∈ J, Tendsto (fun y => cur.2.2 (cur.2.1 y) - (Lg (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ))
      (𝓝 (2 * Real.pi * N ξ)) := fun ξ hξ => by
    rw [hN]; simp only [hξ, ↓reduceDIte]
    exact Classical.choose_spec (hex ξ hξ)
  have hcont : ContinuousOn (fun ξ => 2 * Real.pi * (N ξ : ℝ)) J :=
    continuousOn_of_tendsto_nhdsWithin_H hNspec
  obtain ⟨n, hn⟩ := exists_int_eq_of_isPreconnected hJ hcont fun ξ _ => ⟨N ξ, rfl⟩
  exact ⟨n, fun ξ hξ => by rw [← hn ξ hξ]; exact hNspec ξ hξ⟩

end InteractingSLE.Sec7.R5Lift
