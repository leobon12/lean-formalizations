/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowPocket
import InteractingSLE.Spec.Sec7.Aux130

/-!
# (RS13.3) and Aux. lemma 119: the transition argument keeps its integer

Packet PROVE-STRIPSYS7. Specification §7.4: the proof of Aux. lemma 130, (RS13.3) (`source/spec/p385-432.md`
L440–L456, p. 411), and the proof of Aux. lemma 119 (L14–L33, pp. 385–387).

> In each own chart the right-side height is `λ − θχ`, with its inherited derivative-logarithm lift. The transition
> between the two charts reflects analytically across the flattened common arc and has positive real derivative there.
> Its argument in the inherited branches is consequently `2πn` for an integer `n`, constant on the smaller arc.
> Expressing both germs in one chart therefore forces `θ₁ − π/2 = 2πn`.  (RS13.3)
>
> […] Two analytic logarithms differ by `2πin`, so agreement on that collar fixes the difference to zero.  (Aux. 119)

This file proves the analytic content of these steps:

* **The integer argument of a transition** (`exists_int_tendsto_im_sub`): on a preconnected collar `S`, if the
  inherited lifts `L₁, L₂` of the two charts satisfy `exp(L₂ − L₁) = G` with `G` (the transition derivative read in
  the first chart) in the slit plane on `S` and tending to a positive real along an approach `F` to the arc, then
  `Im(L₂ − L₁) → 2πn` along `F` for one integer `n`; the integer is the same for every approach inside `S`
  (`tendsto_im_sub_unique`). In the flattened coordinate (`exists_int_tendsto_im_of_reflect`): a lift `Λ` of a
  function `Φ` continuous across a real point `x` with `Φ(x) > 0` has `Im Λ → 2πn` at `x` from `ℍ`.
* **(RS13.3), the assembly** (`two_pi_int_of_common_side`, `false_of_common_side`): if two single-path means agree
  in boundary value on a common side (`v₁ − v₂ → 0`, Proposition 3.8 twice:
  `SideHeightBox.ae_tendsto_sub_of_locals`), their side heights in their own charts are `λ − θᵢχ`, and the transition
  argument tends to `2πn`, then `(θ₂ − θ₁)χ = 2πnχ`; for `0 < |θ₁ − θ₂| < 2π` this is impossible
  (`sub_mul_chiC_ne_two_pi_mul_int`), in particular for `θ₂ = π/2`, `−π/2 < θ₁ < π/2`
  (`false_of_common_side_half_pi`, via `Aux130.sub_half_pi_ne_two_pi_mul_int`).
* **Aux. lemma 119, the common lift** (`eq_zero_of_tendsto_im_sub`): if the two lifts' argument difference tends to
  `0` along one approach in the collar, the integer is zero, so the lifts agree on the whole collar
  (`eqOn_of_tendsto_im_sub_zero`).

The geometric inputs (a preconnected common collar on which the transition derivative is in the slit plane, the
approach `F`, and the side heights of the angle-varying strip paths at rational own times) are not constructed here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped Real

namespace InteractingSLE

namespace Sec7

namespace Aux119

/-! ### The integer argument of a transition -/

section Integer

variable {S : Set ℂ} {L₁ L₂ G : ℂ → ℂ}

/-- On a preconnected set where `exp(L₂ − L₁) = G ∈ slitPlane` (all continuous), `L₂ − L₁ − log G` is one constant
`2πin`. -/
theorem exists_int_eqOn_sub (hS : IsPreconnected S) (h₁ : ContinuousOn L₁ S) (h₂ : ContinuousOn L₂ S)
    (hG : ContinuousOn G S) (hslit : ∀ z ∈ S, G z ∈ slitPlane) (hexp : ∀ z ∈ S, exp (L₂ z - L₁ z) = G z) :
    ∃ n : ℤ, ∀ z ∈ S, L₂ z - L₁ z = log (G z) + n * (2 * π * I) := by
  have hn : ∀ z ∈ S, ∃ n : ℤ, L₂ z - L₁ z = log (G z) + n * (2 * π * I) := by
    intro z hz
    have hG0 : G z ≠ 0 := slitPlane_ne_zero (hslit z hz)
    exact exp_eq_exp_iff_exists_int.1 (by rw [hexp z hz, exp_log hG0])
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => hz.elim⟩
  set f : ℂ → ℝ := fun z => (L₂ z - L₁ z - log (G z)).im / (2 * π) with hf_def
  have hfn : ∀ z ∈ S, ∀ n : ℤ, L₂ z - L₁ z = log (G z) + n * (2 * π * I) → f z = n := by
    intro z _ n hzn
    simp only [hf_def, hzn, add_sub_cancel_left, mul_im, intCast_re, intCast_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    field_simp
    ring
  have hlog : ContinuousOn (fun z => log (G z)) S :=
    ContinuousOn.clog hG fun z hz => hslit z hz
  have hfc : ContinuousOn f S :=
    (continuous_im.comp_continuousOn ((h₂.sub h₁).sub hlog)).div_const _
  have hmaps : MapsTo f S (range ((↑) : ℤ → ℝ)) := by
    intro z hz
    obtain ⟨n, hzn⟩ := hn z hz
    exact ⟨n, (hfn z hz n hzn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  obtain ⟨n₀, hn₀⟩ := hn z₀ hz₀
  refine ⟨n₀, fun z hz => ?_⟩
  obtain ⟨n, hzn⟩ := hn z hz
  have hconst := hS.constant_of_mapsTo hdisc hfc hmaps hz hz₀
  rw [hfn z hz n hzn, hfn z₀ hz₀ n₀ hn₀, Int.cast_inj] at hconst
  rw [hzn, hconst]

/-- **The transition argument tends to `2πn`** ("The transition between the two charts reflects analytically across
the flattened common arc and has positive real derivative there. Its argument in the inherited branches is consequently
`2πn` for an integer `n`"): along an approach `F` inside the collar `S` on which the transition derivative `G` tends to
a positive real. -/
theorem exists_int_tendsto_im_sub (hS : IsPreconnected S) (h₁ : ContinuousOn L₁ S) (h₂ : ContinuousOn L₂ S)
    (hG : ContinuousOn G S) (hslit : ∀ z ∈ S, G z ∈ slitPlane) (hexp : ∀ z ∈ S, exp (L₂ z - L₁ z) = G z)
    {F : Filter ℂ} (hFS : F ≤ 𝓟 S) {c : ℝ} (hc : 0 < c) (hGc : Tendsto G F (𝓝 (c : ℂ))) :
    ∃ n : ℤ, Tendsto (fun z => (L₂ z - L₁ z).im) F (𝓝 (2 * π * n)) := by
  obtain ⟨n, hn⟩ := exists_int_eqOn_sub hS h₁ h₂ hG hslit hexp
  refine ⟨n, ?_⟩
  have harg : Tendsto (fun z => arg (G z)) F (𝓝 (arg (c : ℂ))) :=
    (continuousAt_arg (ofReal_mem_slitPlane.2 hc)).tendsto.comp hGc
  rw [arg_ofReal_of_nonneg hc.le] at harg
  have hlim : Tendsto (fun z => arg (G z) + 2 * π * n) F (𝓝 (0 + 2 * π * n)) :=
    harg.add_const _
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [hFS (mem_principal_self S)] with z hz
  rw [hn z hz, add_im, log_im]
  simp only [mul_im, intCast_re, intCast_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
    im_ofNat]
  ring

/-- **The integer does not depend on the approach** ("constant on the smaller arc"): two approaches inside one
preconnected collar give the same integer. -/
theorem tendsto_im_sub_unique (hS : IsPreconnected S) (h₁ : ContinuousOn L₁ S) (h₂ : ContinuousOn L₂ S)
    (hG : ContinuousOn G S) (hslit : ∀ z ∈ S, G z ∈ slitPlane) (hexp : ∀ z ∈ S, exp (L₂ z - L₁ z) = G z)
    {F F' : Filter ℂ} [F.NeBot] [F'.NeBot] (hFS : F ≤ 𝓟 S) (hF'S : F' ≤ 𝓟 S) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 < c') (hGc : Tendsto G F (𝓝 (c : ℂ))) (hGc' : Tendsto G F' (𝓝 (c' : ℂ))) {n n' : ℤ}
    (hn : Tendsto (fun z => (L₂ z - L₁ z).im) F (𝓝 (2 * π * n)))
    (hn' : Tendsto (fun z => (L₂ z - L₁ z).im) F' (𝓝 (2 * π * n'))) : n = n' := by
  -- both approaches see the same constant integer of `exists_int_eqOn_sub`
  obtain ⟨k, hk⟩ := exists_int_eqOn_sub hS h₁ h₂ hG hslit hexp
  have key : ∀ {F₀ : Filter ℂ} [F₀.NeBot], F₀ ≤ 𝓟 S → ∀ {c₀ : ℝ}, 0 < c₀ → Tendsto G F₀ (𝓝 (c₀ : ℂ)) →
      ∀ {n₀ : ℤ}, Tendsto (fun z => (L₂ z - L₁ z).im) F₀ (𝓝 (2 * π * n₀)) → n₀ = k := by
    intro F₀ _ hF₀ c₀ hc₀ hG₀ n₀ hn₀
    have harg : Tendsto (fun z => arg (G z)) F₀ (𝓝 (arg (c₀ : ℂ))) :=
      (continuousAt_arg (ofReal_mem_slitPlane.2 hc₀)).tendsto.comp hG₀
    rw [arg_ofReal_of_nonneg hc₀.le] at harg
    have hlim : Tendsto (fun z => arg (G z) + 2 * π * k) F₀ (𝓝 (0 + 2 * π * k)) := harg.add_const _
    have heq : (fun z => (L₂ z - L₁ z).im) =ᶠ[F₀] fun z => arg (G z) + 2 * π * k := by
      filter_upwards [hF₀ (mem_principal_self S)] with z hz
      rw [hk z hz, add_im, log_im]
      simp only [mul_im, intCast_re, intCast_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
        im_ofNat]
      ring
    have h2 := tendsto_nhds_unique (hn₀.congr' heq) hlim
    rw [zero_add] at h2
    have : (n₀ : ℝ) = k := by
      have hπ : (2 * π : ℝ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hπ (by linarith [h2])
    exact_mod_cast this
  rw [key hFS hc hGc hn, key hF'S hc' hGc' hn']

/-- **Aux. lemma 119, the common lift**: if the argument difference of the two lifts tends to `0` along one approach
in the collar, the two lifts agree on the whole collar up to `log G` ("Two analytic logarithms differ by `2πin`, so
agreement on that collar fixes the difference to zero"). -/
theorem eqOn_of_tendsto_im_sub_zero (hS : IsPreconnected S) (h₁ : ContinuousOn L₁ S) (h₂ : ContinuousOn L₂ S)
    (hG : ContinuousOn G S) (hslit : ∀ z ∈ S, G z ∈ slitPlane) (hexp : ∀ z ∈ S, exp (L₂ z - L₁ z) = G z)
    {F : Filter ℂ} [F.NeBot] (hFS : F ≤ 𝓟 S) {c : ℝ} (hc : 0 < c) (hGc : Tendsto G F (𝓝 (c : ℂ)))
    (h0 : Tendsto (fun z => (L₂ z - L₁ z).im) F (𝓝 0)) : ∀ z ∈ S, L₂ z - L₁ z = log (G z) := by
  obtain ⟨k, hk⟩ := exists_int_eqOn_sub hS h₁ h₂ hG hslit hexp
  have h0' : Tendsto (fun z => (L₂ z - L₁ z).im) F (𝓝 (2 * π * ((0 : ℤ) : ℝ))) := by
    simpa using h0
  obtain ⟨m, hm⟩ := exists_int_tendsto_im_sub hS h₁ h₂ hG hslit hexp hFS hc hGc
  have hk0 : k = 0 := by
    have e1 := tendsto_im_sub_unique hS h₁ h₂ hG hslit hexp hFS hFS hc hc hGc hGc h0' hm
    -- `m` is the constant integer `k` (both describe the same limit)
    have e2 : m = k := by
      have harg : Tendsto (fun z => arg (G z)) F (𝓝 (arg (c : ℂ))) :=
        (continuousAt_arg (ofReal_mem_slitPlane.2 hc)).tendsto.comp hGc
      rw [arg_ofReal_of_nonneg hc.le] at harg
      have hlim : Tendsto (fun z => arg (G z) + 2 * π * k) F (𝓝 (0 + 2 * π * k)) := harg.add_const _
      have heq : (fun z => (L₂ z - L₁ z).im) =ᶠ[F] fun z => arg (G z) + 2 * π * k := by
        filter_upwards [hFS (mem_principal_self S)] with z hz
        rw [hk z hz, add_im, log_im]
        simp only [mul_im, intCast_re, intCast_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
          im_ofNat]
        ring
      have h2 := tendsto_nhds_unique (hm.congr' heq) hlim
      rw [zero_add] at h2
      have : (m : ℝ) = k := by
        have hπ : (2 * π : ℝ) ≠ 0 := by positivity
        exact mul_left_cancel₀ hπ (by linarith [h2])
      exact_mod_cast this
    rw [← e2, ← e1]
  intro z hz
  rw [hk z hz, hk0]
  simp

end Integer

/-! ### The flattened coordinate -/

section Flat

/-- **The reflected transition, in the flattened coordinate**: if `Φ` (the derivative of the reflected transition) is
continuous at a real point `x` with `Φ(x) > 0`, and `Λ` is a continuous logarithm of `Φ` on `ℍ` near `x`, then
`Im Λ → 2πn` at `x` from `ℍ` for an integer `n`. -/
theorem exists_int_tendsto_im_of_reflect {Φ Λ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hΦ : ContinuousOn Φ (Metric.ball (x : ℂ) r)) (hΦx : 0 < (Φ x).re) (hΦx' : (Φ x).im = 0)
    (hΛ : ContinuousOn Λ (Metric.ball (x : ℂ) r ∩ QuantumZipper.H))
    (hexp : ∀ w ∈ Metric.ball (x : ℂ) r ∩ QuantumZipper.H, exp (Λ w) = Φ w) :
    ∃ n : ℤ, Tendsto (fun w => (Λ w).im) (𝓝[QuantumZipper.H] (x : ℂ)) (𝓝 (2 * π * n)) := by
  have hcx : ContinuousAt Φ (x : ℂ) := hΦ.continuousAt (Metric.ball_mem_nhds _ hr)
  -- a smaller ball on which `Φ` stays in the right half-plane
  obtain ⟨ε, hε, hεΦ⟩ := Metric.mem_nhds_iff.1
    (hcx.preimage_mem_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hΦx))
  set ρ := min ε r with hρ
  have hρ0 : 0 < ρ := lt_min hε hr
  set S : Set ℂ := Metric.ball (x : ℂ) ρ ∩ QuantumZipper.H with hS
  have hSsub : S ⊆ Metric.ball (x : ℂ) r ∩ QuantumZipper.H :=
    inter_subset_inter_left _ (Metric.ball_subset_ball (min_le_right _ _))
  have hSconn : IsPreconnected S :=
    ((convex_ball (x : ℂ) ρ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hslit : ∀ w ∈ S, Φ w ∈ slitPlane := fun w hw =>
    Or.inl (hεΦ (Metric.ball_subset_ball (min_le_left _ _) hw.1))
  have hΦx0 : Φ x = ((Φ x).re : ℂ) := Complex.ext (by simp) (by simp [hΦx'])
  have hFS : 𝓝[S] (x : ℂ) ≤ 𝓟 S := inf_le_right
  have hGc : Tendsto Φ (𝓝[S] (x : ℂ)) (𝓝 (((Φ x).re : ℝ) : ℂ)) := by
    rw [← hΦx0]
    exact hcx.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨n, hn⟩ := exists_int_tendsto_im_sub (L₁ := fun _ => 0) (L₂ := Λ) hSconn continuousOn_const
    (hΛ.mono hSsub) (hΦ.mono (hSsub.trans inter_subset_left)) hslit
    (fun w hw => by simpa using hexp w (hSsub hw)) hFS hΦx hGc
  refine ⟨n, ?_⟩
  have hnhds : 𝓝[S] (x : ℂ) = 𝓝[QuantumZipper.H] (x : ℂ) := by
    rw [hS, inter_comm]
    exact nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hρ0))
  rw [← hnhds]
  simpa using hn

end Flat

/-! ### (RS13.3): expressing both germs in one chart -/

section Assembly

open QuantumZipper (chiC)

/-- **(RS13.3), the identity**: if two harmonic means `v₁, v₂` agree in boundary value along an approach `F`
(`v₁ − v₂ → 0`), their side heights in their own charts are `λ − θᵢχ` (`vᵢ + u₀ + χ Im Lᵢ → λ − θᵢχ`), and the
argument of the transition tends to `2πn` (`Im L₁ − Im L₂ → 2πn`), then `(θ₂ − θ₁)χ = 2πnχ`. -/
theorem two_pi_int_of_common_side {F : Filter ℂ} [F.NeBot] {v₁ v₂ u₀ : ℂ → ℝ} {L₁ L₂ : ℂ → ℂ}
    {χ lam θ₁ θ₂ : ℝ} {n : ℤ} (hv : Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0))
    (h₁ : Tendsto (fun z => v₁ z + u₀ z + χ * (L₁ z).im) F (𝓝 (lam - θ₁ * χ)))
    (h₂ : Tendsto (fun z => v₂ z + u₀ z + χ * (L₂ z).im) F (𝓝 (lam - θ₂ * χ)))
    (hL : Tendsto (fun z => (L₁ z).im - (L₂ z).im) F (𝓝 (2 * π * n))) :
    (θ₂ - θ₁) * χ = 2 * π * n * χ := by
  have hsub := h₁.sub h₂
  have hsum := hv.add (hL.const_mul χ)
  have heq : (fun z => (v₁ z + u₀ z + χ * (L₁ z).im) - (v₂ z + u₀ z + χ * (L₂ z).im)) =
      fun z => (v₁ z - v₂ z) + χ * ((L₁ z).im - (L₂ z).im) := by
    funext z
    ring
  rw [heq] at hsub
  have := tendsto_nhds_unique hsub hsum
  linarith

/-- **(RS13.3) is impossible for two distinct angles less than `2π` apart** (supplement §5.3, Lemma 6.13 "retaining
the integer"): with `χ ≠ 0`, `θ₁ ≠ θ₂`, `|θ₁ − θ₂| < 2π`. -/
theorem false_of_common_side {F : Filter ℂ} [F.NeBot] {v₁ v₂ u₀ : ℂ → ℝ} {L₁ L₂ : ℂ → ℂ}
    {χ lam θ₁ θ₂ : ℝ} {n : ℤ} (hχ : χ ≠ 0) (hθ : θ₁ ≠ θ₂) (hθ2 : |θ₂ - θ₁| < 2 * π)
    (hv : Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0))
    (h₁ : Tendsto (fun z => v₁ z + u₀ z + χ * (L₁ z).im) F (𝓝 (lam - θ₁ * χ)))
    (h₂ : Tendsto (fun z => v₂ z + u₀ z + χ * (L₂ z).im) F (𝓝 (lam - θ₂ * χ)))
    (hL : Tendsto (fun z => (L₁ z).im - (L₂ z).im) F (𝓝 (2 * π * n))) : False :=
  sub_mul_chiC_ne_two_pi_mul_int hχ (Ne.symm hθ) hθ2 n (two_pi_int_of_common_side hv h₁ h₂ hL)

/-- **(RS13.3) for the first incoming path against the extremal path** (proof of Aux. lemma 130, p. 411: "Expressing
both germs in one chart therefore forces `θ₁ − π/2 = 2πn`. This is impossible because `−π < θ₁ − π/2 < 0`"): the
second path has angle `π/2`. -/
theorem false_of_common_side_half_pi {F : Filter ℂ} [F.NeBot] {v₁ v₂ u₀ : ℂ → ℝ} {L₁ L₂ : ℂ → ℂ}
    {χ lam θ₁ : ℝ} {n : ℤ} (hχ : χ ≠ 0) (hθ₁ : -(π / 2) < θ₁) (hθ₁' : θ₁ < π / 2)
    (hv : Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0))
    (h₁ : Tendsto (fun z => v₁ z + u₀ z + χ * (L₁ z).im) F (𝓝 (lam - θ₁ * χ)))
    (h₂ : Tendsto (fun z => v₂ z + u₀ z + χ * (L₂ z).im) F (𝓝 (lam - π / 2 * χ)))
    (hL : Tendsto (fun z => (L₁ z).im - (L₂ z).im) F (𝓝 (2 * π * n))) : False := by
  have h := two_pi_int_of_common_side hv h₁ h₂ hL
  have he : π / 2 - θ₁ = 2 * π * n := mul_right_cancel₀ hχ (by linarith [h])
  exact Aux130.sub_half_pi_ne_two_pi_mul_int hθ₁ hθ₁' (-n) (by push_cast; linarith)

end Assembly

end Aux119

end Sec7

end InteractingSLE
