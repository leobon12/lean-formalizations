/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Sec5.Aux61TwoSReflect

/-!
# The argument lift of a conformal map at two reflecting real points

Packet PROVE-AUX61-NOJUMP (the branch integer of R103's landing height). Aux. lemma 57's proof
(`Sec7.sub_eq_log_sub_log_of_path`, the square lemma for the secant `S(z, w) = (T z − T w)/(z − w)`)
applies to any conformal map `T : D → ℍ` of a path-connected `D ⊆ ℍ`, not only to mapping-out
functions:

* **`im_eq_of_posReflect_pair`**: if `T` has positive real reflections at two real points `y < x`
  (half-discs in `D`) with `T(y) < T(x)`, then a continuous logarithm `L` of `T′` on `D` has the same
  imaginary boundary limit at `x` and at `y`.

The order condition is exactly what keeps the corner secant `S(x, y)` off the negative real axis; across
a pole of `T` (the chart target) or a wrap of the coordinate the lift may change by `2π`.

* `tendsto_of_posReflect_of_tendsto_im`: at a reflecting real point the real part of `L` converges
  automatically (`Re L = log |T′|`), so an imaginary limit is a full limit.

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open scoped Real
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61TwoS

/-- **A full limit from an imaginary limit** at a reflecting real point. -/
theorem tendsto_of_posReflect_of_tendsto_im {T G L : ℂ → ℂ} {D : Set ℂ} {x r a : ℝ}
    (hG : IsPosReflect T G x r) (hxD : H ∩ ball (x : ℂ) r ⊆ D)
    (hLe : ∀ z ∈ D, exp (L z) = deriv T z)
    (ha : Tendsto (fun z => (L z).im) (𝓝[H] (x : ℂ)) (𝓝 a)) :
    Tendsto L (𝓝[H] (x : ℂ)) (𝓝 ((Real.log ‖deriv G x‖ : ℂ) + (a : ℂ) * I)) := by
  have hxB : ((x : ℝ) : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hG.pos
  have hd := hG.tendsto_deriv hxB
  have hne : deriv G x ≠ 0 := fun h => by
    have := (hG.deriv_pos hxB).2
    rw [h, zero_re] at this
    exact lt_irrefl _ this
  have hre : Tendsto (fun z => (L z).re) (𝓝[H] (x : ℂ)) (𝓝 (Real.log ‖deriv G x‖)) := by
    have h1 : Tendsto (fun z => Real.log ‖deriv T z‖) (𝓝[H] (x : ℂ)) (𝓝 (Real.log ‖deriv G x‖)) :=
      ((Real.continuousAt_log (norm_ne_zero_iff.2 hne)).tendsto.comp
        (continuous_norm.continuousAt.tendsto.comp hd))
    refine h1.congr' ?_
    filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with z hz
    rw [← hLe z (hxD hz), Complex.norm_exp, Real.log_exp]
  have h := ((continuous_ofReal.tendsto _).comp hre).add
    (((continuous_ofReal.tendsto _).comp ha).mul_const I)
  refine h.congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  exact re_add_im (L z)

/-- **The secant comparison.** Let `T` be holomorphic and injective on an open path-connected `D ⊆ ℍ`
with values in `ℍ`, `L` a continuous logarithm of `T′` on `D`, and let `T` have positive real reflections
`G_x`, `G_y` at real points `y < x` whose upper half-discs lie in `D`, with `G_y(y) < G_x(x)`. Then the
imaginary boundary limits of `L` at `x` and `y` agree. -/
theorem im_eq_of_posReflect_pair {T L Gx Gy : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (hDH : D ⊆ H)
    (hDc : IsPathConnected D) (hTd : DifferentiableOn ℂ T D) (hTinj : InjOn T D)
    (hTH : MapsTo T D H) (hLc : ContinuousOn L D) (hLe : ∀ z ∈ D, exp (L z) = deriv T z)
    {x y rx ry : ℝ} (hGx : IsPosReflect T Gx x rx) (hGy : IsPosReflect T Gy y ry)
    (hxD : H ∩ ball (x : ℂ) rx ⊆ D) (hyD : H ∩ ball (y : ℂ) ry ⊆ D)
    (hyx : y < x) (hT : (Gy y).re < (Gx x).re) {a b : ℝ}
    (hax : Tendsto (fun z => (L z).im) (𝓝[H] (x : ℂ)) (𝓝 a))
    (hby : Tendsto (fun z => (L z).im) (𝓝[H] (y : ℂ)) (𝓝 b)) : a = b := by
  set d : ℝ := (x - y) / 2 with hd
  have hd0 : 0 < d := by simp only [hd]; linarith
  set r₁ : ℝ := min rx d with hr₁
  set r₂ : ℝ := min ry d with hr₂
  have hr₁0 : 0 < r₁ := lt_min hGx.pos hd0
  have hr₂0 : 0 < r₂ := lt_min hGy.pos hd0
  have hdisj : ∀ z, z ∈ ball (x : ℂ) r₁ → z ∉ ball (y : ℂ) r₂ := by
    intro z hzx hzy
    have h1 : dist z (x : ℂ) < d := lt_of_lt_of_le hzx (min_le_right _ _)
    have h2 : dist z (y : ℂ) < d := lt_of_lt_of_le hzy (min_le_right _ _)
    have h3 : dist (x : ℂ) (y : ℂ) = x - y := by
      rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have := dist_triangle_left (x : ℂ) (y : ℂ) z
    linarith
  have hxB : ((x : ℝ) : ℂ) ∈ ball (x : ℂ) rx := mem_ball_self hGx.pos
  have hyB : ((y : ℝ) : ℂ) ∈ ball (y : ℂ) ry := mem_ball_self hGy.pos
  -- the glued holomorphic function
  have hTGx : EqOn T Gx (D ∩ ball (x : ℂ) r₁) := fun z hz =>
    (hGx.eqOn ⟨hDH hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩).symm
  obtain ⟨hf₁d, hf₁T⟩ := Sec7.differentiableOn_piecewise_ball hDo hTd
    (hGx.diff.mono (ball_subset_ball (min_le_left _ _))) hTGx
  set f₁ : ℂ → ℂ := fun z => open scoped Classical in if z ∈ ball (x : ℂ) r₁ then Gx z else T z with hf₁
  have hΩ₁ : IsOpen (D ∪ ball (x : ℂ) r₁) := hDo.union isOpen_ball
  have hf₁Gy : EqOn f₁ Gy ((D ∪ ball (x : ℂ) r₁) ∩ ball (y : ℂ) r₂) := by
    intro z hz
    have hzx : z ∉ ball (x : ℂ) r₁ := fun h => hdisj z h hz.2
    have hzD : z ∈ D := hz.1.resolve_right hzx
    rw [hf₁T hzD]
    exact (hGy.eqOn ⟨hDH hzD, ball_subset_ball (min_le_left _ _) hz.2⟩).symm
  obtain ⟨hfd, hff₁⟩ := Sec7.differentiableOn_piecewise_ball hΩ₁ hf₁d
    (hGy.diff.mono (ball_subset_ball (min_le_left _ _))) hf₁Gy
  set f : ℂ → ℂ := fun z => open scoped Classical in if z ∈ ball (y : ℂ) r₂ then Gy z else f₁ z with hf
  have hΩ : IsOpen ((D ∪ ball (x : ℂ) r₁) ∪ ball (y : ℂ) r₂) := hΩ₁.union isOpen_ball
  have hfT : ∀ z ∈ D, f z = T z := fun z hz => by
    rw [hff₁ (Or.inl hz), hf₁T hz]
  have hfGx : ∀ z ∈ ball (x : ℂ) r₁, f z = Gx z := fun z hz => by
    rw [hff₁ (Or.inr hz)]
    simp only [hf₁, hz, ↓reduceIte]
  have hfGy : ∀ z ∈ ball (y : ℂ) r₂, f z = Gy z := fun z hz => by
    simp only [hf, hz, ↓reduceIte]
  have hxr₁ : ((x : ℝ) : ℂ) ∈ ball (x : ℂ) r₁ := mem_ball_self hr₁0
  have hyr₂ : ((y : ℝ) : ℂ) ∈ ball (y : ℂ) r₂ := mem_ball_self hr₂0
  -- derivatives
  have hdD : ∀ z ∈ D, deriv f z = deriv T z := fun z hz =>
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hDo.mem_nhds hz) hfT)
  have hdx : deriv f x = deriv Gx x :=
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxr₁) hfGx)
  have hdy : deriv f y = deriv Gy y :=
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hyr₂) hfGy)
  -- the path
  set c : ℝ := min r₁ r₂ / 2 with hc
  have hc0 : 0 < c := by simp only [hc]; exact half_pos (lt_min hr₁0 hr₂0)
  have hvert : ∀ (v ρ ρ' : ℝ), 0 < ρ → c < ρ → ρ ≤ ρ' → H ∩ ball (v : ℂ) ρ' ⊆ D →
      ∀ s : ℝ, 0 < s → s ≤ c → (v : ℂ) + (s : ℂ) * I ∈ D := by
    intro v ρ ρ' _ hcρ hρρ' hsub s hs hsc
    refine hsub ⟨show (0 : ℝ) < ((v : ℂ) + (s : ℂ) * I).im by simp [hs], ?_⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hs]
    linarith
  have hcr₁ : c < r₁ := by
    simp only [hc]; linarith [min_le_left r₁ r₂, half_lt_self (lt_min hr₁0 hr₂0)]
  have hcr₂ : c < r₂ := by
    simp only [hc]; linarith [min_le_right r₁ r₂, half_lt_self (lt_min hr₁0 hr₂0)]
  obtain ⟨γ, hγc, hγ0, hγ1, hγD⟩ := Sec7.exists_path_of_vert hDc
    (hvert x r₁ rx hr₁0 hcr₁ (min_le_left _ _) hxD)
    (hvert y r₂ ry hr₂0 hcr₂ (min_le_left _ _) hyD) hc0
  set P : Set ℂ := insert (x : ℂ) (insert (y : ℂ) D) with hP
  have hPΩ : P ⊆ (D ∪ ball (x : ℂ) r₁) ∪ ball (y : ℂ) r₂ := by
    rintro z (rfl | rfl | hz)
    · exact Or.inl (Or.inr hxr₁)
    · exact Or.inr hyr₂
    · exact Or.inl (Or.inl hz)
  have hγP : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hγ0]; exact Or.inr (Or.inl rfl)
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, hγ1]; exact Or.inl rfl
    · exact Or.inr (Or.inr (hγD t ⟨h0, h1⟩))
  -- values
  have hfx : f x = ((Gx x).re : ℂ) := by
    rw [hfGx _ hxr₁]
    exact Complex.ext (by simp) (by simp [hGx.im_eq_zero hxB])
  have hfy : f y = ((Gy y).re : ℂ) := by
    rw [hfGy _ hyr₂]
    exact Complex.ext (by simp) (by simp [hGy.im_eq_zero hyB])
  have hfDH : ∀ z ∈ D, 0 < (f z).im := fun z hz => by rw [hfT z hz]; exact hTH hz
  have hinj : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → f a ≠ f b := by
    have hxy : f x ≠ f y := by
      rw [hfx, hfy]; intro h; exact (ne_of_gt hT) (ofReal_injective h)
    have hDx : ∀ z ∈ D, f z ≠ f x := fun z hz h => by
      have := hfDH z hz; rw [h, hfx, ofReal_im] at this; exact lt_irrefl _ this
    have hDy : ∀ z ∈ D, f z ≠ f y := fun z hz h => by
      have := hfDH z hz; rw [h, hfy, ofReal_im] at this; exact lt_irrefl _ this
    rintro a (rfl | rfl | ha) b (rfl | rfl | hb) hab
    · exact absurd rfl hab
    · exact hxy
    · exact (hDx b hb).symm
    · exact hxy.symm
    · exact absurd rfl hab
    · exact (hDy b hb).symm
    · exact hDx a ha
    · exact hDy a ha
    · intro h
      rw [hfT a ha, hfT b hb] at h
      exact hab (hTinj ha hb h)
  have hder : ∀ a ∈ P, deriv f a ≠ 0 := by
    rintro a (rfl | rfl | ha)
    · rw [hdx]; intro h; have := (hGx.deriv_pos hxB).2; rw [h, zero_re] at this; exact lt_irrefl _ this
    · rw [hdy]; intro h; have := (hGy.deriv_pos hyB).2; rw [h, zero_re] at this; exact lt_irrefl _ this
    · rw [hdD a ha, ← hLe a ha]; exact exp_ne_zero _
  -- secants
  have hcorner : dslope f (y : ℂ) (x : ℂ) ∈ slitPlane := by
    have hne : (x : ℂ) ≠ (y : ℂ) := fun h => (ne_of_gt hyx) (ofReal_injective h)
    rw [dslope_of_ne _ hne, slope_def_field, hfx, hfy, ← ofReal_sub, ← ofReal_sub, ← ofReal_div]
    exact Or.inl (by rw [ofReal_re]; exact div_pos (by linarith) (by linarith))
  have hpx : deriv f x ∈ slitPlane := by rw [hdx]; exact Or.inl (hGx.deriv_pos hxB).2
  have hpy : deriv f y ∈ slitPlane := by rw [hdy]; exact Or.inl (hGy.deriv_pos hyB).2
  have hfxim : (f x).im = 0 := by rw [hfx, ofReal_im]
  have hfyim : (f y).im = 0 := by rw [hfy, ofReal_im]
  have hbot : ∀ t ∈ Icc (0 : ℝ) 1, dslope f (γ 0) (γ t) ∈ slitPlane := by
    intro t ht
    rw [hγ0]
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hγ0, dslope_same]; exact hpy
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, hγ1]; exact hcorner
    · have hz := hγD t ⟨h0, h1⟩
      exact (Sec7.dslope_mem_slitPlane (hDH hz) (by simp) (hfDH _ hz) hfyim).1
  have hright : ∀ s ∈ Icc (0 : ℝ) 1, dslope f (γ s) (γ 1) ∈ slitPlane := by
    intro s hs
    rw [hγ1]
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hγ0]; exact hcorner
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · rw [h1, hγ1, dslope_same]; exact hpx
    · have hz := hγD s ⟨h0, h1⟩
      exact (Sec7.dslope_mem_slitPlane (hDH hz) (by simp) (hfDH _ hz) hfxim).2
  -- the end limits
  have hγH0 : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hγ0]; exact (hγc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact hDH (hγD t ht)
  have hγH1 : Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hγ1]; exact (hγc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact hDH (hγD t ht)
  have hLx := tendsto_of_posReflect_of_tendsto_im hGx hxD hLe hax
  have hLy := tendsto_of_posReflect_of_tendsto_im hGy hyD hLe hby
  have hkey := Sec7.sub_eq_log_sub_log_of_path hΩ hfd hLc (fun z hz => by rw [hdD z hz]; exact hLe z hz)
    hγc hγP hPΩ hγD hinj hder hbot hright (hLy.comp hγH0) (hLx.comp hγH1)
  rw [hγ1, hγ0, hdx, hdy] at hkey
  have him := congrArg Complex.im hkey
  have hax0 : (log (deriv Gx x)).im = 0 := by
    rw [log_im, arg_eq_zero_iff]; exact ⟨(hGx.deriv_pos hxB).2.le, (hGx.deriv_pos hxB).1⟩
  have hby0 : (log (deriv Gy y)).im = 0 := by
    rw [log_im, arg_eq_zero_iff]; exact ⟨(hGy.deriv_pos hyB).2.le, (hGy.deriv_pos hyB).1⟩
  simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
    hax0, hby0, sub_zero] at him
  linarith

end InteractingSLE.Sec5.Aux61Nj
