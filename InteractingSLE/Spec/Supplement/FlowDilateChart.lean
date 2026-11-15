/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.FlowDilate
import InteractingSLE.Spec.Supplement.RLCChart

/-!
# Chart completability is invariant under `A(z) = a z + m` (`a > 0`) and a time change

Packet PROVE-RLC-J, item (g): the last part of Lemma G8's affine normalization ("the two seed collars retain their
canonical heights under this positive affine map"; the completability of the conditional pair is the conclusion of
`RLC.G8FrameStatement`). For curves with real first seed:

* `seedRayClosure_aff`, **`closedLeftSide_aff`**: the closed left Jordan side of `A ∘ γ ∘ (c ·)` is `A` of that of
  `γ` (`A` is an orientation-preserving homeomorphism; the base points `γ(0) − 1 − i` and `A(γ(0) − 1 − i)` lie in the
  open lower-left quadrant at the seed, a convex set off the closed curve);
* `IsProperCompletion.affine`;
* **`IsChartCompletable.affine`**: completability of `(g₁, s₁; g₂, s₂)` gives completability of
  `(A ∘ g₁ ∘ (c ·), s₁/c; A ∘ g₂ ∘ (c ·), s₂/c)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal

namespace InteractingSLE

namespace FlowDilate

variable {a m : ℝ} {c : ℝ≥0}

theorem aff_bijective (ha : a ≠ 0) : Function.Bijective (aff a m) := (affHomeo ha).bijective

theorem c_mul_div (hc : c ≠ 0) (s : ℝ≥0) : c * (s / c) = s := by
  rw [mul_div_cancel₀ s hc]

theorem range_aff_comp (hc : c ≠ 0) (γ : ℝ≥0 → ℂ) :
    range (fun t => aff a m (γ (c * t))) = aff a m '' range γ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨γ (c * t), ⟨_, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s / c, by simp only [c_mul_div hc]⟩

theorem seedRayClosure_aff (ha : 0 < a) (hc : c ≠ 0) (γ : ℝ≥0 → ℂ) :
    seedRayClosure (fun t => aff a m (γ (c * t))) = aff a m '' seedRayClosure γ := by
  unfold seedRayClosure
  rw [image_union, range_aff_comp hc]
  congr 1
  simp only [mul_zero]
  ext z
  simp only [mem_ofPred_eq, mem_image, aff_re, aff_im]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨affInv a m z, ⟨?_, ?_⟩, aff_affInv ha.ne' z⟩
    · simp only [affInv, aff_re]; rw [h1]; field_simp; ring
    · simp only [affInv, aff_im]
      rw [inv_mul_le_iff₀ ha]
      exact h2
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    exact ⟨by rw [aff_re, h1], by rw [aff_im]; exact mul_le_mul_of_nonneg_left h2 ha.le⟩

/-- The image of a connected component under `A`. -/
theorem image_connectedComponentIn_aff (ha : a ≠ 0) (S : Set ℂ) (p : ℂ) :
    aff a m '' connectedComponentIn S p = connectedComponentIn (aff a m '' S) (aff a m p) := by
  by_cases hp : p ∈ S
  · refine subset_antisymm ((continuous_aff a m).continuousOn.image_connectedComponentIn_subset hp) ?_
    have h := (continuous_aff (a⁻¹) (-m / a)).continuousOn.image_connectedComponentIn_subset
      (s := aff a m '' S) (a := aff a m p) ⟨p, hp, rfl⟩
    have e1 : aff a⁻¹ (-m / a) '' (aff a m '' S) = S := affInv_image_aff_image ha S
    have e2 : aff a⁻¹ (-m / a) (aff a m p) = p := affInv_aff ha p
    rw [e1, e2] at h
    have h' := image_mono (f := aff a m) h
    have e3 : aff a m '' (aff a⁻¹ (-m / a) '' connectedComponentIn (aff a m '' S) (aff a m p)) =
        connectedComponentIn (aff a m '' S) (aff a m p) := aff_image_affInv_image ha _
    rwa [e3] at h'
  · have hp' : aff a m p ∉ aff a m '' S := fun ⟨q, hq, e⟩ => hp ((affHomeo (m := m) ha).injective e ▸ hq)
    rw [connectedComponentIn_eq_empty hp, connectedComponentIn_eq_empty hp', image_empty]

/-- **The closed left side under `A` and a time change**, for a curve in the closed upper half-plane with a real
first point. -/
theorem closedLeftSide_aff (ha : 0 < a) (hc : c ≠ 0) {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im)
    (h0 : (γ 0).im = 0) :
    closedLeftSide (fun t => aff a m (γ (c * t))) = aff a m '' closedLeftSide γ := by
  unfold closedLeftSide
  rw [image_union, ← seedRayClosure_aff ha hc]
  congr 1
  set S := seedRayClosure γ with hS
  set F := (seedRayClosure fun t => aff a m (γ (c * t)))ᶜ with hF
  have hFS : F = aff a m '' Sᶜ := by
    rw [hF, seedRayClosure_aff ha hc, image_compl_eq (aff_bijective ha.ne')]
  simp only [mul_zero]
  rw [image_connectedComponentIn_aff ha.ne', ← hFS]
  -- the two base points lie in the open lower-left quadrant at the seed, a convex subset of `F`
  set q : ℂ := aff a m (γ 0) with hq
  set Q : Set ℂ := {z | z.re < q.re ∧ z.im < 0} with hQ
  have hQc : IsPreconnected Q := by
    refine (Convex.inter ?_ ?_).isPreconnected
    · exact convex_halfSpace_lt (f := Complex.reCLM) Complex.reCLM.isLinear _
    · exact convex_halfSpace_lt (f := Complex.imCLM) Complex.imCLM.isLinear _
  have hQF : Q ⊆ F := by
    rintro z ⟨hzr, hzi⟩ hzS
    rcases hzS with ⟨t, rfl⟩ | ⟨hre, -⟩
    · have := hγ (c * t)
      simp only [aff_im] at hzi
      nlinarith
    · simp only [mul_zero] at hre
      rw [hre] at hzr
      exact lt_irrefl _ hzr
  have h1 : q - 1 - Complex.I ∈ Q := ⟨by simp, by simp [hq, aff_im, h0]⟩
  have h2 : aff a m (γ 0 - 1 - Complex.I) ∈ Q := by
    refine ⟨?_, ?_⟩
    · simp only [hq, aff_re, Complex.sub_re, Complex.one_re, Complex.I_re, sub_zero]; nlinarith
    · simp only [aff_im, Complex.sub_im, Complex.one_im, Complex.I_im, h0, sub_zero]; nlinarith
  have hsub := hQc.subset_connectedComponentIn h1 hQF
  exact connectedComponentIn_eq (hsub h2)

/-- Proper completions under `A` and a time change. -/
theorem _root_.InteractingSLE.IsProperCompletion.affine (ha : 0 < a) (hc : c ≠ 0) {g γ : ℝ≥0 → ℂ} {s : ℝ≥0}
    (h : IsProperCompletion g s γ) :
    IsProperCompletion (fun t => aff a m (g (c * t))) (s / c) (fun t => aff a m (γ (c * t))) := by
  obtain ⟨hcont, hinj, him, hlim, hagree⟩ := h
  have hc0 : 0 < c := pos_iff_ne_zero.2 hc
  refine ⟨(continuous_aff a m).comp (hcont.comp (continuous_const.mul continuous_id)), fun t t' e => ?_,
    fun t => ?_, ?_, fun t ht => ?_⟩
  · have e1 := (affHomeo (m := m) ha.ne').injective e
    have e2 := hinj e1
    exact mul_left_cancel₀ hc e2
  · simp only [aff_im]
    exact mul_nonneg ha.le (him _)
  · have hT : Tendsto (fun t : ℝ≥0 => c * t) atTop atTop := tendsto_id.const_mul_atTop' hc0
    have h1 : Tendsto (fun t : ℝ≥0 => a * ‖γ (c * t)‖ + -|m|) atTop atTop :=
      tendsto_atTop_add_const_right _ _ ((hlim.comp hT).const_mul_atTop ha)
    refine tendsto_atTop_mono (fun t => ?_) h1
    show a * ‖γ (c * t)‖ + -|m| ≤ ‖a • γ (c * t) + (m : ℂ)‖
    have h2 := norm_sub_le (a • γ (c * t) + (m : ℂ)) (m : ℂ)
    simp only [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ha.le, Complex.norm_real,
      Real.norm_eq_abs] at h2
    linarith
  · have hct : c * t ≤ s := by
      rw [le_div_iff₀ hc0] at ht
      rwa [mul_comm]
    simp only [hagree _ hct]

/-- **Chart completability under `A` and a time change** (Lemma G8's affine normalization): if `(g₁, s₁; g₂, s₂)`
is completable and `g₁` starts on `ℝ`, so is `(A ∘ g₁ ∘ (c ·), s₁/c; A ∘ g₂ ∘ (c ·), s₂/c)`. -/
theorem _root_.InteractingSLE.RLC.IsChartCompletable.affine (ha : 0 < a) (hc : c ≠ 0) {g₁ g₂ : ℝ≥0 → ℂ}
    {s₁ s₂ : ℝ≥0} (h10 : (g₁ 0).im = 0) (h : RLC.IsChartCompletable g₁ s₁ g₂ s₂) :
    RLC.IsChartCompletable (fun t => aff a m (g₁ (c * t))) (s₁ / c) (fun t => aff a m (g₂ (c * t))) (s₂ / c) := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hord, hs₁, hs₂⟩ := h
  have hγ₁0 : (γ₁ 0).im = 0 := by rw [hγ₁.2.2.2.2 0 zero_le]; exact h10
  refine ⟨_, _, hγ₁.affine ha hc, hγ₂.affine ha hc, ?_, ?_, ?_⟩
  · rw [range_aff_comp hc, closedLeftSide_aff ha hc hγ₁.2.2.1 hγ₁0]
    exact image_mono hord
  · simp only [mul_zero]
    rw [range_aff_comp hc]
    rintro ⟨w, hw, e⟩
    exact hs₁ ((affHomeo (m := m) ha.ne').injective e ▸ hw)
  · simp only [mul_zero]
    rw [range_aff_comp hc]
    rintro ⟨w, hw, e⟩
    exact hs₂ ((affHomeo (m := m) ha.ne').injective e ▸ hw)

end FlowDilate

end InteractingSLE
