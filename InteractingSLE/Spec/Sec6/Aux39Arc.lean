/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionLens
import InteractingSLE.Foundations.Topology.Jordan.Complex
import QuantumZipper.Proofs.Complex.TopoJaniszewski

/-!
# Arcs in the closed upper half-plane and the two sides of a Jordan curve there

Toolkit for the fixed-chart gate lemma (Lemma 1.3 of the ZTip-elimination note, ruling R41) used in
**Aux.** lemmas 39 and 41.

* `arcJoin u v`, `arcRev u`, `segPath a b`, `circPath R θ₀ θ₁`: paths on `[0, 1]` (concatenation,
  reversal, straight segment, circular arc of radius `R`), with continuity, injectivity, images and
  endpoints;
* `outerSide J = connectedComponentIn Jᶜ (-I)` and `innerSide J = Jᶜ \ outerSide J` for a Jordan
  curve `J ⊆ ℍ̄`: the inner side is the bounded component of `Jᶜ`, lies in `ℍ`, and both sides have
  frontier `J`; the outer side contains the open lower half-plane and every real point off `J`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

/-! ### Concatenation and reversal -/

/-- Concatenation of two paths on `[0, 1]`. -/
def arcJoin (u v : ℝ → ℂ) (t : ℝ) : ℂ := if t ≤ 1 / 2 then u (2 * t) else v (2 * t - 1)

/-- Reversal of a path on `[0, 1]`. -/
def arcRev (u : ℝ → ℂ) (t : ℝ) : ℂ := u (1 - t)

section Join

variable {u v : ℝ → ℂ}

theorem arcJoin_zero : arcJoin u v 0 = u 0 := by simp [arcJoin]

theorem arcJoin_one : arcJoin u v 1 = v 1 := by norm_num [arcJoin]

theorem arcJoin_eqOn_left : EqOn (arcJoin u v) (fun t => u (2 * t)) (Icc 0 (1 / 2)) :=
  fun t ht => by simp only [arcJoin, ht.2, ↓reduceIte]

theorem arcJoin_eqOn_right (huv : u 1 = v 0) :
    EqOn (arcJoin u v) (fun t => v (2 * t - 1)) (Icc (1 / 2) 1) := by
  intro t ht
  by_cases h : t ≤ 1 / 2
  · have : t = 1 / 2 := le_antisymm h ht.1
    subst this
    norm_num [arcJoin, huv]
  · simp only [arcJoin, h, ↓reduceIte]

theorem mapsTo_two_mul : MapsTo (fun t : ℝ => 2 * t) (Icc 0 (1 / 2)) (Icc 0 1) :=
  fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem mapsTo_two_mul_sub : MapsTo (fun t : ℝ => 2 * t - 1) (Icc (1 / 2) 1) (Icc 0 1) :=
  fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem continuousOn_arcJoin (hu : ContinuousOn u (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (huv : u 1 = v 0) : ContinuousOn (arcJoin u v) (Icc 0 1) := by
  have h1 : ContinuousOn (arcJoin u v) (Icc 0 (1 / 2)) :=
    (hu.comp (continuous_const.mul continuous_id).continuousOn mapsTo_two_mul).congr
      arcJoin_eqOn_left
  have h2 : ContinuousOn (arcJoin u v) (Icc (1 / 2) 1) :=
    (hv.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
      mapsTo_two_mul_sub).congr (arcJoin_eqOn_right huv)
  have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this

theorem image_arcJoin (huv : u 1 = v 0) :
    arcJoin u v '' Icc 0 1 = u '' Icc 0 1 ∪ v '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h : t ≤ 1 / 2
    · exact Or.inl ⟨2 * t, mapsTo_two_mul ⟨ht.1, h⟩, (arcJoin_eqOn_left ⟨ht.1, h⟩).symm⟩
    · push Not at h
      exact Or.inr ⟨2 * t - 1, mapsTo_two_mul_sub ⟨h.le, ht.2⟩,
        (arcJoin_eqOn_right huv ⟨h.le, ht.2⟩).symm⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      rw [arcJoin_eqOn_left ⟨by linarith [hs.1], by linarith [hs.2]⟩]
      simp only
      congr 1; ring
    · refine ⟨(s + 1) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      rw [arcJoin_eqOn_right huv ⟨by linarith [hs.1], by linarith [hs.2]⟩]
      simp only
      congr 1; ring

theorem injOn_arcJoin (hui : InjOn u (Icc 0 1)) (hvi : InjOn v (Icc 0 1)) (huv : u 1 = v 0)
    (hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 1}) : InjOn (arcJoin u v) (Icc 0 1) := by
  -- the two halves
  have hL : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ 1 / 2 → arcJoin u v t = u (2 * t) := fun t ht h =>
    arcJoin_eqOn_left ⟨ht.1, h⟩
  have hR : ∀ t ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ t → arcJoin u v t = v (2 * t - 1) := fun t ht h =>
    arcJoin_eqOn_right huv ⟨h, ht.2⟩
  -- a common value of `u` and `v` is `u 1`, attained only at the junction
  have hcross : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, u s = v r → s = 1 ∧ r = 0 := by
    intro s hs r hr hsr
    have hmem : u s ∈ u '' Icc 0 1 ∩ v '' Icc 0 1 := ⟨⟨s, hs, rfl⟩, ⟨r, hr, hsr.symm⟩⟩
    have h1 : u s = u 1 := hint hmem
    have hs1 : s = 1 := hui hs ⟨zero_le_one, le_rfl⟩ h1
    refine ⟨hs1, hvi hr ⟨le_rfl, zero_le_one⟩ ?_⟩
    rw [← hsr, hs1, huv]
  intro t ht t' ht' htt'
  rcases le_total t (1 / 2) with h | h <;> rcases le_total t' (1 / 2) with h' | h'
  · rw [hL t ht h, hL t' ht' h'] at htt'
    have := hui (mapsTo_two_mul ⟨ht.1, h⟩) (mapsTo_two_mul ⟨ht'.1, h'⟩) htt'
    linarith
  · rw [hL t ht h, hR t' ht' h'] at htt'
    obtain ⟨h1, h2⟩ := hcross _ (mapsTo_two_mul ⟨ht.1, h⟩) _ (mapsTo_two_mul_sub ⟨h', ht'.2⟩)
      htt'
    linarith
  · rw [hR t ht h, hL t' ht' h'] at htt'
    obtain ⟨h1, h2⟩ := hcross _ (mapsTo_two_mul ⟨ht'.1, h'⟩) _ (mapsTo_two_mul_sub ⟨h, ht.2⟩)
      htt'.symm
    linarith
  · rw [hR t ht h, hR t' ht' h'] at htt'
    have := hvi (mapsTo_two_mul_sub ⟨h, ht.2⟩) (mapsTo_two_mul_sub ⟨h', ht'.2⟩) htt'
    linarith

end Join

section Rev

variable {u : ℝ → ℂ}

theorem arcRev_zero : arcRev u 0 = u 1 := by simp [arcRev]

theorem arcRev_one : arcRev u 1 = u 0 := by simp [arcRev]

theorem mapsTo_one_sub : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) :=
  fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem continuousOn_arcRev (hu : ContinuousOn u (Icc 0 1)) : ContinuousOn (arcRev u) (Icc 0 1) :=
  hu.comp (continuous_const.sub continuous_id).continuousOn mapsTo_one_sub

theorem injOn_arcRev (hu : InjOn u (Icc 0 1)) : InjOn (arcRev u) (Icc 0 1) := by
  intro t ht t' ht' h
  have := hu (mapsTo_one_sub ht) (mapsTo_one_sub ht') h
  linarith

theorem image_arcRev : arcRev u '' Icc 0 1 = u '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, mapsTo_one_sub ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, mapsTo_one_sub ht, by simp [arcRev]⟩

end Rev

/-! ### Real segments and circular arcs -/

/-- The straight path from `a` to `b`. -/
def segPath (a b : ℂ) (t : ℝ) : ℂ := a + (t : ℂ) * (b - a)

theorem segPath_zero (a b : ℂ) : segPath a b 0 = a := by simp [segPath]

theorem segPath_one (a b : ℂ) : segPath a b 1 = b := by simp [segPath]

theorem continuous_segPath (a b : ℂ) : Continuous (segPath a b) := by
  unfold segPath; fun_prop

theorem injOn_segPath {a b : ℂ} (hab : a ≠ b) : InjOn (segPath a b) (Icc 0 1) := by
  intro t _ t' _ h
  simp only [segPath, add_right_inj] at h
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  exact_mod_cast mul_right_cancel₀ hba h

/-- A segment between two real points is real, and lies between them. -/
theorem segPath_ofReal (x y t : ℝ) : segPath x y t = ((x + t * (y - x) : ℝ) : ℂ) := by
  simp [segPath]

theorem image_segPath_ofReal {x y : ℝ} (hxy : x ≤ y) :
    segPath x y '' Icc 0 1 = ofReal '' Icc x y := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨x + t * (y - x), ⟨?_, ?_⟩, (segPath_ofReal x y t).symm⟩
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  · rintro ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hxy with h | h
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      rw [segPath_zero]
      have : s = x := le_antisymm (h ▸ hs.2) hs.1
      rw [this]
    · refine ⟨(s - x) / (y - x), ⟨div_nonneg (by linarith [hs.1]) (by linarith),
        (div_le_one (by linarith)).2 (by linarith [hs.2])⟩, ?_⟩
      rw [segPath_ofReal]
      congr 1
      field_simp
      ring

theorem image_segPath_ofReal' {x y : ℝ} (hxy : y ≤ x) :
    segPath x y '' Icc 0 1 = ofReal '' Icc y x := by
  rw [← image_segPath_ofReal hxy]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, mapsTo_one_sub ht, by simp [segPath]; ring⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, mapsTo_one_sub ht, by simp [segPath]; ring⟩

/-- The circular arc of radius `R` from angle `θ₀` to angle `θ₁`. -/
def circPath (R θ₀ θ₁ : ℝ) (t : ℝ) : ℂ := (R : ℂ) * exp (((θ₀ + t * (θ₁ - θ₀) : ℝ) : ℂ) * I)

theorem continuous_circPath (R θ₀ θ₁ : ℝ) : Continuous (circPath R θ₀ θ₁) := by
  unfold circPath; fun_prop

theorem circPath_zero (R θ₀ θ₁ : ℝ) : circPath R θ₀ θ₁ 0 = (R : ℂ) * exp ((θ₀ : ℂ) * I) := by
  simp [circPath]

theorem circPath_one (R θ₀ θ₁ : ℝ) : circPath R θ₀ θ₁ 1 = (R : ℂ) * exp ((θ₁ : ℂ) * I) := by
  simp [circPath]

theorem norm_mul_exp_ofReal_mul_I {R : ℝ} (hR : 0 ≤ R) (φ : ℝ) :
    ‖(R : ℂ) * exp ((φ : ℂ) * I)‖ = R := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hR]

theorem im_mul_exp_ofReal_mul_I (R φ : ℝ) : ((R : ℂ) * exp ((φ : ℂ) * I)).im = R * Real.sin φ := by
  rw [exp_mul_I]
  simp [sin_ofReal_re]

theorem re_mul_exp_ofReal_mul_I (R φ : ℝ) : ((R : ℂ) * exp ((φ : ℂ) * I)).re = R * Real.cos φ := by
  rw [exp_mul_I]
  simp [cos_ofReal_re]

theorem eq_of_mul_exp_eq {R φ ψ : ℝ} (hR : 0 < R) (hφ : φ ∈ Ioc (-Real.pi) Real.pi)
    (hψ : ψ ∈ Ioc (-Real.pi) Real.pi)
    (h : (R : ℂ) * exp ((φ : ℂ) * I) = (R : ℂ) * exp ((ψ : ℂ) * I)) : φ = ψ := by
  have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR.ne'
  have h' := mul_left_cancel₀ hR' h
  have h1 : arg (exp ((φ : ℂ) * I)) = φ := by
    rw [exp_mul_I]; exact arg_cos_add_sin_mul_I hφ
  have h2 : arg (exp ((ψ : ℂ) * I)) = ψ := by
    rw [exp_mul_I]; exact arg_cos_add_sin_mul_I hψ
  rw [← h1, ← h2, h']

/-- The angles of `circPath R θ₀ θ₁` on `[0, 1]` lie between `θ₀` and `θ₁`. -/
theorem circPath_angle_mem {θ₀ θ₁ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    θ₀ + t * (θ₁ - θ₀) ∈ uIcc θ₀ θ₁ := by
  rcases le_total θ₀ θ₁ with h | h
  · rw [uIcc_of_le h]; constructor <;> nlinarith [ht.1, ht.2]
  · rw [uIcc_of_ge h]; constructor <;> nlinarith [ht.1, ht.2]

theorem injOn_circPath {R θ₀ θ₁ : ℝ} (hR : 0 < R) (hne : θ₀ ≠ θ₁)
    (h₀ : θ₀ ∈ Icc 0 Real.pi) (h₁ : θ₁ ∈ Icc 0 Real.pi) : InjOn (circPath R θ₀ θ₁) (Icc 0 1) := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, θ₀ + t * (θ₁ - θ₀) ∈ Ioc (-Real.pi) Real.pi := by
    intro t ht
    have := circPath_angle_mem (θ₀ := θ₀) (θ₁ := θ₁) ht
    have hpi := Real.pi_pos
    rcases le_total θ₀ θ₁ with h | h
    · rw [uIcc_of_le h] at this
      exact ⟨by linarith [this.1, h₀.1], by linarith [this.2, h₁.2]⟩
    · rw [uIcc_of_ge h] at this
      exact ⟨by linarith [this.1, h₁.1], by linarith [this.2, h₀.2]⟩
  intro t ht t' ht' h
  have := eq_of_mul_exp_eq hR (hmem t ht) (hmem t' ht') h
  have hd : θ₁ - θ₀ ≠ 0 := sub_ne_zero.2 hne.symm
  have : (t - t') * (θ₁ - θ₀) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_right hd
  linarith

theorem norm_circPath {R : ℝ} (hR : 0 ≤ R) (θ₀ θ₁ t : ℝ) : ‖circPath R θ₀ θ₁ t‖ = R :=
  norm_mul_exp_ofReal_mul_I hR _

theorem im_circPath (R θ₀ θ₁ t : ℝ) :
    (circPath R θ₀ θ₁ t).im = R * Real.sin (θ₀ + t * (θ₁ - θ₀)) :=
  im_mul_exp_ofReal_mul_I R _

theorem re_circPath (R θ₀ θ₁ t : ℝ) :
    (circPath R θ₀ θ₁ t).re = R * Real.cos (θ₀ + t * (θ₁ - θ₀)) :=
  re_mul_exp_ofReal_mul_I R _

/-! ### The two sides of a Jordan curve in `ℍ̄` -/

/-- The outer side of a Jordan curve `J ⊆ ℍ̄`: the component of `Jᶜ` containing `-I`. -/
def outerSide (J : Set ℂ) : Set ℂ := connectedComponentIn Jᶜ (-I)

/-- The inner side of a Jordan curve `J ⊆ ℍ̄`: the rest of `Jᶜ`. -/
def innerSide (J : Set ℂ) : Set ℂ := Jᶜ \ outerSide J

theorem neg_I_im : (-I : ℂ).im < 0 := by simp

theorem isPreconnected_lowerHalf : IsPreconnected {z : ℂ | z.im < 0} :=
  (convex_halfSpace_im_lt 0).isPreconnected

theorem lowerHalf_not_isBounded : ¬ IsBounded {z : ℂ | z.im < 0} := by
  intro hb
  obtain ⟨C, hC⟩ := hb.subset_closedBall 0
  set r : ℝ := |C| + 1 with hr
  have hr0 : 0 < r := by positivity
  have hm : ((-r : ℝ) : ℂ) * I ∈ {z : ℂ | z.im < 0} := by
    show (((-r : ℝ) : ℂ) * I).im < 0
    simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
    linarith
  have := hC hm
  rw [mem_closedBall, dist_zero_right, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
    abs_neg, abs_of_pos hr0] at this
  linarith [le_abs_self C]

section Sides

variable {J : Set ℂ}

theorem lowerHalf_subset_compl (hJH : J ⊆ Hbar) : {z : ℂ | z.im < 0} ⊆ Jᶜ := by
  intro z hz hzJ
  have h1 : 0 ≤ z.im := hJH hzJ
  have h2 : z.im < 0 := hz
  linarith

theorem lowerHalf_subset_outerSide (hJH : J ⊆ Hbar) : {z : ℂ | z.im < 0} ⊆ outerSide J :=
  isPreconnected_lowerHalf.subset_connectedComponentIn neg_I_im (lowerHalf_subset_compl hJH)

theorem outerSide_not_isBounded (hJH : J ⊆ Hbar) : ¬ IsBounded (outerSide J) :=
  fun hb => lowerHalf_not_isBounded (hb.subset (lowerHalf_subset_outerSide hJH))

/-- The Jordan curve theorem for `J ⊆ ℍ̄`, in terms of `innerSide` and `outerSide`. -/
theorem jordan_sides (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar) :
    (∃ x₁ ∈ Jᶜ, innerSide J = connectedComponentIn Jᶜ x₁) ∧ IsBounded (innerSide J) ∧
      frontier (innerSide J) = J ∧ frontier (outerSide J) = J ∧
      IsOpen (innerSide J) ∧ IsOpen (outerSide J) ∧ IsClosed J ∧
      IsPreconnected (innerSide J) ∧ IsPreconnected (outerSide J) := by
  obtain ⟨x₁, hx₁, x₀, hx₀, hb, hu, hdisj, hunion, hfr₁, hfr₀⟩ :=
    Foundations.Jordan.jordan_curve_components_complex hJ
  have hJc : IsClosed J := hfr₁ ▸ isClosed_frontier
  have hnI : (-I : ℂ) ∈ Jᶜ := lowerHalf_subset_compl hJH neg_I_im
  -- the outer side is the unbounded component
  have hout : outerSide J = connectedComponentIn Jᶜ x₀ := by
    have hnI' := hnI
    rw [hunion] at hnI'
    rcases hnI' with h | h
    · exfalso
      have heq : connectedComponentIn Jᶜ x₁ = connectedComponentIn Jᶜ (-I) :=
        connectedComponentIn_eq h
      exact outerSide_not_isBounded hJH (by rw [outerSide, ← heq]; exact hb)
    · exact (connectedComponentIn_eq h).symm
  have hin : innerSide J = connectedComponentIn Jᶜ x₁ := by
    ext z
    simp only [innerSide, Set.mem_sdiff, hout]
    constructor
    · rintro ⟨hz, h'⟩
      have hz' := hz
      rw [hunion] at hz'
      rcases hz' with h | h
      · exact h
      · exact absurd h h'
    · intro h
      exact ⟨connectedComponentIn_subset _ _ h, fun h' => hdisj.le_bot ⟨h, h'⟩⟩
  have hopen : IsOpen Jᶜ := hJc.isOpen_compl
  refine ⟨⟨x₁, hx₁, hin⟩, hin ▸ hb, hin ▸ hfr₁, hout ▸ hfr₀, hin ▸ hopen.connectedComponentIn,
    hout ▸ hopen.connectedComponentIn, hJc, hin ▸ isPreconnected_connectedComponentIn,
    isPreconnected_connectedComponentIn⟩

theorem compl_eq_innerSide_union_outerSide : Jᶜ = innerSide J ∪ outerSide J := by
  ext z
  constructor
  · intro hz
    by_cases h : z ∈ outerSide J
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩
  · rintro (h | h)
    · exact h.1
    · exact connectedComponentIn_subset _ _ h

theorem disjoint_innerSide_outerSide : Disjoint (innerSide J) (outerSide J) :=
  Set.disjoint_left.2 fun _ h h' => h.2 h'

theorem outerSide_subset_compl : outerSide J ⊆ Jᶜ := connectedComponentIn_subset _ _

theorem innerSide_subset_compl : innerSide J ⊆ Jᶜ := fun _ h => h.1

/-- Every point of `ℍ̄` off `J` near which the lower half-plane meets the same ball side is outer:
real points off `J` lie on the outer side. -/
theorem ofReal_mem_outerSide (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar)
    {x : ℝ} (hx : (x : ℂ) ∉ J) : (x : ℂ) ∈ outerSide J := by
  obtain ⟨-, -, -, -, -, -, hJc, -, -⟩ := jordan_sides hJ hJH
  obtain ⟨ε, hε, hεJ⟩ := Metric.isOpen_iff.1 hJc.isOpen_compl x hx
  have hball : ball (x : ℂ) ε ⊆ outerSide J := by
    have hlow : (x : ℂ) - ((ε / 2 : ℝ) : ℂ) * I ∈ ball (x : ℂ) ε ∩ outerSide J := by
      refine ⟨?_, lowerHalf_subset_outerSide hJH ?_⟩
      · rw [mem_ball, dist_eq, sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one, norm_real,
          Real.norm_of_nonneg (by positivity)]
        linarith
      · show ((x : ℂ) - ((ε / 2 : ℝ) : ℂ) * I).im < 0
        simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, add_zero, mul_one,
          zero_sub]
        linarith
    have hpre := (convex_ball (x : ℂ) ε).isPreconnected
    have h1 := hpre.subset_connectedComponentIn hlow.1 hεJ
    have h2 : connectedComponentIn Jᶜ (-I) = connectedComponentIn Jᶜ
        ((x : ℂ) - ((ε / 2 : ℝ) : ℂ) * I) := connectedComponentIn_eq hlow.2
    rw [outerSide, h2]
    exact h1
  exact hball (mem_ball_self hε)

/-- The inner side lies in `ℍ`. -/
theorem innerSide_subset_H (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar) :
    innerSide J ⊆ H := by
  intro z hz
  show 0 < z.im
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with h | h
  · exact hz.2 (lowerHalf_subset_outerSide hJH h)
  · have hzr : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h]
    rw [hzr] at hz
    exact hz.2 (ofReal_mem_outerSide hJ hJH hz.1)

/-- A bounded component of `Jᶜ` is the inner side. -/
theorem eq_innerSide_of_isBounded (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJH : J ⊆ Hbar)
    {x : ℂ} (hx : x ∈ Jᶜ) (hb : IsBounded (connectedComponentIn Jᶜ x)) :
    connectedComponentIn Jᶜ x = innerSide J := by
  have hx' := hx
  rw [compl_eq_innerSide_union_outerSide] at hx'
  rcases hx' with h | h
  · obtain ⟨⟨x₁, -, hin⟩, -⟩ := jordan_sides hJ hJH
    rw [hin] at h ⊢
    exact (connectedComponentIn_eq h).symm
  · exfalso
    have heq : connectedComponentIn Jᶜ (-I) = connectedComponentIn Jᶜ x := connectedComponentIn_eq h
    exact outerSide_not_isBounded hJH (by rw [outerSide, heq]; exact hb)

/-- An outer point is joined to `-I` off `J`. -/
theorem neg_I_mem_of_mem_outerSide {w : ℂ} (hw : w ∈ outerSide J) :
    (-I : ℂ) ∈ connectedComponentIn Jᶜ w := by
  rw [outerSide] at hw
  rw [← connectedComponentIn_eq hw]
  exact mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨w, hw⟩)

end Sides

end InteractingSLE.Sec6
