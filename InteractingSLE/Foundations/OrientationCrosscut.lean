/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.OrientationWinding
import InteractingSLE.WangWu.ChamberTheta

/-!
# The winding numbers of a disc crosscut closed by the upper semicircle

Packet PROVE-ORIENT. For a crosscut `α` of the unit disc from `−1` to `1` (`WangWu.IsDiscCrosscut`), the **reference
loop** `crossLoop α` runs along `α` from `−1` to `1` and back along the upper semicircle. Its winding number is `1` on
the upper side `crossSide α 1` (the left of `α`) and `0` on the lower side `crossSide α (−1)` (the right of `α`).

* `windNum_eq_zero_of_mem_jordanOut`: a loop inside `Γ ∪ jordanIn Γ` has winding number `0` at the points of
  `jordanOut Γ` (their component of `ℂ \ Γ` is unbounded and avoids `jordanIn Γ`);
* `windNum_eq_zero_of_mem_crossSide_neg`: hence `0` on the lower side, for every loop in the closed upper side;
* **`windNum_crossLoop_of_mem_crossSide_one`**: `1` on the upper side, by the crossing lemma at `i` against the
  clockwise unit circle (winding number `−1` inside, `0` outside), which runs along the upper semicircle in the other
  direction.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped Real

open QuantumZipper.CA.Topo (HasLogOn hasLogOn_of_arc two_pi_I_ne_zero')
open InteractingSLE.WangWu (IsDiscCrosscut crossRange crossSide semiArc jordanIn jordanOut upperParam)

namespace InteractingSLE.Orientation

/-! ### Points outside a closed curve -/

/-- **A loop in `Γ ∪ jordanIn Γ` has winding number `0` on `jordanOut Γ`.** -/
theorem windNum_eq_zero_of_mem_jordanOut {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1)
    {Γ : Set ℂ} (hγΓ : γ '' Icc 0 1 ⊆ Γ ∪ jordanIn Γ) {w : ℂ} (hw : w ∈ jordanOut Γ) : windNum γ w = 0 := by
  set Q := connectedComponentIn Γᶜ w
  have hQΓ : Q ⊆ Γᶜ := connectedComponentIn_subset _ _
  refine windNum_eq_zero_of_isPreconnected hγ hl isPreconnected_connectedComponentIn hw.2 ?_
    (mem_connectedComponentIn hw.1)
  refine Set.disjoint_left.2 fun z hzQ hzγ => ?_
  rcases hγΓ hzγ with h | h
  · exact hQΓ hzQ h
  · have he : connectedComponentIn Γᶜ z = Q := connectedComponentIn_eq hzQ |>.symm
    have hb := h.2
    rw [he] at hb
    exact hw.2 hb

/-! ### The reference loop of a crosscut -/

/-- The **reference loop** of a crosscut `α`: along `α` from `−1` to `1` for `t ∈ [0, 1/2]`, then back along the
upper semicircle `t ↦ e^{iπ(2t − 1)}` from `1` to `−1`. -/
def crossLoop (α : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then α (2 * t) else exp (((π * (2 * t - 1) : ℝ) : ℂ) * I)

/-- The **clockwise unit circle** `t ↦ e^{−2πit}`. -/
def cwLoop (t : ℝ) : ℂ := exp (((-(2 * π * t)) : ℝ) * I)

theorem continuous_cwLoop : Continuous cwLoop := by unfold cwLoop; fun_prop

theorem norm_cwLoop (t : ℝ) : ‖cwLoop t‖ = 1 := norm_exp_ofReal_mul_I _

theorem cwLoop_zero : cwLoop 0 = 1 := by simp [cwLoop]

theorem cwLoop_half : cwLoop (1 / 2) = -1 := by
  rw [cwLoop, show (-(2 * π * (1 / 2)) : ℝ) = -π by ring, ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I]
  norm_num

theorem cwLoop_one : cwLoop 1 = 1 := by
  rw [cwLoop, show (-(2 * π * 1) : ℝ) = -(2 * π) by ring, ofReal_neg, neg_mul, exp_neg]
  push_cast
  rw [exp_two_pi_mul_I, inv_one]

theorem im_cwLoop (t : ℝ) : (cwLoop t).im = -Real.sin (2 * π * t) := by
  rw [cwLoop, exp_ofReal_mul_I_im, Real.sin_neg]

/-- The clockwise circle winds `−1` times about the points of the open disc. -/
theorem windNum_cwLoop {w : ℂ} (hw : ‖w‖ < 1) : windNum cwLoop w = -1 := by
  have hc : ContinuousOn cwLoop (Icc 0 1) := continuous_cwLoop.continuousOn
  have hl : cwLoop 0 = cwLoop 1 := by rw [cwLoop_zero, cwLoop_one]
  have h0 : ∀ t ∈ Icc (0 : ℝ) 1, cwLoop t ≠ 0 := fun t _ h => by
    have := norm_cwLoop t; rw [h, norm_zero] at this; exact zero_ne_one this
  rw [windNum_eq_of_norm_sub_lt hc hl (w := 0) fun t _ => by
    rw [zero_sub, norm_neg, sub_zero, norm_cwLoop]; exact hw]
  have hs := windNum_spec hc h0 hl (L := fun t => ((-(2 * π * t)) : ℝ) * I) (by fun_prop)
    fun t _ => by rw [sub_zero]; rfl
  have : ((windNum cwLoop 0 : ℤ) : ℂ) * (2 * π * I) = ((-1 : ℤ) : ℂ) * (2 * π * I) := by
    rw [← hs]; push_cast; ring
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero' this

theorem cwLoop_mem_semiArc {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) : cwLoop t ∈ semiArc 1 := by
  refine ⟨norm_cwLoop t, ?_⟩
  rw [one_mul, im_cwLoop, neg_nonneg]
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * π * t - π)
    (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])
  rw [Real.sin_sub_pi] at h
  linarith

theorem im_cwLoop_nonpos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) : (cwLoop t).im ≤ 0 := by
  rw [im_cwLoop, neg_nonpos]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])

variable {α : ℝ → ℂ}

theorem crossLoop_of_le {t : ℝ} (ht : t ≤ 1 / 2) : crossLoop α t = α (2 * t) := by
  simp only [crossLoop, ht, ↓reduceIte]

theorem crossLoop_of_ge (hα1 : α 1 = 1) {t : ℝ} (ht : 1 / 2 ≤ t) :
    crossLoop α t = exp (((π * (2 * t - 1) : ℝ) : ℂ) * I) := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, crossLoop_of_le le_rfl]
    norm_num [hα1]
  · have h' : ¬ t ≤ 1 / 2 := not_le.2 h
    simp only [crossLoop, h', ↓reduceIte]

theorem continuousOn_crossLoop (hαc : ContinuousOn α (Icc 0 1)) (hα1 : α 1 = 1) :
    ContinuousOn (crossLoop α) (Icc 0 1) := by
  have h1 : ContinuousOn (crossLoop α) (Icc 0 (1 / 2)) := by
    refine ContinuousOn.congr (f := fun t => α (2 * t)) ?_ fun t ht => crossLoop_of_le ht.2
    exact hαc.comp (continuous_const.mul continuous_id).continuousOn fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : ContinuousOn (crossLoop α) (Icc (1 / 2) 1) := by
    refine ContinuousOn.congr (f := fun t => exp (((π * (2 * t - 1) : ℝ) : ℂ) * I)) (by fun_prop)
      fun t ht => crossLoop_of_ge hα1 ht.1
  have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this

theorem crossLoop_zero (hα0 : α 0 = -1) : crossLoop α 0 = -1 := by
  rw [crossLoop_of_le (by norm_num), mul_zero, hα0]

theorem crossLoop_half (hα1 : α 1 = 1) : crossLoop α (1 / 2) = 1 := by
  rw [crossLoop_of_le le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, hα1]

theorem crossLoop_one (hα1 : α 1 = 1) : crossLoop α 1 = -1 := by
  rw [crossLoop_of_ge hα1 (by norm_num), show π * (2 * 1 - 1) = π by ring, exp_pi_mul_I]

theorem crossLoop_loop (hα0 : α 0 = -1) (hα1 : α 1 = 1) : crossLoop α 0 = crossLoop α 1 := by
  rw [crossLoop_zero hα0, crossLoop_one hα1]

theorem crossLoop_mem_semiArc (hα1 : α 1 = 1) {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    crossLoop α t ∈ semiArc 1 := by
  rw [crossLoop_of_ge hα1 ht.1]
  refine ⟨norm_exp_ofReal_mul_I _, ?_⟩
  rw [one_mul, exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])

theorem crossLoop_mem_crossRange {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) : crossLoop α t ∈ crossRange α := by
  rw [crossLoop_of_le ht.2]
  exact ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩

theorem image_crossLoop_subset (hα1 : α 1 = 1) :
    crossLoop α '' Icc 0 1 ⊆ crossRange α ∪ semiArc 1 := by
  rintro _ ⟨t, ht, rfl⟩
  rcases le_total t (1 / 2) with h | h
  · exact Or.inl (crossLoop_mem_crossRange ⟨ht.1, h⟩)
  · exact Or.inr (crossLoop_mem_semiArc hα1 ⟨h, ht.2⟩)

/-- The lower side lies outside `α ∪ (upper semicircle)`. -/
theorem crossSide_neg_subset_jordanOut (hα : IsDiscCrosscut α) :
    crossSide α (-1) ⊆ jordanOut (crossRange α ∪ semiArc 1) := by
  intro w hw
  have hwb := hα.crossSide_subset (Or.inr rfl) hw
  have hwΓ : w ∉ crossRange α ∪ semiArc 1 := by
    rintro (h | h)
    · exact hwb.2 h
    · have := hwb.1; rw [mem_ball, dist_zero_right, h.1] at this; exact lt_irrefl _ this
  have hwc : w ∈ (crossRange α ∪ semiArc 1)ᶜ := hwΓ
  rw [WangWu.compl_eq_jordanIn_union_jordanOut] at hwc
  rcases hwc with h | h
  · exact absurd hw (Set.disjoint_left.1 hα.disjoint_crossSide h)
  · exact h

/-- **Every loop in the closed upper side has winding number `0` on the lower side.** -/
theorem windNum_eq_zero_of_mem_crossSide_neg (hα : IsDiscCrosscut α) {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hl : γ 0 = γ 1) (hγα : γ '' Icc 0 1 ⊆ closure (crossSide α 1)) {w : ℂ} (hw : w ∈ crossSide α (-1)) :
    windNum γ w = 0 := by
  refine windNum_eq_zero_of_mem_jordanOut hγ hl (fun z hz => ?_) (crossSide_neg_subset_jordanOut hα hw)
  have h := hγα hz
  rw [hα.closure_crossSide (Or.inl rfl)] at h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The upper semicircle carries continuous logarithms of `z - w` for `w` off it (an arc). -/
theorem hasLogOn_semiArc {w : ℂ} (hw : w ∉ semiArc 1) : HasLogOn (fun z => z - w) (semiArc 1) := by
  rw [← WangWu.image_upperParam]
  refine hasLogOn_of_arc WangWu.continuous_upperParam.continuousOn WangWu.injOn_upperParam
    (by fun_prop) fun z hz h => hw ?_
  rw [← WangWu.image_upperParam, ← sub_eq_zero.1 h]
  exact hz

/-- **The reference loop winds once about a set on the left of `α`**: a preconnected set `K` of the open disc off
`α([0, 1])` whose closure contains a point `u` of the open upper semicircle off `α`. (Crossing lemma at `u` against the
clockwise unit circle, then constancy on `K`.) Here `α` is any path from `−1` to `1` in the closed disc; it may touch
the circle. -/
theorem windNum_crossLoop_eq_one_of_mem_closure (hαc : ContinuousOn α (Icc 0 1)) (hα0 : α 0 = -1)
    (hα1 : α 1 = 1) (hαD : crossRange α ⊆ closedBall 0 1) {K : Set ℂ} (hK : IsPreconnected K)
    (hKD : K ⊆ ball 0 1) (hKα : Disjoint K (crossRange α)) {u : ℂ} (hu : u ∈ closure K) (hun : ‖u‖ = 1)
    (hui : 0 < u.im) (huα : u ∉ crossRange α) {w : ℂ} (hw : w ∈ K) : windNum (crossLoop α) w = 1 := by
  have hγ := continuousOn_crossLoop hαc hα1
  have hγl := crossLoop_loop hα0 hα1
  have hδ : ContinuousOn cwLoop (Icc 0 1) := continuous_cwLoop.continuousOn
  have hδl : cwLoop 0 = cwLoop 1 := by rw [cwLoop_zero, cwLoop_one]
  have himg : crossLoop α '' Icc 0 1 ⊆ closedBall 0 1 := fun z hz => by
    rcases image_crossLoop_subset hα1 hz with h | h
    · exact hαD h
    · rw [mem_closedBall, dist_zero_right, h.1]
  -- the crossing at `u`
  have hp : u ∉ crossLoop α '' Icc 0 (1 / 2) ∪ crossLoop α '' Icc 1 1 ∪ cwLoop '' Icc 0 (1 / 2) ∪
      cwLoop '' Icc 1 1 := by
    rintro (((⟨t, ht, he⟩ | ⟨t, ht, he⟩) | ⟨t, ht, he⟩) | ⟨t, ht, he⟩)
    · exact huα (he ▸ crossLoop_mem_crossRange ht)
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, crossLoop_one hα1] at he
      rw [← he] at hui; simp at hui
    · have h := im_cwLoop_nonpos ht
      rw [he] at h
      linarith
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, cwLoop_one] at he
      rw [← he] at hui; simp at hui
  obtain ⟨ε, hε, hcross⟩ := windNum_add_windNum_eq hγ hδ hγl hδl (A := semiArc 1)
    (fun w hw => hasLogOn_semiArc hw) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl
    (fun t ht => crossLoop_mem_semiArc hα1 ht) (fun t ht => cwLoop_mem_semiArc ht)
    (by rw [crossLoop_half hα1, cwLoop_one]) (by rw [crossLoop_one hα1, cwLoop_half]) hp
  obtain ⟨w₁, hw₁K, hw₁u⟩ := Metric.mem_closure_iff.1 hu ε hε
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  set w₂ : ℂ := ((1 + η : ℝ) : ℂ) * u
  have hn₂ : ‖w₂‖ = 1 + η := by
    simp only [w₂, norm_mul, hun, mul_one, norm_real, Real.norm_eq_abs]; exact abs_of_pos (by linarith)
  have hd₂ : dist w₂ u = η := by
    rw [dist_eq_norm, show w₂ - u = ((η : ℝ) : ℂ) * u by simp only [w₂]; push_cast; ring, norm_mul, hun,
      mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hη0]
  have hn₁ : ‖w₁‖ < 1 := mem_ball_zero_iff.1 (hKD hw₁K)
  have hw₁A : w₁ ∉ semiArc 1 := fun h => by have := h.1; linarith
  have hw₂A : w₂ ∉ semiArc 1 := fun h => by have := h.1; rw [hn₂] at this; linarith
  have key := hcross w₁ (by rw [mem_ball, dist_comm]; exact hw₁u) w₂ (by rw [mem_ball, hd₂]; linarith)
    hw₁A hw₂A
  have hγ₂ : windNum (crossLoop α) w₂ = 0 := windNum_eq_zero_of_norm_lt hγ hγl fun t ht => by
    rw [hn₂]
    have h := himg ⟨t, ht, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h
    linarith
  have hδ₂ : windNum cwLoop w₂ = 0 := windNum_eq_zero_of_norm_lt hδ hδl fun t _ => by
    rw [hn₂, norm_cwLoop]; linarith
  rw [hγ₂, hδ₂, windNum_cwLoop hn₁] at key
  have h1 : windNum (crossLoop α) w₁ = 1 := by linarith
  rw [windNum_eq_of_isPreconnected hγ hγl hK ?_ hw hw₁K, h1]
  refine Set.disjoint_left.2 fun z hz hzγ => ?_
  rcases image_crossLoop_subset hα1 hzγ with h | h
  · exact Set.disjoint_left.1 hKα hz h
  · have := hKD hz; rw [mem_ball, dist_zero_right, h.1] at this; exact lt_irrefl _ this

/-- **The reference loop winds once about the points of the upper side** of a crosscut. -/
theorem windNum_crossLoop_of_mem_crossSide_one (hα : IsDiscCrosscut α) {w : ℂ} (hw : w ∈ crossSide α 1) :
    windNum (crossLoop α) w = 1 := by
  have hIα : I ∉ crossRange α := fun h => by
    rcases hα.eq_of_mem_crossRange_of_norm h norm_I with h' | h'
    · have := congrArg Complex.im h'; simp at this
    · have := congrArg Complex.im h'; simp at this
  refine windNum_crossLoop_eq_one_of_mem_closure hα.cont hα.zero hα.one hα.crossRange_subset_closedBall
    (hα.isPreconnected_crossSide (Or.inl rfl)) (fun z hz => (hα.crossSide_subset (Or.inl rfl) hz).1)
    (Set.disjoint_left.2 fun z hz => (hα.crossSide_subset (Or.inl rfl) hz).2)
    (hα.semiArc_subset_closure_crossSide (Or.inl rfl) ⟨norm_I, by simp⟩) norm_I (by simp) hIα hw

end InteractingSLE.Orientation
