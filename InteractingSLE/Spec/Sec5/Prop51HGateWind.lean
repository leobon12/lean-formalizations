/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.OrientationCrosscut

/-!
# Winding-number tools for the separation step of Proposition 5.1's forward route

Packet PROVE-PROP51H-TOPO2 (ruling R71: Astra's follow-up 4, Part (1), §1.7). Generic planar facts used to prove
the deterministic no-wrap statement `Prop51G.FwdNoWrapQStatement` by counting winding numbers of the completed
excursion crosscuts along one compact chart path:

* `windNum_affine`: the winding number is invariant under `z ↦ c + d z` (`d ≠ 0`);
* `windNum_crossLoop_diam`: the reference loop of the diameter `[-1, 1]` winds once about the upper half-disc;
* **`windNum_jump_real`**: a loop that runs to the right along a real segment `[x - δ, x + δ]` and otherwise avoids
  `x` has winding number one larger just above `x` than just below it (crossing lemma against the reflected
  half-disc loop);
* `isPathConnected_H_diff`: `ℍ` minus a point is path connected;
* **`eq_of_locally_const_along`**: an integer function which is locally constant near every point of a compact path,
  off a set that is nowhere locally full near the path, takes the same value at the two ends.

Deterministic; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open scoped Real
open QuantumZipper (H)
open QuantumZipper.CA.Topo (HasLogOn two_pi_I_ne_zero')
open InteractingSLE.WangWu (crossRange semiArc)

namespace InteractingSLE.Sec5.Prop51HGate

open _root_.InteractingSLE.Orientation

/-! ### Affine invariance -/

/-- **The winding number is invariant under a complex affine map.** -/
theorem windNum_affine {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1) {z c d : ℂ}
    (hd : d ≠ 0) (hz : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z) :
    windNum (fun t => c + d * γ t) (c + d * z) = windNum γ z := by
  obtain ⟨L, hLc, hL⟩ := exists_lift hγ hz
  have hγ' : ContinuousOn (fun t => c + d * γ t) (Icc 0 1) :=
    continuousOn_const.add (continuousOn_const.mul hγ)
  have hz' : ∀ t ∈ Icc (0 : ℝ) 1, c + d * γ t ≠ c + d * z := fun t ht h =>
    hz t ht (mul_left_cancel₀ hd (add_left_cancel h))
  have h1 := windNum_spec hγ hz hl hLc hL
  have h2 := windNum_spec hγ' hz' (by simp only [hl]) (L := fun t => Complex.log d + L t)
    (continuousOn_const.add hLc) (fun t ht => by
      rw [Complex.exp_add, Complex.exp_log hd, hL t ht]; ring)
  have h3 : ((windNum (fun t => c + d * γ t) (c + d * z) : ℤ) : ℂ) * (2 * π * I) =
      (windNum γ z : ℂ) * (2 * π * I) := by
    rw [← h1, ← h2]; ring
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero' h3

/-! ### The diameter loop -/

/-- The diameter `[-1, 1]` of the unit disc, from `-1` to `1`. -/
def diam (u : ℝ) : ℂ := ((2 * u - 1 : ℝ) : ℂ)

theorem continuous_diam : Continuous diam := by unfold diam; fun_prop

theorem diam_zero : diam 0 = -1 := by simp [diam]

theorem diam_one : diam 1 = 1 := by norm_num [diam]

theorem im_diam (u : ℝ) : (diam u).im = 0 := by simp [diam]

/-- The reference loop of the diameter winds once about the open upper half-disc. -/
theorem windNum_crossLoop_diam {z : ℂ} (hz : ‖z‖ < 1) (hzi : 0 < z.im) :
    windNum (crossLoop diam) z = 1 := by
  set K : Set ℂ := ball 0 1 ∩ {w : ℂ | 0 < w.im} with hK
  have hKc : Convex ℝ K := (convex_ball 0 1).inter
    (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0)
  have hIK : I ∈ closure K := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    set r : ℝ := min ε 1 / 2 with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := by linarith [min_le_right ε 1]
    refine ⟨((1 - r : ℝ) : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · show 0 < (((1 - r : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith
    · rw [dist_eq_norm, show I - ((1 - r : ℝ) : ℂ) * I = ((r : ℝ) : ℂ) * I by push_cast; ring,
        norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      linarith [min_le_left ε 1]
  have hIα : I ∉ crossRange diam := by
    rintro ⟨u, -, hu⟩
    have := congrArg Complex.im hu
    rw [im_diam] at this
    simp at this
  refine windNum_crossLoop_eq_one_of_mem_closure continuous_diam.continuousOn diam_zero diam_one ?_
    hKc.isPreconnected (fun w hw => hw.1) ?_ hIK norm_I (by simp) hIα ⟨mem_ball_zero_iff.2 hz, hzi⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [mem_closedBall, dist_zero_right, diam, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  · refine Set.disjoint_left.2 fun w hw hwα => ?_
    obtain ⟨u, -, rfl⟩ := hwα
    have := hw.2
    rw [Set.mem_ofPred_eq, im_diam] at this
    exact lt_irrefl _ this

/-! ### The jump across a real segment -/

/-- The common real segment `[x - δ, x + δ]`, as the image of an affine parametrization of `[0, 1]`. -/
def realSeg (x δ : ℝ) : Set ℂ := (fun u : ℝ => ((x + δ * (2 * u - 1) : ℝ) : ℂ)) '' Icc 0 1

theorem ofReal_mem_realSeg {x δ y : ℝ} (hδ : 0 < δ) (hy : y ∈ Icc (x - δ) (x + δ)) :
    (y : ℂ) ∈ realSeg x δ := by
  refine ⟨(y - x + δ) / (2 * δ), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hy.1]) (by positivity)
  · rw [div_le_one (by positivity)]; linarith [hy.2]
  · field_simp
    ring_nf

theorem im_of_mem_realSeg {x δ : ℝ} {z : ℂ} (hz : z ∈ realSeg x δ) : z.im = 0 := by
  obtain ⟨u, -, rfl⟩ := hz
  simp

theorem hasLogOn_realSeg {x δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : w ∉ realSeg x δ) :
    HasLogOn (fun z => z - w) (realSeg x δ) := by
  refine hasLogOn_sub_image_Icc zero_lt_one (by fun_prop) ?_ hw
  intro u _ v _ he
  have h := congrArg Complex.re he
  simp only [ofReal_re] at h
  have : δ * (2 * u - 1) = δ * (2 * v - 1) := by linarith
  have := mul_left_cancel₀ hδ.ne' this
  linarith

/-- The reflected half-disc loop at `x`: along the real segment from `x + δ` to `x - δ`, then along the lower
semicircle back to `x + δ` (positively oriented about the lower half-disc). -/
def jumpLoop (x δ : ℝ) (t : ℝ) : ℂ := (x : ℂ) + (-(δ : ℂ)) * crossLoop diam t

theorem continuousOn_jumpLoop (x δ : ℝ) : ContinuousOn (jumpLoop x δ) (Icc 0 1) :=
  continuousOn_const.add (continuousOn_const.mul (continuousOn_crossLoop continuous_diam.continuousOn diam_one))

theorem jumpLoop_loop (x δ : ℝ) : jumpLoop x δ 0 = jumpLoop x δ 1 := by
  simp only [jumpLoop, crossLoop_loop diam_zero diam_one]

theorem im_jumpLoop_nonpos {x δ : ℝ} (hδ : 0 ≤ δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (jumpLoop x δ t).im ≤ 0 := by
  have h : 0 ≤ (crossLoop diam t).im := by
    rcases image_crossLoop_subset diam_one ⟨t, ht, rfl⟩ with h | h
    · obtain ⟨u, -, hu⟩ := h
      rw [← hu, im_diam]
    · exact (one_mul (crossLoop diam t).im) ▸ h.2
  simp only [jumpLoop, add_im, ofReal_im, mul_im, neg_re, ofReal_re, neg_im, zero_add]
  nlinarith

/-- **The jump of the winding number across a real segment traversed to the right.** If a loop `γ` runs along
`[x - δ, x + δ]` from `x - δ` to `x + δ` on `[s₀, s₁]` and its remaining part avoids `x`, then just above `x` its
winding number is one larger than just below `x`. -/
theorem windNum_jump_real {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1) {s₀ s₁ x δ : ℝ}
    (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s₁) (hs₁ : s₁ ≤ 1) (hδ : 0 < δ)
    (hseg : ∀ t ∈ Icc s₀ s₁, ∃ y ∈ Icc (x - δ) (x + δ), γ t = (y : ℂ))
    (hγ₀ : γ s₀ = ((x - δ : ℝ) : ℂ)) (hγ₁ : γ s₁ = ((x + δ : ℝ) : ℂ))
    (hrest : (x : ℂ) ∉ γ '' Icc 0 s₀ ∪ γ '' Icc s₁ 1) :
    ∃ ε > 0, ∀ e : ℝ, 0 < e → e < ε → windNum γ (x + e * I) = windNum γ (x - e * I) + 1 := by
  have hm := continuousOn_jumpLoop x δ
  have hml := jumpLoop_loop x δ
  have hγA : MapsTo γ (Icc s₀ s₁) (realSeg x δ) := fun t ht => by
    obtain ⟨y, hy, he⟩ := hseg t ht
    rw [he]
    exact ofReal_mem_realSeg hδ hy
  have hmA : MapsTo (jumpLoop x δ) (Icc 0 (1 / 2)) (realSeg x δ) := fun t ht => by
    refine ⟨1 - 2 * t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    simp only [jumpLoop, crossLoop_of_le ht.2, diam]
    push_cast
    ring
  have h₀ : γ s₀ = jumpLoop x δ (1 / 2) := by
    rw [hγ₀, jumpLoop, crossLoop_half diam_one]
    push_cast; ring
  have h₁ : γ s₁ = jumpLoop x δ 0 := by
    rw [hγ₁, jumpLoop, crossLoop_zero diam_zero]
    push_cast; ring
  have hp : (x : ℂ) ∉ γ '' Icc 0 s₀ ∪ γ '' Icc s₁ 1 ∪ jumpLoop x δ '' Icc 0 0 ∪
      jumpLoop x δ '' Icc (1 / 2) 1 := by
    rintro ((h | ⟨t, ht, he⟩) | ⟨t, ht, he⟩)
    · exact hrest h
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, ← h₁, hγ₁] at he
      have := congrArg Complex.re he
      simp only [ofReal_re] at this
      linarith
    · have hn := (crossLoop_mem_semiArc diam_one ht).1
      have : (x : ℂ) + (-(δ : ℂ)) * crossLoop diam t - x = 0 := by
        rw [show jumpLoop x δ t = (x : ℂ) + (-(δ : ℂ)) * crossLoop diam t from rfl] at he
        rw [he]; ring
      have h2 : ‖(-(δ : ℂ)) * crossLoop diam t‖ = δ := by
        rw [norm_mul, hn, mul_one, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      rw [add_sub_cancel_left] at this
      rw [this, norm_zero] at h2
      exact hδ.ne h2
  obtain ⟨ε, hε, hcross⟩ := windNum_add_windNum_eq hγ hm hl hml (A := realSeg x δ)
    (fun w hw => hasLogOn_realSeg hδ hw) hs₀ hs hs₁ le_rfl (by norm_num) (by norm_num) hγA hmA h₀ h₁ hp
  refine ⟨min ε δ, lt_min hε hδ, fun e he heε => ?_⟩
  have heε' : e < ε := heε.trans_le (min_le_left _ _)
  have heδ : e < δ := heε.trans_le (min_le_right _ _)
  have hdist : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → (x : ℂ) + σ * e * I ∈ ball (x : ℂ) ε := by
    intro σ hσ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    rcases hσ with rfl | rfl
    · simp only [ofReal_one, one_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
        abs_of_pos he]
      exact heε'
    · simp only [ofReal_neg, ofReal_one, neg_mul, one_mul, norm_neg, norm_mul, norm_real,
        Real.norm_eq_abs, norm_I, mul_one, abs_of_pos he]
      exact heε'
  have hnotA : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → (x : ℂ) + σ * e * I ∉ realSeg x δ := by
    intro σ hσ h
    have := im_of_mem_realSeg h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at this
    rcases hσ with rfl | rfl <;> simp at this <;> linarith
  have key := hcross _ (hdist 1 (Or.inl rfl)) _ (hdist (-1) (Or.inr rfl)) (hnotA 1 (Or.inl rfl))
    (hnotA (-1) (Or.inr rfl))
  have hup : (x : ℂ) + ((1 : ℝ) : ℂ) * e * I = x + e * I := by push_cast; ring
  have hdn : (x : ℂ) + ((-1 : ℝ) : ℂ) * e * I = x - e * I := by push_cast; ring
  rw [hup, hdn] at key
  -- the jump loop: `0` above (it lies in the closed lower half-plane), `1` below
  have hm_up : windNum (jumpLoop x δ) (x + e * I) = 0 := by
    have hH : IsPreconnected H :=
      (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).isPreconnected
    have hHu : ¬ IsBounded H := by
      intro hb
      obtain ⟨R, hR⟩ := hb.exists_norm_le
      have h := hR (((|R| + 1 : ℝ) : ℂ) * I) (by
        show (0 : ℝ) < (((|R| + 1 : ℝ) : ℂ) * I).im
        simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        positivity)
      rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
      linarith [le_abs_self R]
    refine windNum_eq_zero_of_isPreconnected hm hml hH hHu ?_ ?_
    · refine Set.disjoint_left.2 fun z hz hzm => ?_
      obtain ⟨t, ht, rfl⟩ := hzm
      exact absurd (im_jumpLoop_nonpos hδ.le ht) (not_le.2 hz)
    · show (0 : ℝ) < ((x : ℂ) + e * I).im
      simp [he]
  have hm_dn : windNum (jumpLoop x δ) (x - e * I) = 1 := by
    set z : ℂ := ((e / δ : ℝ) : ℂ) * I with hz
    have hzn : ‖z‖ < 1 := by
      rw [hz, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_lt_one hδ]
      exact heδ
    have hzi : 0 < z.im := by
      rw [hz]; simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      positivity
    have hzoff : ∀ t ∈ Icc (0 : ℝ) 1, crossLoop diam t ≠ z := by
      intro t ht h
      rcases image_crossLoop_subset diam_one ⟨t, ht, rfl⟩ with h' | h'
      · obtain ⟨u, -, hu⟩ := h'
        rw [h] at hu
        have := congrArg Complex.im hu
        rw [im_diam] at this
        linarith
      · rw [h] at h'
        linarith [h'.1]
    have h := windNum_affine (continuousOn_crossLoop continuous_diam.continuousOn diam_one)
      (crossLoop_loop diam_zero diam_one) (c := (x : ℂ)) (d := -(δ : ℂ))
      (neg_ne_zero.2 (ofReal_ne_zero.2 hδ.ne')) hzoff
    rw [windNum_crossLoop_diam hzn hzi] at h
    have hδ' : (δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hδ.ne'
    have he' : (x : ℂ) + -(δ : ℂ) * z = x - e * I := by
      rw [hz]; push_cast; field_simp; ring
    rw [he'] at h
    exact h
  rw [hm_up, hm_dn] at key
  linarith

/-! ### `ℍ` minus a point is path connected -/

theorem isPathConnected_H_diff (q : ℂ) : IsPathConnected (H \ {q}) := by
  have hcv : ∀ S : Set ℂ, Convex ℝ S → S.Nonempty → IsPathConnected S := fun S hS hne =>
    hS.isPathConnected hne
  have him : ∀ r : ℝ, Convex ℝ {z : ℂ | r < z.im} := fun r =>
    convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear r
  have himl : ∀ r : ℝ, Convex ℝ {z : ℂ | z.im < r} := fun r =>
    convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear r
  have hrel : ∀ r : ℝ, Convex ℝ {z : ℂ | z.re < r} := fun r =>
    convex_halfSpace_lt (f := fun w : ℂ => w.re) Complex.reLm.isLinear r
  have hreg : ∀ r : ℝ, Convex ℝ {z : ℂ | r < z.re} := fun r =>
    convex_halfSpace_gt (f := fun w : ℂ => w.re) Complex.reLm.isLinear r
  by_cases hq : q.im ≤ 0
  · have he : H \ {q} = {z : ℂ | 0 < z.im} := by
      ext z
      refine ⟨fun h => h.1, fun h => ⟨h, fun he => ?_⟩⟩
      rw [mem_singleton_iff] at he
      have : (0 : ℝ) < z.im := h
      rw [he] at this
      linarith
    rw [he]
    exact hcv _ (him 0) ⟨I, by simp⟩
  push Not at hq
  set U₁ : Set ℂ := {z | 0 < z.im} ∩ {z | z.re < q.re}
  set U₂ : Set ℂ := {z | 0 < z.im} ∩ {z | q.re < z.re}
  set U₃ : Set ℂ := {z | q.im < z.im}
  set U₄ : Set ℂ := {z | 0 < z.im} ∩ {z | z.im < q.im}
  have hpt : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * I).re = a ∧ ((a : ℂ) + (b : ℂ) * I).im = b := by
    intro a b; simp
  have h₁ : IsPathConnected U₁ := hcv _ ((him 0).inter (hrel _))
    ⟨(q.re - 1 : ℝ) + (q.im : ℂ) * I, by simp [U₁, hq]⟩
  have h₂ : IsPathConnected U₂ := hcv _ ((him 0).inter (hreg _))
    ⟨(q.re + 1 : ℝ) + (q.im : ℂ) * I, by simp [U₂, hq]⟩
  have h₃ : IsPathConnected U₃ := hcv _ (him _) ⟨(q.re : ℂ) + ((q.im + 1 : ℝ) : ℂ) * I, by simp [U₃]⟩
  have h₄ : IsPathConnected U₄ := hcv _ ((him 0).inter (himl _))
    ⟨(q.re : ℂ) + ((q.im / 2 : ℝ) : ℂ) * I, by simp [U₄, hq]⟩
  have h₁₃ : IsPathConnected (U₁ ∪ U₃) := h₁.union h₃
    ⟨((q.re - 1 : ℝ) : ℂ) + ((q.im + 1 : ℝ) : ℂ) * I, by simp [U₁, U₃]; linarith⟩
  have h₁₃₂ : IsPathConnected (U₁ ∪ U₃ ∪ U₂) := h₁₃.union h₂
    ⟨((q.re + 1 : ℝ) : ℂ) + ((q.im + 1 : ℝ) : ℂ) * I, by simp [U₁, U₂, U₃]; linarith⟩
  have hall : IsPathConnected (U₁ ∪ U₃ ∪ U₂ ∪ U₄) := h₁₃₂.union h₄
    ⟨((q.re - 1 : ℝ) : ℂ) + ((q.im / 2 : ℝ) : ℂ) * I, by simp [U₁, U₂, U₃, U₄, hq]⟩
  convert hall using 1
  ext z
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq, U₁, U₂, U₃, U₄]
  constructor
  · rintro ⟨hz, hzq⟩
    have hz' : (0 : ℝ) < z.im := hz
    rcases lt_trichotomy z.re q.re with h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hz', h⟩))
    · rcases lt_trichotomy z.im q.im with h' | h' | h'
      · exact Or.inr ⟨hz', h'⟩
      · exact absurd (Complex.ext h h') hzq
      · exact Or.inl (Or.inl (Or.inr h'))
    · exact Or.inl (Or.inr ⟨hz', h⟩)
  · rintro (((⟨h1, h2⟩ | h3) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨h1, fun he => by rw [he] at h2; exact lt_irrefl _ h2⟩
    · exact ⟨show (0 : ℝ) < z.im by linarith, fun he => by rw [he] at h3; exact lt_irrefl _ h3⟩
    · exact ⟨h1, fun he => by rw [he] at h2; exact lt_irrefl _ h2⟩
    · exact ⟨h1, fun he => by rw [he] at h2; exact lt_irrefl _ h2⟩

/-- A continuous path on `[0, 1]` in `ℍ` from `a` to `b` avoiding the point `q`. -/
theorem exists_path_H_avoid {a b q : ℂ} (ha : a ∈ H) (hb : b ∈ H) (haq : a ≠ q) (hbq : b ≠ q) :
    ∃ P : ℝ → ℂ, Continuous P ∧ P 0 = a ∧ P 1 = b ∧ MapsTo P (Icc 0 1) (H \ {q}) := by
  obtain ⟨γ, hγ⟩ := (isPathConnected_H_diff q).joinedIn a ⟨ha, haq⟩ b ⟨hb, hbq⟩
  refine ⟨γ.extend, γ.continuous_extend, γ.extend_zero, γ.extend_one, fun t ht => ?_⟩
  rw [γ.extend_apply ht]
  exact hγ ⟨t, ht⟩

/-! ### Constancy along a compact path -/

/-- **A locally constant integer function along a path.** Let `σ` be continuous on `[0, 1]`. If near every point
of `σ` the function `g` is constant on the good set `B`, and `B` accumulates at every point of `σ`, then `g` takes
the same value at the two (good) ends of `σ`. -/
theorem eq_of_locally_const_along {σ : ℝ → ℂ} (hσ : ContinuousOn σ (Icc 0 1)) {g : ℂ → ℤ} {B : Set ℂ}
    (hloc : ∀ t ∈ Icc (0 : ℝ) 1, ∃ v : ℤ, ∀ᶠ z in 𝓝 (σ t), z ∈ B → g z = v)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 1, ∃ᶠ z in 𝓝 (σ t), z ∈ B)
    (h0 : σ 0 ∈ B) (h1 : σ 1 ∈ B) : g (σ 0) = g (σ 1) := by
  classical
  let V : ℝ → ℤ := fun t =>
    if h : ∃ v : ℤ, ∀ᶠ z in 𝓝 (σ t), z ∈ B → g z = v then h.choose else 0
  have hV : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ z in 𝓝 (σ t), z ∈ B → g z = V t := by
    intro t ht
    have h := hloc t ht
    simp only [V, h, ↓reduceDIte]
    exact h.choose_spec
  have hloc' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ t' in 𝓝[Icc 0 1] t, V t' = V t := by
    intro t ht
    obtain ⟨O, hOU, hO, htO⟩ := _root_.mem_nhds_iff.1 (hV t ht)
    have hev : ∀ᶠ t' in 𝓝[Icc 0 1] t, σ t' ∈ O := (hσ t ht).tendsto (hO.mem_nhds htO)
    filter_upwards [hev, self_mem_nhdsWithin] with t' ht'O ht'
    obtain ⟨z, hzB, hzO, hzV⟩ := ((hdense t' ht').and_eventually
      ((show ∀ᶠ z in 𝓝 (σ t'), z ∈ O from hO.mem_nhds ht'O).and (hV t' ht'))).exists
    exact (hzV hzB).symm.trans (hOU hzO hzB)
  have hcont : ContinuousOn V (Icc 0 1) := by
    intro t ht
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    exact hloc' t ht
  have hV01 : V 0 = V 1 := isPreconnected_Icc.constant hcont (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  rw [(hV 0 (left_mem_Icc.2 zero_le_one)).self_of_nhds h0,
    (hV 1 (right_mem_Icc.2 zero_le_one)).self_of_nhds h1, hV01]

end InteractingSLE.Sec5.Prop51HGate
