/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Topology.Jordan.Crossing
import InteractingSLE.WangWu.ChamberJordan

/-!
# Crossing paths in a Jordan domain

Packet PROVE-WW-B4. The topological core of the contact-order argument for ordered curves (specification Aux. lemma 93,
`source/spec/p289-336.md#aux-93`, used in the proof of Lemma 7.1 and, for the Wang–Wu chambers, in the proof of
Lemma 4.22 of `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31): "a later contact strictly behind it
would put the path in a component cut off from its terminal boundary point by an earlier prefix". It is the following
crossing statement: **in the closure of a Jordan domain, a path joining two boundary points `a, b` meets every path
joining two boundary points `c, d` that are separated by `a, b` on the curve.**

* `disc_crossing`: the case of the closed unit disc with `a = −1`, `b = 1`, `c` on the open lower and `d` on the open
  upper semicircle. It is Maehara's crossing lemma (`Foundations.Jordan.crossing`, from Brouwer's fixed point
  theorem) in the square `[−1, 1]²`, after extending the second path vertically from `c` down to the bottom edge and
  from `d` up to the top edge (these segments leave the closed disc at once).
* `discMob a b`: the Möbius automorphism of the closed disc `w ↦ ((k + 2i)w − kb)/(kw + (2i − k)b)`,
  `k = i(b + a)/(b − a)` (real), with `a ↦ −1`, `b ↦ 1`; the identity
  `|num|² − |den|² = 4(|w|² − 1)` (`normSq_mobNum_sub_normSq_mobDen`) gives the disc and circle invariance.
* `disc_crossing_of_sep`: the closed disc with arbitrary boundary points; "separated" is: every preconnected subset
  of the circle containing `c` and `d` contains `a` or `b`.
* `jordan_crossing`: the closure of the inside of any Jordan curve, through the Schoenflies homeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open InteractingSLE.Foundations.Jordan (Plane crossing)

namespace InteractingSLE.WangWu

/-! ### The plane coordinates of a complex number -/

/-- The point `(Re z, Im z)` of `ℝ²`. -/
def toPlane (z : ℂ) : Plane := WithLp.toLp 2 ![z.re, z.im]

@[simp] theorem toPlane_zero (z : ℂ) : (toPlane z).ofLp 0 = z.re := rfl

@[simp] theorem toPlane_one (z : ℂ) : (toPlane z).ofLp 1 = z.im := rfl

theorem continuous_toPlane : Continuous toPlane := by
  unfold toPlane
  fun_prop

theorem toPlane_injective : Function.Injective toPlane := by
  intro z w h
  apply Complex.ext
  · have := congrArg (fun p : Plane => p.ofLp 0) h; simpa using this
  · have := congrArg (fun p : Plane => p.ofLp 1) h; simpa using this

theorem re_mem_Icc_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : z.re ∈ Icc (-1 : ℝ) 1 :=
  abs_le.1 ((abs_re_le_norm z).trans hz)

theorem im_mem_Icc_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : z.im ∈ Icc (-1 : ℝ) 1 :=
  abs_le.1 ((abs_im_le_norm z).trans hz)

/-- Moving a point of the unit circle vertically away from the real axis leaves the closed disc. -/
theorem one_lt_norm_add_mul_I {q : ℂ} (hq : ‖q‖ = 1) {c : ℝ} (hc : 0 < q.im * c) :
    1 < ‖q + (c : ℂ) * I‖ := by
  have h1 : q.re * q.re + q.im * q.im = 1 := by
    have := Complex.sq_norm q
    rw [hq, Complex.normSq_apply] at this
    linarith
  have h2 : ‖q + (c : ℂ) * I‖ ^ 2 = q.re * q.re + (q.im + c) * (q.im + c) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
  have h3 : 1 < ‖q + (c : ℂ) * I‖ ^ 2 := by
    rw [h2]; nlinarith [mul_pos hc hc, sq_nonneg c]
  nlinarith [norm_nonneg (q + (c : ℂ) * I)]

/-! ### The crossing lemma in the closed unit disc -/

/-- **Crossing in the closed disc.** A path in the closed unit disc from `−1` to `1` meets every path in the closed
disc from a point of the open lower semicircle to a point of the open upper semicircle. -/
theorem disc_crossing {P Q : ℝ → ℂ} (hP : ContinuousOn P (Icc 0 1)) (hQ : ContinuousOn Q (Icc 0 1))
    (hPD : MapsTo P (Icc 0 1) (closedBall 0 1)) (hQD : MapsTo Q (Icc 0 1) (closedBall 0 1))
    (hP0 : P 0 = -1) (hP1 : P 1 = 1) (hQ0 : ‖Q 0‖ = 1) (hQ0i : (Q 0).im < 0) (hQ1 : ‖Q 1‖ = 1)
    (hQ1i : 0 < (Q 1).im) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P s = Q t := by
  set q0 := (Q 0).im
  set q1 := (Q 1).im
  have hq0 : -1 ≤ q0 := (im_mem_Icc_of_norm_le hQ0.le).1
  have hq1 : q1 ≤ 1 := (im_mem_Icc_of_norm_le hQ1.le).2
  set u : ℝ → ℝ := fun t => max 0 (min 1 (t + 1 / 2)) with hu
  set d : ℝ → ℝ := fun t => 2 * (1 + q0) * max 0 (-1 / 2 - t) with hd
  set e : ℝ → ℝ := fun t => 2 * (1 - q1) * max 0 (t - 1 / 2) with he
  set h : ℝ → Plane := fun t => toPlane (P ((t + 1) / 2)) with hh
  set v : ℝ → Plane := fun t => toPlane (Q (u t) + ((e t - d t : ℝ) : ℂ) * I) with hv
  have hu01 : ∀ t, u t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hs01 : ∀ t ∈ Icc (-1 : ℝ) 1, (t + 1) / 2 ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have huc : Continuous u := by rw [hu]; fun_prop
  have hhc : ContinuousOn h (Icc (-1) 1) :=
    continuous_toPlane.comp_continuousOn (hP.comp (by fun_prop) hs01)
  have hvc : ContinuousOn v (Icc (-1) 1) := by
    have hQu : Continuous fun t => Q (u t) := hQ.comp_continuous huc hu01
    have : Continuous v := continuous_toPlane.comp (hQu.add (by rw [hd, he]; fun_prop))
    exact this.continuousOn
  -- the three regimes of `v`
  have hlow : ∀ t, t ≤ -1 / 2 → u t = 0 ∧ e t = 0 := fun t ht => by
    refine ⟨?_, ?_⟩
    · simp only [hu]; rw [max_eq_left]; exact (min_le_right _ _).trans (by linarith)
    · simp only [he]; rw [max_eq_left (by linarith)]; ring
  have hhigh : ∀ t, 1 / 2 ≤ t → u t = 1 ∧ d t = 0 := fun t ht => by
    refine ⟨?_, ?_⟩
    · simp only [hu]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    · simp only [hd]; rw [max_eq_left (by linarith)]; ring
  have hmid : ∀ t, -1 / 2 ≤ t → t ≤ 1 / 2 → d t = 0 ∧ e t = 0 := fun t h1 h2 => by
    refine ⟨?_, ?_⟩
    · simp only [hd]; rw [max_eq_left (by linarith)]; ring
    · simp only [he]; rw [max_eq_left (by linarith)]; ring
  have hd0 : ∀ t, 0 ≤ d t := fun t => mul_nonneg (by linarith) (le_max_left _ _)
  have he0 : ∀ t, 0 ≤ e t := fun t => mul_nonneg (by linarith) (le_max_left _ _)
  obtain ⟨s, hs, t, ht, hst⟩ := crossing Foundations.Jordan.Brouwer.brouwerFPT (a := -1) (b := 1)
    (c := -1) (d := 1) (by norm_num) (by norm_num) h v hhc hvc
    (fun t ht => by
      have := hPD (hs01 t ht)
      rw [mem_closedBall, dist_zero_right] at this
      exact ⟨re_mem_Icc_of_norm_le this, im_mem_Icc_of_norm_le this⟩)
    (fun t ht => by
      have hQt := hQD (hu01 t)
      rw [mem_closedBall, dist_zero_right] at hQt
      simp only [hv, toPlane_zero, toPlane_one, add_re, add_im, mul_re, mul_im, ofReal_re,
        ofReal_im, I_re, I_im, mul_zero, sub_zero, mul_one, add_zero]
      refine ⟨re_mem_Icc_of_norm_le hQt, ?_⟩
      rcases le_or_gt t (-1 / 2) with h1 | h1
      · obtain ⟨hu0, he0'⟩ := hlow t h1
        rw [hu0, he0']
        have hdt : d t ≤ 1 + q0 := by
          simp only [hd]
          have : max 0 (-1 / 2 - t) ≤ 1 / 2 := max_le (by norm_num) (by linarith [ht.1])
          nlinarith
        constructor <;> linarith [hd0 t]
      rcases le_or_gt t (1 / 2) with h2 | h2
      · obtain ⟨hd0', he0'⟩ := hmid t h1.le h2
        rw [hd0', he0', sub_zero, add_zero]
        exact im_mem_Icc_of_norm_le hQt
      · obtain ⟨hu1, hd0'⟩ := hhigh t h2.le
        rw [hu1, hd0']
        have het : e t ≤ 1 - q1 := by
          simp only [he]
          have : max 0 (t - 1 / 2) ≤ 1 / 2 := max_le (by norm_num) (by linarith [ht.2])
          nlinarith
        constructor <;> linarith [he0 t, hQ1i])
    (by simp [hh, hP0]) (by simp [hh, hP1])
    (by
      obtain ⟨hu0, he0'⟩ := hlow (-1) (by norm_num)
      simp only [hv, toPlane_one, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
        mul_one, hu0, he0']
      simp only [hd]; norm_num; ring)
    (by
      obtain ⟨hu1, hd0'⟩ := hhigh 1 (by norm_num)
      simp only [hv, toPlane_one, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
        mul_one, hu1, hd0']
      simp only [he]; norm_num; ring)
  -- read the meeting point back in `ℂ`
  have hPQ := toPlane_injective hst
  have hPs := hPD (hs01 s hs)
  rw [mem_closedBall, dist_zero_right] at hPs
  refine ⟨(s + 1) / 2, hs01 s hs, u t, hu01 t, ?_⟩
  rw [hPQ]
  rcases le_or_gt t (-1 / 2) with h1 | h1
  · obtain ⟨hu0, he0'⟩ := hlow t h1
    rcases (hd0 t).eq_or_lt with hdz | hdz
    · rw [he0', ← hdz, sub_zero, ofReal_zero, zero_mul, add_zero]
    · exfalso
      rw [hPQ, hu0, he0'] at hPs
      have := one_lt_norm_add_mul_I hQ0 (c := 0 - d t) (by nlinarith)
      linarith
  rcases le_or_gt t (1 / 2) with h2 | h2
  · obtain ⟨hd0', he0'⟩ := hmid t h1.le h2
    rw [hd0', he0', sub_zero, ofReal_zero, zero_mul, add_zero]
  · obtain ⟨hu1, hd0'⟩ := hhigh t h2.le
    rcases (he0 t).eq_or_lt with hez | hez
    · rw [hd0', ← hez, sub_zero, ofReal_zero, zero_mul, add_zero]
    · exfalso
      rw [hPQ, hu1, hd0'] at hPs
      have := one_lt_norm_add_mul_I hQ1 (c := e t - 0) (by nlinarith)
      linarith

/-! ### A Möbius automorphism of the disc sending two boundary points to `∓1` -/

/-- `k = Re (i (b + a)/(b − a))`; for `a, b` on the unit circle `i (b + a)/(b − a)` is real (`ofReal_mobK`). -/
def mobK (a b : ℂ) : ℝ := (I * (b + a) / (b - a)).re

theorem ofReal_mobK {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    ((mobK a b : ℝ) : ℂ) = I * (b + a) / (b - a) := by
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have hca : (starRingEnd ℂ) a = a⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ha]; simp
  have hcb : (starRingEnd ℂ) b = b⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]; simp
  have hreal : (starRingEnd ℂ) (I * (b + a) / (b - a)) = I * (b + a) / (b - a) := by
    rw [map_div₀, map_mul, map_add, map_sub, Complex.conj_I, hca, hcb]
    field_simp
    ring
  exact Complex.conj_eq_iff_re.1 hreal

/-- The numerator of `discMob a b`. -/
def mobNum (k : ℝ) (b w : ℂ) : ℂ := ((k : ℂ) + 2 * I) * w - (k : ℂ) * b

/-- The denominator of `discMob a b`. -/
def mobDen (k : ℝ) (b w : ℂ) : ℂ := (k : ℂ) * w + (2 * I - (k : ℂ)) * b

/-- The disc automorphism `w ↦ ((k + 2i)w − kb)/(kw + (2i − k)b)`, `k = mobK a b`. -/
def discMob (a b w : ℂ) : ℂ := mobNum (mobK a b) b w / mobDen (mobK a b) b w

/-- The inverse map `z ↦ ((2i − k)bz + kb)/(−kz + (k + 2i))`. -/
def discMobInv (a b z : ℂ) : ℂ :=
  ((2 * I - (mobK a b : ℂ)) * b * z + (mobK a b : ℂ) * b) / (-(mobK a b : ℂ) * z + ((mobK a b : ℂ) + 2 * I))

theorem normSq_mobNum_sub_normSq_mobDen (k : ℝ) {b : ℂ} (hb : ‖b‖ = 1) (w : ℂ) :
    normSq (mobNum k b w) - normSq (mobDen k b w) = 4 * (normSq w - 1) := by
  have hb2 : b.re * b.re + b.im * b.im = 1 := by
    have := Complex.sq_norm b
    rw [hb, Complex.normSq_apply] at this
    linarith
  simp only [mobNum, mobDen, normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
  linear_combination (-4 : ℝ) * hb2

theorem normSq_invNum_sub_normSq_invDen (k : ℝ) {b : ℂ} (hb : ‖b‖ = 1) (z : ℂ) :
    normSq ((2 * I - (k : ℂ)) * b * z + (k : ℂ) * b) - normSq (-(k : ℂ) * z + ((k : ℂ) + 2 * I)) =
      4 * (normSq z - 1) := by
  have hb2 : b.re * b.re + b.im * b.im = 1 := by
    have := Complex.sq_norm b
    rw [hb, Complex.normSq_apply] at this
    linarith
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re,
    I_im, re_ofNat, im_ofNat, neg_re, neg_im]
  linear_combination ((2 * z.re - k * z.im) * (2 * z.re - k * z.im) +
    (k - k * z.re - 2 * z.im) * (k - k * z.re - 2 * z.im)) * hb2

theorem mobDen_ne_zero (k : ℝ) {b : ℂ} (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ ≤ 1) : mobDen k b w ≠ 0 := by
  intro h0
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hid := normSq_mobNum_sub_normSq_mobDen k hb w
  rw [h0, map_zero, sub_zero] at hid
  have hw2 : normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hn0 : mobNum k b w = 0 := by
    have := normSq_nonneg (mobNum k b w)
    exact normSq_eq_zero.1 (le_antisymm (by linarith) this)
  have hwb : w = b := by
    have : (2 * I) * (b - w) = 0 := by
      simp only [mobNum, mobDen] at h0 hn0
      linear_combination h0 - hn0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero I_ne_zero)
    · exact (sub_eq_zero.1 h).symm
  subst hwb
  have : mobDen k w w = 2 * I * w := by simp only [mobDen]; ring
  rw [this] at h0
  exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hb0 h0

theorem invDen_ne_zero (k : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) : -(k : ℂ) * z + ((k : ℂ) + 2 * I) ≠ 0 := by
  intro h0
  have h1 : (k : ℂ) * z = (k : ℂ) + 2 * I := by linear_combination -h0
  have h2 := congrArg normSq h1
  rw [map_mul, normSq_ofReal] at h2
  have h3 : normSq ((k : ℂ) + 2 * I) = k * k + 4 := by
    simp [normSq_apply]; ring
  rw [h3] at h2
  have hz2 : normSq z ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  nlinarith [mul_self_nonneg k]

variable {a b : ℂ}

theorem discMob_left (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) : discMob a b a = -1 := by
  have hk := ofReal_mobK ha hb hab
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hkab : (mobK a b : ℂ) * (b - a) = I * (b + a) := by rw [hk]; field_simp
  have hnum : mobNum (mobK a b) b a = I * (a - b) := by
    simp only [mobNum]; linear_combination -hkab
  have hden : mobDen (mobK a b) b a = I * (b - a) := by
    simp only [mobDen]; linear_combination -hkab
  rw [discMob, hnum, hden, div_eq_iff (mul_ne_zero I_ne_zero hba)]
  ring

theorem discMob_right (hb : ‖b‖ = 1) : discMob a b b = 1 := by
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hnum : mobNum (mobK a b) b b = 2 * I * b := by simp only [mobNum]; ring
  have hden : mobDen (mobK a b) b b = 2 * I * b := by simp only [mobDen]; ring
  rw [discMob, hnum, hden, div_self (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hb0)]

theorem normSq_discMob (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    normSq (discMob a b w) = 1 + 4 * (normSq w - 1) / normSq (mobDen (mobK a b) b w) := by
  have hd := mobDen_ne_zero (mobK a b) hb hw
  have hdpos : 0 < normSq (mobDen (mobK a b) b w) := normSq_pos.2 hd
  rw [discMob, map_div₀, ← normSq_mobNum_sub_normSq_mobDen (mobK a b) hb w]
  field_simp
  ring

theorem norm_discMob_le (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖discMob a b w‖ ≤ 1 := by
  have hdpos : 0 < normSq (mobDen (mobK a b) b w) := normSq_pos.2 (mobDen_ne_zero _ hb hw)
  have hw2 : normSq w ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have h := normSq_discMob (a := a) hb hw
  have : normSq (discMob a b w) ≤ 1 := by
    rw [h]
    have : 4 * (normSq w - 1) / normSq (mobDen (mobK a b) b w) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hdpos.le
    linarith
  rw [Complex.normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (discMob a b w)]

theorem norm_discMob_eq_one (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ = 1) : ‖discMob a b w‖ = 1 := by
  have h := normSq_discMob (a := a) hb hw.le
  have hw2 : normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [hw2, sub_self, mul_zero, zero_div, add_zero, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (discMob a b w)]

theorem continuousOn_discMob (hb : ‖b‖ = 1) : ContinuousOn (discMob a b) (closedBall 0 1) := by
  intro w hw
  rw [mem_closedBall, dist_zero_right] at hw
  have hd := mobDen_ne_zero (mobK a b) hb hw
  refine ContinuousAt.continuousWithinAt ?_
  unfold discMob mobNum mobDen
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hd

theorem discMob_injOn (hb : ‖b‖ = 1) : InjOn (discMob a b) (closedBall 0 1) := by
  intro w hw w' hw' heq
  rw [mem_closedBall, dist_zero_right] at hw hw'
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hd := mobDen_ne_zero (mobK a b) hb hw
  have hd' := mobDen_ne_zero (mobK a b) hb hw'
  rw [discMob, discMob, div_eq_div_iff hd hd'] at heq
  have : (-4 * b) * (w - w') = 0 := by
    simp only [mobNum, mobDen] at heq
    linear_combination heq + (-4 * b * (w - w')) * I_sq
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (mul_ne_zero (by norm_num) hb0)
  · exact sub_eq_zero.1 h

theorem discMobInv_discMob (hb : ‖b‖ = 1) {w : ℂ} (hw : ‖w‖ ≤ 1) : discMobInv a b (discMob a b w) = w := by
  have hd := mobDen_ne_zero (mobK a b) hb hw
  have hv : discMob a b w * mobDen (mobK a b) b w = mobNum (mobK a b) b w := by
    rw [discMob, div_mul_cancel₀ _ hd]
  have hvn : ‖discMob a b w‖ ≤ 1 := norm_discMob_le hb hw
  rw [discMobInv, div_eq_iff (invDen_ne_zero _ hvn)]
  simp only [mobNum, mobDen] at hv
  linear_combination hv

theorem discMob_discMobInv (hb : ‖b‖ = 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : discMob a b (discMobInv a b z) = z := by
  have hd := invDen_ne_zero (mobK a b) hz
  set u := discMobInv a b z with hu
  have hu' : u * (-(mobK a b : ℂ) * z + ((mobK a b : ℂ) + 2 * I)) =
      (2 * I - (mobK a b : ℂ)) * b * z + (mobK a b : ℂ) * b := by
    rw [hu, discMobInv, div_mul_cancel₀ _ hd]
  -- `u` lies in the closed disc
  have hun : ‖u‖ ≤ 1 := by
    have hid := normSq_invNum_sub_normSq_invDen (mobK a b) hb z
    have hdpos : 0 < normSq (-(mobK a b : ℂ) * z + ((mobK a b : ℂ) + 2 * I)) := normSq_pos.2 hd
    have hz2 : normSq z ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
    have hu2 : normSq u ≤ 1 := by
      rw [hu, discMobInv, map_div₀, div_le_one hdpos]
      linarith
    rw [Complex.normSq_eq_norm_sq] at hu2
    nlinarith [norm_nonneg u]
  rw [discMob, div_eq_iff (mobDen_ne_zero _ hb hun)]
  simp only [mobNum, mobDen]
  linear_combination hu'

theorem norm_discMobInv_eq_one (hb : ‖b‖ = 1) {z : ℂ} (hz : ‖z‖ = 1) : ‖discMobInv a b z‖ = 1 := by
  have hd := invDen_ne_zero (mobK a b) hz.le
  have hid := normSq_invNum_sub_normSq_invDen (mobK a b) hb z
  have hz2 : normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [hz2, sub_self, mul_zero, sub_eq_zero] at hid
  have h : normSq (discMobInv a b z) = 1 := by
    rw [discMobInv, map_div₀, hid, div_self (normSq_pos.2 hd).ne']
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (discMobInv a b z)]

theorem continuousOn_discMobInv : ContinuousOn (discMobInv a b) (closedBall 0 1) := by
  intro z hz
  rw [mem_closedBall, dist_zero_right] at hz
  refine ContinuousAt.continuousWithinAt ?_
  unfold discMobInv
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (invDen_ne_zero _ hz)

/-! ### Crossing in the closed disc with arbitrary boundary points -/

/-- The open upper semicircle is the image of `(0, π)`. -/
theorem mem_image_exp_Ioo_of_im_pos {z : ℂ} (hz : ‖z‖ = 1) (him : 0 < z.im) :
    z ∈ (fun θ : ℝ => exp ((θ : ℂ) * I)) '' Ioo 0 Real.pi := by
  refine ⟨arg z, ⟨?_, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne (arg_nonneg_iff.2 him.le) fun h => ?_
    exact him.ne' (arg_eq_zero_iff.1 h.symm).2
  · exact arg_lt_pi_iff.2 (Or.inr him.ne')
  · simpa [hz] using norm_mul_exp_arg_mul_I z

/-- The open lower semicircle is the image of `(−π, 0)`. -/
theorem mem_image_exp_Ioo_of_im_neg {z : ℂ} (hz : ‖z‖ = 1) (him : z.im < 0) :
    z ∈ (fun θ : ℝ => exp ((θ : ℂ) * I)) '' Ioo (-Real.pi) 0 := by
  refine ⟨arg z, ⟨neg_pi_lt_arg z, arg_neg_iff.2 him⟩, ?_⟩
  simpa [hz] using norm_mul_exp_arg_mul_I z

theorem im_exp_mul_I_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) : 0 < (exp ((θ : ℂ) * I)).im := by
  rw [exp_ofReal_mul_I_im]; exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

theorem im_exp_mul_I_neg {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) 0) : (exp ((θ : ℂ) * I)).im < 0 := by
  rw [exp_ofReal_mul_I_im]; exact Real.sin_neg_of_neg_of_neg_pi_lt hθ.2 hθ.1

/-- Points of the unit circle off `±1` have nonzero imaginary part. -/
theorem im_ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (h2 : z ≠ -1) : z.im ≠ 0 := by
  intro him
  have hre : z.re * z.re = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply, him, mul_zero, add_zero] at this
    linarith
  rcases mul_self_eq_one_iff.1 hre with h | h
  · exact h1 (Complex.ext (by simp [h]) (by simp [him]))
  · exact h2 (Complex.ext (by simp [h]) (by simp [him]))

/-- The image of an open semicircle under `discMobInv` is a preconnected subset of the circle avoiding `a, b`. -/
theorem discMobInv_semicircle (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) {J : Set ℝ} (hJ : IsPreconnected J)
    (hJs : ∀ θ ∈ J, (exp ((θ : ℂ) * I)).im ≠ 0) :
    IsPreconnected (discMobInv a b '' ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' J)) ∧
      discMobInv a b '' ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' J) ⊆ sphere 0 1 ∧
      a ∉ discMobInv a b '' ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' J) ∧
      b ∉ discMobInv a b '' ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' J) := by
  have hsph : ∀ θ : ℝ, ‖exp ((θ : ℂ) * I)‖ = 1 := fun θ => norm_exp_ofReal_mul_I θ
  refine ⟨(hJ.image _ (by fun_prop : Continuous fun θ : ℝ => exp ((θ : ℂ) * I)).continuousOn).image _
    (continuousOn_discMobInv.mono ?_), ?_, ?_, ?_⟩
  · rintro _ ⟨θ, -, rfl⟩
    rw [mem_closedBall, dist_zero_right, hsph]
  · rintro _ ⟨_, ⟨θ, -, rfl⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact norm_discMobInv_eq_one hb (hsph θ)
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, h⟩
    have := discMob_discMobInv (a := a) hb (hsph θ).le
    rw [h, discMob_left ha hb hab] at this
    exact hJs θ hθ (by rw [← this]; simp)
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, h⟩
    have := discMob_discMobInv (a := a) hb (hsph θ).le
    rw [h, discMob_right hb] at this
    exact hJs θ hθ (by rw [← this]; simp)

/-- **Crossing in the closed disc.** Let `a ≠ b` lie on the unit circle and let `c, d` be points of the circle
separated by `{a, b}` (every preconnected subset of the circle containing `c` and `d` contains `a` or `b`). Then
every path in the closed disc from `a` to `b` meets every path in the closed disc from `c` to `d`. -/
theorem disc_crossing_of_sep {c d : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) (hc : ‖c‖ = 1)
    (hd : ‖d‖ = 1) (hsep : ∀ K ⊆ sphere (0 : ℂ) 1, IsPreconnected K → c ∈ K → d ∈ K → a ∈ K ∨ b ∈ K)
    {P Q : ℝ → ℂ} (hP : ContinuousOn P (Icc 0 1)) (hQ : ContinuousOn Q (Icc 0 1))
    (hPD : MapsTo P (Icc 0 1) (closedBall 0 1)) (hQD : MapsTo Q (Icc 0 1) (closedBall 0 1))
    (hP0 : P 0 = a) (hP1 : P 1 = b) (hQ0 : Q 0 = c) (hQ1 : Q 1 = d) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P s = Q t := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- trivial meetings at the endpoints
  by_cases hca : c = a
  · exact ⟨0, h0, 0, h0, by rw [hP0, hQ0, hca]⟩
  by_cases hcb : c = b
  · exact ⟨1, h1, 0, h0, by rw [hP1, hQ0, hcb]⟩
  by_cases hda : d = a
  · exact ⟨0, h0, 1, h1, by rw [hP0, hQ1, hda]⟩
  by_cases hdb : d = b
  · exact ⟨1, h1, 1, h1, by rw [hP1, hQ1, hdb]⟩
  set M := discMob a b with hMdef
  have hMc : ContinuousOn M (closedBall 0 1) := continuousOn_discMob hb
  have hMi : InjOn M (closedBall 0 1) := discMob_injOn hb
  have hMD : MapsTo M (closedBall 0 1) (closedBall 0 1) := fun w hw => by
    rw [mem_closedBall, dist_zero_right] at hw ⊢; exact norm_discMob_le hb hw
  have hcD : c ∈ closedBall (0 : ℂ) 1 := by rw [mem_closedBall, dist_zero_right, hc]
  have hdD : d ∈ closedBall (0 : ℂ) 1 := by rw [mem_closedBall, dist_zero_right, hd]
  have haD : a ∈ closedBall (0 : ℂ) 1 := by rw [mem_closedBall, dist_zero_right, ha]
  have hbD : b ∈ closedBall (0 : ℂ) 1 := by rw [mem_closedBall, dist_zero_right, hb]
  have hMa : M a = -1 := discMob_left ha hb hab
  have hMb : M b = 1 := discMob_right hb
  -- `M c` and `M d` lie on the circle, off `±1`
  have hMcn : ‖M c‖ = 1 := norm_discMob_eq_one hb hc
  have hMdn : ‖M d‖ = 1 := norm_discMob_eq_one hb hd
  have hMcim : (M c).im ≠ 0 := im_ne_zero_of_norm_eq_one hMcn
    (fun h => hcb (hMi hcD hbD (h.trans hMb.symm))) (fun h => hca (hMi hcD haD (h.trans hMa.symm)))
  have hMdim : (M d).im ≠ 0 := im_ne_zero_of_norm_eq_one hMdn
    (fun h => hdb (hMi hdD hbD (h.trans hMb.symm))) (fun h => hda (hMi hdD haD (h.trans hMa.symm)))
  -- they lie on opposite semicircles
  have hinv : ∀ w ∈ closedBall (0 : ℂ) 1, discMobInv a b (M w) = w := fun w hw => by
    rw [mem_closedBall, dist_zero_right] at hw; exact discMobInv_discMob hb hw
  have hsame : ∀ J : Set ℝ, IsPreconnected J → (∀ θ ∈ J, (exp ((θ : ℂ) * I)).im ≠ 0) →
      M c ∈ (fun θ : ℝ => exp ((θ : ℂ) * I)) '' J → M d ∈ (fun θ : ℝ => exp ((θ : ℂ) * I)) '' J → False := by
    intro J hJ hJs hcJ hdJ
    obtain ⟨hK, hKs, haK, hbK⟩ := discMobInv_semicircle ha hb hab hJ hJs
    rcases hsep _ hKs hK ⟨_, hcJ, hinv c hcD⟩ ⟨_, hdJ, hinv d hdD⟩ with h | h
    · exact haK h
    · exact hbK h
  have hPM : ContinuousOn (fun s => M (P s)) (Icc 0 1) := hMc.comp hP hPD
  have hQM : ContinuousOn (fun s => M (Q s)) (Icc 0 1) := hMc.comp hQ hQD
  have hback : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, M (P s) = M (Q t) → P s = Q t :=
    fun s hs t ht h => hMi (hPD hs) (hQD ht) h
  rcases lt_or_gt_of_ne hMcim with hcneg | hcpos
  · rcases lt_or_gt_of_ne hMdim with hdneg | hdpos
    · exact (hsame _ (convex_Ioo _ _).isPreconnected (fun θ hθ => (im_exp_mul_I_neg hθ).ne)
        (mem_image_exp_Ioo_of_im_neg hMcn hcneg) (mem_image_exp_Ioo_of_im_neg hMdn hdneg)).elim
    · obtain ⟨s, hs, t, ht, hst⟩ := disc_crossing hPM hQM (hMD.comp hPD) (hMD.comp hQD)
        (by simp only [hP0, hMa]) (by simp only [hP1, hMb]) (by simp only [hQ0, hMcn])
        (by simpa only [hQ0] using hcneg) (by simp only [hQ1, hMdn]) (by simpa only [hQ1] using hdpos)
      exact ⟨s, hs, t, ht, hback s hs t ht hst⟩
  · rcases lt_or_gt_of_ne hMdim with hdneg | hdpos
    · -- reverse the second path
      have hrev : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := fun t ht =>
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      obtain ⟨s, hs, t, ht, hst⟩ := disc_crossing hPM (hQM.comp (by fun_prop) hrev)
        (hMD.comp hPD) ((hMD.comp hQD).comp hrev)
        (by simp only [hP0, hMa]) (by simp only [hP1, hMb])
        (by simp only [Function.comp_apply, sub_zero, hQ1, hMdn])
        (by simpa only [Function.comp_apply, sub_zero, hQ1] using hdneg)
        (by simp only [Function.comp_apply, sub_self, hQ0, hMcn])
        (by simpa only [Function.comp_apply, sub_self, hQ0] using hcpos)
      exact ⟨s, hs, 1 - t, hrev ht, hback s hs _ (hrev ht) hst⟩
    · exact (hsame _ (convex_Ioo _ _).isPreconnected (fun θ hθ => (im_exp_mul_I_pos hθ).ne')
        (mem_image_exp_Ioo_of_im_pos hMcn hcpos) (mem_image_exp_Ioo_of_im_pos hMdn hdpos)).elim

/-! ### Crossing in a Jordan domain -/

/-- **Crossing in the closure of a Jordan domain.** Let `Γ` be a Jordan curve, `a ≠ b` points of `Γ`, and `c, d` points
of `Γ` separated by `{a, b}` on `Γ` (every preconnected subset of `Γ` containing `c` and `d` contains `a` or `b`).
Then every path in `jordanIn Γ ∪ Γ` from `a` to `b` meets every path in `jordanIn Γ ∪ Γ` from `c` to `d`. -/
theorem jordan_crossing {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {c d : ℂ} (ha : a ∈ Γ)
    (hb : b ∈ Γ) (hab : a ≠ b) (hc : c ∈ Γ) (hd : d ∈ Γ)
    (hsep : ∀ K ⊆ Γ, IsPreconnected K → c ∈ K → d ∈ K → a ∈ K ∨ b ∈ K)
    {P Q : ℝ → ℂ} (hP : ContinuousOn P (Icc 0 1)) (hQ : ContinuousOn Q (Icc 0 1))
    (hPD : MapsTo P (Icc 0 1) (jordanIn Γ ∪ Γ)) (hQD : MapsTo Q (Icc 0 1) (jordanIn Γ ∪ Γ))
    (hP0 : P 0 = a) (hP1 : P 1 = b) (hQ0 : Q 0 = c) (hQ1 : Q 1 = d) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, P s = Q t := by
  obtain ⟨h, hs, hbl⟩ := exists_homeomorph_jordanIn hΓ
  have hcl : h '' closedBall 0 1 = jordanIn Γ ∪ Γ := by
    rw [← ball_union_sphere, image_union, hbl, hs]
  have hsymm : ∀ z ∈ jordanIn Γ ∪ Γ, h.symm z ∈ closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [← hcl] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [h.symm_apply_apply]
  have hsph : ∀ z ∈ Γ, ‖h.symm z‖ = 1 := by
    intro z hz
    rw [← hs] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [h.symm_apply_apply, ← mem_sphere_zero_iff_norm]
    exact hw
  have hsep' : ∀ K ⊆ sphere (0 : ℂ) 1, IsPreconnected K → h.symm c ∈ K → h.symm d ∈ K →
      h.symm a ∈ K ∨ h.symm b ∈ K := by
    intro K hK hKc hcK hdK
    have hK' : h '' K ⊆ Γ := by rw [← hs]; exact image_mono hK
    rcases hsep _ hK' (hKc.image _ h.continuous.continuousOn) ⟨_, hcK, h.apply_symm_apply c⟩
        ⟨_, hdK, h.apply_symm_apply d⟩ with h' | h'
    · left
      obtain ⟨w, hw, hwa⟩ := h'
      rwa [← hwa, h.symm_apply_apply]
    · right
      obtain ⟨w, hw, hwb⟩ := h'
      rwa [← hwb, h.symm_apply_apply]
  obtain ⟨s, hs', t, ht, hst⟩ := disc_crossing_of_sep (hsph a ha) (hsph b hb)
    (fun h' => hab (h.symm.injective h')) (hsph c hc) (hsph d hd) hsep'
    (h.symm.continuous.comp_continuousOn hP) (h.symm.continuous.comp_continuousOn hQ)
    (fun s hs => hsymm _ (hPD hs)) (fun t ht => hsymm _ (hQD ht))
    (by simp only [Function.comp_apply, hP0]) (by simp only [Function.comp_apply, hP1])
    (by simp only [Function.comp_apply, hQ0]) (by simp only [Function.comp_apply, hQ1])
  exact ⟨s, hs', t, ht, h.symm.injective hst⟩

end InteractingSLE.WangWu
