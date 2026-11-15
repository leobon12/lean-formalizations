/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2Wind
import InteractingSLE.Foundations.OrientationCrosscut
import InteractingSLE.Spec.Supplement.S9BTransfer

/-!
# Lemma S2: the closed walk `β̂[0, t_L]` + lower semicircle

Packet PROVE-T14-SB4. For a proper curve `γ` from `0` that visits `L < 0` at `t_L`, the proof of Lemma S2 (supplement
p. 578) closes the witness prefix `γ([0, t_L])` along the real segment `[L, 0]`. Here it is closed instead along the
lower semicircle `S⁻` over `[L, 0]` (the segment would lie on the loop; the semicircle keeps `(L, 0)` off it), in the
normalized coordinate `u = (2/L) z − 1` (`0 ↦ −1`, `L ↦ 1`, the closed upper half-plane onto the closed lower one),
where the loop is ORIENT's reference loop `crossLoop` of the normalized arc, closed by the upper unit semicircle.

* `s2Wind L γ t_L z`: the winding number of this loop about `z`;
* `s2Wind_eq_one`: it is `1` in the open lower half-disc over `(L, 0)` (crossing lemma at the bottom of the
  semicircle against the clockwise circle, then convexity);
* `s2Wind_eq_zero_of_outer`: `0` below the axis outside that disc (a vertical ray to infinity);
* `s2Wind_eq_of_isPreconnected`, `s2Wind_eq_zero_of_isPreconnected`: constant on preconnected sets off the loop,
  `0` on unbounded ones;
* `mem_closure_s2Wind_ne_zero`: every interior point of the witness prefix is a limit of points about which the loop
  winds (a simple loop bounds its winding set, `mem_closure_windNum_ne_zero`);
* `s2AWind_eq_add`: the additivity behind (S2.2): for a path `p` from `0` to `L` (a part of the history), the loop
  `p` + semicircle winds about `z` as often as the loop `γ([0, t_L])` + semicircle plus the closed walk
  `p − γ([0, t_L])`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped Real NNReal
open InteractingSLE.Orientation
open InteractingSLE.WangWu (semiArc crossRange upperParam)

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### The normalizing map -/

/-- The normalizing affine map `z ↦ (2/L) z − 1` (`0 ↦ −1`, `L ↦ 1`). -/
def s2Nrm (L : ℝ) (z : ℂ) : ℂ := ((2 / L : ℝ) : ℂ) * z - 1

/-- Its inverse `u ↦ (L/2)(u + 1)`. -/
def s2NrmInv (L : ℝ) (u : ℂ) : ℂ := ((L / 2 : ℝ) : ℂ) * (u + 1)

theorem s2NrmInv_s2Nrm {L : ℝ} (hL : L ≠ 0) (z : ℂ) : s2NrmInv L (s2Nrm L z) = z := by
  simp only [s2NrmInv, s2Nrm, sub_add_cancel, ← mul_assoc, ← ofReal_mul]
  rw [show L / 2 * (2 / L) = 1 by field_simp, ofReal_one, one_mul]

theorem s2Nrm_s2NrmInv {L : ℝ} (hL : L ≠ 0) (u : ℂ) : s2Nrm L (s2NrmInv L u) = u := by
  simp only [s2NrmInv, s2Nrm, ← mul_assoc, ← ofReal_mul]
  rw [show 2 / L * (L / 2) = 1 by field_simp, ofReal_one, one_mul, add_sub_cancel_right]

theorem continuous_s2Nrm (L : ℝ) : Continuous (s2Nrm L) := by unfold s2Nrm; fun_prop

theorem continuous_s2NrmInv (L : ℝ) : Continuous (s2NrmInv L) := by unfold s2NrmInv; fun_prop

theorem s2Nrm_zero (L : ℝ) : s2Nrm L 0 = -1 := by simp [s2Nrm]

theorem s2Nrm_self {L : ℝ} (hL : L ≠ 0) : s2Nrm L L = 1 := by
  simp only [s2Nrm, ← ofReal_mul]
  rw [show 2 / L * L = 2 by field_simp]
  norm_num

theorem im_s2Nrm (L : ℝ) (z : ℂ) : (s2Nrm L z).im = 2 / L * z.im := by simp [s2Nrm]

theorem re_s2Nrm (L : ℝ) (z : ℂ) : (s2Nrm L z).re = 2 / L * z.re - 1 := by simp [s2Nrm]

theorem s2Nrm_injective {L : ℝ} (hL : L ≠ 0) : Function.Injective (s2Nrm L) := fun z w h => by
  rw [← s2NrmInv_s2Nrm hL z, h, s2NrmInv_s2Nrm hL]

/-- The normalizing map keeps sets unbounded. -/
theorem not_isBounded_image_s2Nrm {L : ℝ} (hL : L ≠ 0) {S : Set ℂ} (hS : ¬ IsBounded S) :
    ¬ IsBounded (s2Nrm L '' S) := fun hb => hS <| by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨|L / 2| * (M + 1), fun z hz => ?_⟩
  have h1 := hM _ (mem_image_of_mem _ hz)
  rw [← s2NrmInv_s2Nrm hL z, s2NrmInv, norm_mul, norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by rw [norm_one]; linarith)) (abs_nonneg _)

/-- For `L < 0`, the closed upper half-plane goes to the closed lower one. -/
theorem im_s2Nrm_nonpos {L : ℝ} (hL : L < 0) {z : ℂ} (hz : 0 ≤ z.im) : (s2Nrm L z).im ≤ 0 := by
  rw [im_s2Nrm]
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos zero_le_two hL.le) hz

theorem im_s2Nrm_pos {L : ℝ} (hL : L < 0) {z : ℂ} (hz : z.im < 0) : 0 < (s2Nrm L z).im := by
  rw [im_s2Nrm]
  exact mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg two_pos hL) hz

/-- The real points of `(L, 0)` go into the open unit disc. -/
theorem norm_s2Nrm_ofReal_lt_one {L : ℝ} (hL : L < 0) {x : ℝ} (hx : x ∈ Ioo L 0) : ‖s2Nrm L x‖ < 1 := by
  have e : s2Nrm L x = ((2 / L * x - 1 : ℝ) : ℂ) := by simp [s2Nrm]
  rw [e, norm_real, Real.norm_eq_abs, abs_lt]
  have h1 : 0 < 2 / L * x := mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg two_pos hL) hx.2
  have h2 : 2 / L * x < 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff_of_neg hL]
    linarith [hx.1]
  constructor <;> linarith

/-- The real points off `[L, 0]` go outside the closed unit disc. -/
theorem one_lt_norm_s2Nrm_ofReal {L : ℝ} (hL : L < 0) {x : ℝ} (hx : x < L ∨ 0 < x) : 1 < ‖s2Nrm L x‖ := by
  have e : s2Nrm L x = ((2 / L * x - 1 : ℝ) : ℂ) := by simp [s2Nrm]
  rw [e, norm_real, Real.norm_eq_abs]
  rcases hx with hx | hx
  · have h2 : 2 < 2 / L * x := by
      rw [div_mul_eq_mul_div, lt_div_iff_of_neg hL]
      linarith
    rw [abs_of_pos (by linarith)]
    linarith
  · have h1 : 2 / L * x < 0 := mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg two_pos hL) hx
    rw [abs_of_neg (by linarith)]
    linarith

/-! ### The lower semicircle `S⁻` over `[L, 0]` -/

/-- The lower semicircle over `[L, 0]`: the preimage of the upper unit semicircle. -/
def s2Lower (L : ℝ) : Set ℂ := {z | s2Nrm L z ∈ semiArc 1}

theorem im_nonpos_of_mem_s2Lower {L : ℝ} (hL : L < 0) {z : ℂ} (hz : z ∈ s2Lower L) : z.im ≤ 0 := by
  have h := hz.2
  rw [one_mul, im_s2Nrm] at h
  by_contra hc
  have : 2 / L * z.im < 0 := mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg two_pos hL) (not_le.1 hc)
  linarith

theorem eq_or_eq_of_mem_s2Lower {L : ℝ} (hL : L < 0) {z : ℂ} (hz : z ∈ s2Lower L) (h0 : z.im = 0) :
    z = 0 ∨ z = L := by
  have hn := hz.1
  have hu : s2Nrm L z = ((2 / L * z.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s2Nrm, h0]
  rw [hu, norm_real, Real.norm_eq_abs] at hn
  have hL0 : L ≠ 0 := hL.ne
  rcases abs_eq (zero_le_one' ℝ) |>.1 hn with h | h
  · right
    apply Complex.ext
    · simp only [ofReal_re]
      field_simp at h
      linarith
    · simp [h0]
  · left
    apply Complex.ext
    · simp only [zero_re]
      have : 2 / L * z.re = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (div_ne_zero two_ne_zero hL0)
      · exact h'
    · simp [h0]

theorem re_neg_of_mem_s2Lower {L : ℝ} (hL : L < 0) {z : ℂ} (hz : z ∈ s2Lower L) (him : z.im < 0) :
    z.re < 0 := by
  have hn := hz.1
  by_contra hc
  have hre : (s2Nrm L z).re ≤ -1 := by
    rw [re_s2Nrm]
    have : 2 / L * z.re ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos zero_le_two hL.le) (not_lt.1 hc)
    linarith
  have him' : 0 < (s2Nrm L z).im := im_s2Nrm_pos hL him
  have : 1 < ‖s2Nrm L z‖ := by
    have h1 : 1 < (s2Nrm L z).re ^ 2 + (s2Nrm L z).im ^ 2 := by nlinarith
    have h2 : ‖s2Nrm L z‖ ^ 2 = (s2Nrm L z).re ^ 2 + (s2Nrm L z).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg (s2Nrm L z)]
  rw [hn] at this
  exact lt_irrefl _ this

/-! ### The normalized arc and the loop -/

/-- The normalized initial witness arc `t ↦ s2Nrm L (γ(t_L t))`, from `−1` to `1`. -/
def s2Arc (L : ℝ) (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (t : ℝ) : ℂ := s2Nrm L (Supp9B.seedLine γ ((tL : ℝ) * t))

/-- The closed walk `γ([0, t_L])` + `S⁻`, normalized: ORIENT's reference loop of `s2Arc`. -/
def s2Loop (L : ℝ) (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : ℝ → ℂ := crossLoop (s2Arc L γ tL)

/-- The winding number of the closed walk `γ([0, t_L])` + `S⁻` about `z`. -/
def s2Wind (L : ℝ) (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (z : ℂ) : ℤ := windNum (s2Loop L γ tL) (s2Nrm L z)

section Loop

variable {L : ℝ} {γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

theorem continuous_s2Arc (hγ : Supp9B.IsProperCurve γ) : Continuous (s2Arc L γ tL) :=
  (continuous_s2Nrm L).comp ((Supp9B.continuous_seedLine hγ.1).comp (continuous_const.mul continuous_id))

theorem s2Arc_zero (hγ0 : γ 0 = 0) : s2Arc L γ tL 0 = -1 := by
  simp [s2Arc, Supp9B.seedLine, hγ0, s2Nrm_zero]

theorem s2Arc_one (hL : L ≠ 0) (htL : γ tL = L) : s2Arc L γ tL 1 = 1 := by
  rw [s2Arc, mul_one, Supp9B.seedLine_coe, htL, s2Nrm_self hL]

theorem s2Arc_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ s : ℝ≥0, s ≤ tL ∧ s = (tL : ℝ) * t ∧ s2Arc L γ tL t = s2Nrm L (γ s) := by
  have h0 : 0 ≤ (tL : ℝ) * t := mul_nonneg tL.2 ht.1
  refine ⟨⟨(tL : ℝ) * t, h0⟩, ?_, rfl, ?_⟩
  · show (tL : ℝ) * t ≤ tL
    exact mul_le_of_le_one_right tL.2 ht.2
  · rw [s2Arc]
    congr 1
    have := Supp9B.seedLine_coe γ ⟨(tL : ℝ) * t, h0⟩
    exact this

theorem im_s2Arc_nonpos (hγ : Supp9B.IsProperCurve γ) (hL : L < 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (s2Arc L γ tL t).im ≤ 0 := by
  obtain ⟨s, -, -, e⟩ := s2Arc_eq (L := L) (γ := γ) ht
  rw [e]
  exact im_s2Nrm_nonpos hL (hγ.2.2.1 s)

theorem injOn_s2Arc (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L ≠ 0) (htL : 0 < tL) :
    InjOn (s2Arc L γ tL) (Icc 0 1) := by
  intro s hs t ht h
  have h1 := Supp9B.seedLine_injective hγ (by rw [hγ0]; rfl) (s2Nrm_injective hL h)
  have htL' : (0 : ℝ) < tL := htL
  exact mul_left_cancel₀ htL'.ne' h1

theorem continuousOn_s2Loop (hγ : Supp9B.IsProperCurve γ) (hL : L ≠ 0) (htL : γ tL = L) :
    ContinuousOn (s2Loop L γ tL) (Icc 0 1) :=
  continuousOn_crossLoop (continuous_s2Arc hγ).continuousOn (s2Arc_one hL htL)

theorem s2Loop_loop (hγ0 : γ 0 = 0) (hL : L ≠ 0) (htL : γ tL = L) : s2Loop L γ tL 0 = s2Loop L γ tL 1 :=
  crossLoop_loop (s2Arc_zero hγ0) (s2Arc_one hL htL)

/-- The points of the normalized loop are in the closed lower half-plane or on the unit circle. -/
theorem im_nonpos_or_norm_eq_one (hγ : Supp9B.IsProperCurve γ) (hL : L < 0) (htL : γ tL = L) {u : ℂ}
    (hu : u ∈ s2Loop L γ tL '' Icc 0 1) : u.im ≤ 0 ∨ ‖u‖ = 1 := by
  rcases image_crossLoop_subset (s2Arc_one hL.ne htL) hu with ⟨t, ht, rfl⟩ | h
  · exact Or.inl (im_s2Arc_nonpos hγ hL ht)
  · exact Or.inr h.1

theorem s2Loop_of_gt {t : ℝ} (hL : L ≠ 0) (htL : γ tL = L) (ht : 1 / 2 < t) (ht1 : t < 1) :
    s2Loop L γ tL t = exp (((π * (2 * t - 1) : ℝ) : ℂ) * I) ∧ 0 < (s2Loop L γ tL t).im := by
  have e := crossLoop_of_ge (s2Arc_one (γ := γ) (tL := tL) hL htL) ht.le
  refine ⟨e, ?_⟩
  rw [s2Loop, e, exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- The normalized loop is simple. -/
theorem injOn_s2Loop (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L)
    (htL0 : 0 < tL) : InjOn (s2Loop L γ tL) (Ico 0 1) := by
  have hlo : ∀ t ∈ Icc (0 : ℝ) (1 / 2), s2Loop L γ tL t = s2Arc L γ tL (2 * t) ∧
      (s2Loop L γ tL t).im ≤ 0 := fun t ht => by
    have e : s2Loop L γ tL t = s2Arc L γ tL (2 * t) := crossLoop_of_le ht.2
    exact ⟨e, e ▸ im_s2Arc_nonpos hγ hL ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  intro s hs t ht hst
  by_cases hs2 : s ≤ 1 / 2 <;> by_cases ht2 : t ≤ 1 / 2
  · obtain ⟨es, -⟩ := hlo s ⟨hs.1, hs2⟩
    obtain ⟨et, -⟩ := hlo t ⟨ht.1, ht2⟩
    rw [es, et] at hst
    have := injOn_s2Arc hγ hγ0 hL.ne htL0 ⟨by linarith [hs.1], by linarith⟩
      ⟨by linarith [ht.1], by linarith⟩ hst
    linarith
  · have h1 := (hlo s ⟨hs.1, hs2⟩).2
    have h2 := (s2Loop_of_gt hL.ne htL (not_le.1 ht2) ht.2).2
    rw [hst] at h1
    linarith
  · have h1 := (hlo t ⟨ht.1, ht2⟩).2
    have h2 := (s2Loop_of_gt hL.ne htL (not_le.1 hs2) hs.2).2
    rw [← hst] at h1
    linarith
  · obtain ⟨es, -⟩ := s2Loop_of_gt hL.ne htL (not_le.1 hs2) hs.2
    obtain ⟨et, -⟩ := s2Loop_of_gt hL.ne htL (not_le.1 ht2) ht.2
    rw [es, et] at hst
    have hc := congrArg Complex.re hst
    rw [exp_ofReal_mul_I_re, exp_ofReal_mul_I_re] at hc
    have := Real.injOn_cos ⟨by nlinarith [Real.pi_pos, not_le.1 hs2], by nlinarith [Real.pi_pos, hs.2]⟩
      ⟨by nlinarith [Real.pi_pos, not_le.1 ht2], by nlinarith [Real.pi_pos, ht.2]⟩ hc
    have hπ := Real.pi_pos
    have : 2 * s - 1 = 2 * t - 1 := mul_left_cancel₀ hπ.ne' this
    linarith

/-- **The loop winds once about the open lower half-disc over `(L, 0)`** (normalized: the open upper half of the
unit disc). Crossing lemma at `i` against the clockwise unit circle; the point `(1 + η) i` is joined to infinity by
a vertical ray off the loop. -/
theorem windNum_s2Loop_eq_one (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L)
    {u : ℂ} (hu : ‖u‖ < 1) (hui : 0 < u.im) : windNum (s2Loop L γ tL) u = 1 := by
  set α := s2Arc L γ tL with hαdef
  have hα1 : α 1 = 1 := s2Arc_one hL.ne htL
  have hα0 : α 0 = -1 := s2Arc_zero hγ0
  have hγc : ContinuousOn (crossLoop α) (Icc 0 1) := continuousOn_crossLoop (continuous_s2Arc hγ).continuousOn hα1
  have hγl := crossLoop_loop hα0 hα1
  have hδ : ContinuousOn cwLoop (Icc 0 1) := continuous_cwLoop.continuousOn
  have hδl : cwLoop 0 = cwLoop 1 := by rw [cwLoop_zero, cwLoop_one]
  have hαim : ∀ t ∈ Icc (0 : ℝ) 1, (α t).im ≤ 0 := fun t ht => im_s2Arc_nonpos hγ hL ht
  have himg : ∀ z ∈ crossLoop α '' Icc 0 1, z.im ≤ 0 ∨ ‖z‖ = 1 := fun z hz =>
    im_nonpos_or_norm_eq_one hγ hL htL hz
  have hp : I ∉ crossLoop α '' Icc 0 (1 / 2) ∪ crossLoop α '' Icc 1 1 ∪ cwLoop '' Icc 0 (1 / 2) ∪
      cwLoop '' Icc 1 1 := by
    rintro (((⟨t, ht, he⟩ | ⟨t, ht, he⟩) | ⟨t, ht, he⟩) | ⟨t, ht, he⟩)
    · rw [crossLoop_of_le ht.2] at he
      have := hαim (2 * t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [he] at this
      norm_num at this
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, crossLoop_one hα1] at he
      have := congrArg Complex.im he
      simp at this
    · have h := im_cwLoop_nonpos ht
      rw [he] at h
      norm_num at h
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, cwLoop_one] at he
      have := congrArg Complex.im he
      simp at this
  obtain ⟨ε, hε, hcross⟩ := windNum_add_windNum_eq hγc hδ hγl hδl (A := semiArc 1)
    (fun w hw => hasLogOn_semiArc hw) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl
    (fun t ht => crossLoop_mem_semiArc hα1 ht) (fun t ht => cwLoop_mem_semiArc ht)
    (by rw [crossLoop_half hα1, cwLoop_one]) (by rw [crossLoop_one hα1, cwLoop_half]) hp
  set η := min (ε / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  set w₁ : ℂ := ((1 - η : ℝ) : ℂ) * I with hw₁
  set w₂ : ℂ := ((1 + η : ℝ) : ℂ) * I with hw₂
  have hn₁ : ‖w₁‖ = 1 - η := by
    rw [hw₁, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hn₂ : ‖w₂‖ = 1 + η := by
    rw [hw₂, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hd₁ : dist w₁ I = η := by
    rw [dist_eq_norm, show w₁ - I = ((-η : ℝ) : ℂ) * I by rw [hw₁]; push_cast; ring, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hη0]
  have hd₂ : dist w₂ I = η := by
    rw [dist_eq_norm, show w₂ - I = ((η : ℝ) : ℂ) * I by rw [hw₂]; push_cast; ring, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs, abs_of_pos hη0]
  have hw₁A : w₁ ∉ semiArc 1 := fun h => by have := h.1; rw [hn₁] at this; linarith
  have hw₂A : w₂ ∉ semiArc 1 := fun h => by have := h.1; rw [hn₂] at this; linarith
  have key := hcross w₁ (by rw [mem_ball, hd₁]; exact hηε) w₂ (by rw [mem_ball, hd₂]; exact hηε) hw₁A hw₂A
  -- the vertical ray above `w₂`
  set S : Set ℂ := (fun s : ℝ => (s : ℂ) * I) '' Ioi 1 with hS
  have hSc : IsPreconnected S := isPreconnected_Ioi.image _ (by fun_prop)
  have hSu : ¬ IsBounded S := fun hb => by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    have h := hM _ (mem_image_of_mem _ (show max M 1 + 1 ∈ Ioi (1 : ℝ) by
      show (1 : ℝ) < max M 1 + 1
      linarith [le_max_right M 1]))
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [le_max_right M 1])] at h
    linarith [le_max_left M 1]
  have hSd : Disjoint S (crossLoop α '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun z hz hzγ => ?_
    obtain ⟨s, hs, rfl⟩ := hz
    have hs1 : (1 : ℝ) < s := hs
    rcases himg _ hzγ with h | h
    · simp at h
      linarith
    · rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h
      linarith
  have hγ₂ : windNum (crossLoop α) w₂ = 0 :=
    windNum_eq_zero_of_isPreconnected hγc hγl hSc hSu hSd ⟨1 + η, show (1 : ℝ) < 1 + η by linarith, rfl⟩
  have hδ₂ : windNum cwLoop w₂ = 0 := windNum_eq_zero_of_norm_lt hδ hδl fun t _ => by
    rw [hn₂, norm_cwLoop]; linarith
  rw [hγ₂, hδ₂, windNum_cwLoop (by rw [hn₁]; linarith)] at key
  have h1 : windNum (crossLoop α) w₁ = 1 := by linarith
  -- constancy on the open upper half-disc
  have hK : IsPreconnected (ball (0 : ℂ) 1 ∩ {z | 0 < z.im}) :=
    ((convex_ball 0 1).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hKd : Disjoint (ball (0 : ℂ) 1 ∩ {z | 0 < z.im}) (crossLoop α '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun z hz hzγ => ?_
    rcases himg _ hzγ with h | h
    · exact absurd hz.2 (not_lt.2 h)
    · have := mem_ball_zero_iff.1 hz.1
      rw [h] at this
      exact lt_irrefl _ this
  have hw₁K : w₁ ∈ ball (0 : ℂ) 1 ∩ {z | 0 < z.im} := by
    refine ⟨mem_ball_zero_iff.2 (by rw [hn₁]; linarith), ?_⟩
    show 0 < w₁.im
    rw [hw₁]
    simp
    linarith
  show windNum (crossLoop α) u = 1
  rw [windNum_eq_of_isPreconnected hγc hγl hK hKd ⟨mem_ball_zero_iff.2 hu, hui⟩ hw₁K, h1]

/-! ### The image of the loop, in the original coordinate -/

/-- A point whose normalization is on the loop is on the witness prefix or on `S⁻`. -/
theorem mem_of_s2Nrm_mem_image (hL : L < 0) (htL : γ tL = L) {z : ℂ}
    (hz : s2Nrm L z ∈ s2Loop L γ tL '' Icc 0 1) : z ∈ γ '' Icc 0 tL ∨ z ∈ s2Lower L := by
  rcases image_crossLoop_subset (s2Arc_one (γ := γ) (tL := tL) hL.ne htL) hz with ⟨t, ht, he⟩ | h
  · obtain ⟨s, hs, -, e⟩ := s2Arc_eq (L := L) (γ := γ) (tL := tL) ht
    rw [e] at he
    exact Or.inl ⟨s, ⟨zero_le, hs⟩, s2Nrm_injective hL.ne he⟩
  · exact Or.inr h

theorem s2Nrm_mem_image_of_le (htL0 : 0 < tL) {s : ℝ≥0} (hs : s ≤ tL) :
    s2Nrm L (γ s) ∈ s2Loop L γ tL '' Icc 0 1 := by
  have htL' : (0 : ℝ) < tL := htL0
  have hs' : (s : ℝ) ≤ tL := hs
  refine ⟨s / (2 * tL), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith [s.2]
  · rw [s2Loop, crossLoop_of_le (by rw [div_le_iff₀ (by positivity)]; linarith), s2Arc,
      show (tL : ℝ) * (2 * (s / (2 * tL))) = s by field_simp, Supp9B.seedLine_coe]

theorem s2Nrm_mem_image_of_mem_s2Lower (hL : L ≠ 0) (htL : γ tL = L) {z : ℂ} (hz : z ∈ s2Lower L) :
    s2Nrm L z ∈ s2Loop L γ tL '' Icc 0 1 := by
  have hz' : s2Nrm L z ∈ upperParam '' Icc 0 1 := by rw [WangWu.image_upperParam]; exact hz
  obtain ⟨s, hs, e⟩ := hz'
  refine ⟨1 - s / 2, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
  rw [s2Loop, crossLoop_of_ge (s2Arc_one hL htL) (by linarith [hs.2]), ← e, WangWu.upperParam]
  congr 3
  ring

/-- The loop winds `0` times about its own points. -/
theorem s2Wind_eq_zero_of_mem (hL : L < 0) (htL : γ tL = L) (htL0 : 0 < tL) {z : ℂ}
    (hz : z ∈ γ '' Icc 0 tL ∨ z ∈ s2Lower L) : s2Wind L γ tL z = 0 := by
  refine windNum_eq_zero_of_mem_image ?_
  rcases hz with ⟨s, hs, rfl⟩ | hz
  · exact s2Nrm_mem_image_of_le htL0 hs.2
  · exact s2Nrm_mem_image_of_mem_s2Lower hL.ne htL hz

theorem notMem_of_s2Wind_ne_zero (hL : L < 0) (htL : γ tL = L) (htL0 : 0 < tL) {z : ℂ}
    (hz : s2Wind L γ tL z ≠ 0) : z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L :=
  ⟨fun h => hz (s2Wind_eq_zero_of_mem hL htL htL0 (Or.inl h)),
    fun h => hz (s2Wind_eq_zero_of_mem hL htL htL0 (Or.inr h))⟩

/-! ### Winding facts in the original coordinate -/

theorem s2Loop_ne (hL : L < 0) (htL : γ tL = L) {z : ℂ} (hzγ : z ∉ γ '' Icc 0 tL) (hzl : z ∉ s2Lower L) :
    ∀ t ∈ Icc (0 : ℝ) 1, s2Loop L γ tL t ≠ s2Nrm L z := fun t ht h => by
  rcases mem_of_s2Nrm_mem_image hL htL ⟨t, ht, h⟩ with h' | h'
  · exact hzγ h'
  · exact hzl h'

theorem disjoint_image_of_forall_ne {Λ : ℝ → ℂ} {S : Set ℂ}
    (hS : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, Λ t ≠ s2Nrm L z) : Disjoint (s2Nrm L '' S) (Λ '' Icc 0 1) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨z, hz, rfl⟩ ⟨t, ht, he⟩
  exact hS z hz t ht he

/-- The winding number is constant on preconnected sets off `γ([0, t_L]) ∪ S⁻`. -/
theorem s2Wind_eq_of_isPreconnected (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0)
    (htL : γ tL = L) {S : Set ℂ} (hSc : IsPreconnected S) (hS : ∀ z ∈ S, z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L)
    {z₁ z₂ : ℂ} (h₁ : z₁ ∈ S) (h₂ : z₂ ∈ S) : s2Wind L γ tL z₁ = s2Wind L γ tL z₂ :=
  windNum_eq_of_isPreconnected (continuousOn_s2Loop hγ hL.ne htL) (s2Loop_loop hγ0 hL.ne htL)
    (hSc.image _ (continuous_s2Nrm L).continuousOn)
    (disjoint_image_of_forall_ne fun z hz => s2Loop_ne hL htL (hS z hz).1 (hS z hz).2)
    (mem_image_of_mem _ h₁) (mem_image_of_mem _ h₂)

/-- The winding number vanishes on unbounded preconnected sets off `γ([0, t_L]) ∪ S⁻`. -/
theorem s2Wind_eq_zero_of_isPreconnected (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0)
    (htL : γ tL = L) {S : Set ℂ} (hSc : IsPreconnected S) (hSu : ¬ IsBounded S)
    (hS : ∀ z ∈ S, z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L) {z : ℂ} (hz : z ∈ S) : s2Wind L γ tL z = 0 :=
  windNum_eq_zero_of_isPreconnected (continuousOn_s2Loop hγ hL.ne htL) (s2Loop_loop hγ0 hL.ne htL)
    (hSc.image _ (continuous_s2Nrm L).continuousOn) (not_isBounded_image_s2Nrm hL.ne hSu)
    (disjoint_image_of_forall_ne fun z hz => s2Loop_ne hL htL (hS z hz).1 (hS z hz).2) (mem_image_of_mem _ hz)

/-- **Winding `1` in the open lower half-disc over `(L, 0)`.** -/
theorem s2Wind_eq_one (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L) {z : ℂ}
    (hz : z.im < 0) (hn : ‖s2Nrm L z‖ < 1) : s2Wind L γ tL z = 1 :=
  windNum_s2Loop_eq_one hγ hγ0 hL htL hn (im_s2Nrm_pos hL hz)

/-- **Winding `0` below the axis outside the half-disc** (a vertical ray to infinity, in the normalized coordinate). -/
theorem s2Wind_eq_zero_of_outer (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L)
    {z : ℂ} (hz : z.im < 0) (hn : 1 < ‖s2Nrm L z‖) : s2Wind L γ tL z = 0 := by
  set u := s2Nrm L z with hu
  have hui : 0 < u.im := im_s2Nrm_pos hL hz
  set S : Set ℂ := (fun s : ℝ => u + (s : ℂ) * I) '' Ici 0 with hS
  have hSc : IsPreconnected S := isPreconnected_Ici.image _ (by fun_prop)
  have hSu : ¬ IsBounded S := fun hb => by
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    have hM0 : ‖u‖ ≤ M := by
      have := hM u ⟨0, Set.self_mem_Ici, by simp⟩
      exact this
    have hpos : (0 : ℝ) ≤ ‖u‖ + M + 1 := by linarith [norm_nonneg u]
    have h := hM _ (mem_image_of_mem _ (show ‖u‖ + M + 1 ∈ Ici (0 : ℝ) from hpos))
    have h2 : ‖((‖u‖ + M + 1 : ℝ) : ℂ) * I‖ ≤ ‖u + ((‖u‖ + M + 1 : ℝ) : ℂ) * I‖ + ‖u‖ := by
      calc ‖((‖u‖ + M + 1 : ℝ) : ℂ) * I‖ = ‖(u + ((‖u‖ + M + 1 : ℝ) : ℂ) * I) - u‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at h2
    linarith
  have hSd : Disjoint S (s2Loop L γ tL '' Icc 0 1) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ hγ'
    have hs0 : (0 : ℝ) ≤ s := hs
    rcases im_nonpos_or_norm_eq_one hγ hL htL hγ' with h | h
    · simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero] at h
      linarith
    · have e : ‖u + (s : ℂ) * I‖ ^ 2 = u.re ^ 2 + (u.im + s) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im,
          mul_im]
        ring
      have e' : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      rw [h] at e
      have h1 : 1 < ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
      nlinarith
  exact windNum_eq_zero_of_isPreconnected (continuousOn_s2Loop hγ hL.ne htL) (s2Loop_loop hγ0 hL.ne htL) hSc hSu
    hSd ⟨0, Set.self_mem_Ici, by simp [hu]⟩

/-- **Every interior point of the witness prefix is a limit of points about which the loop winds.** -/
theorem mem_closure_s2Wind_ne_zero (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L)
    {s : ℝ≥0} (hs0 : 0 < s) (hs : s < tL) : γ s ∈ closure {z | s2Wind L γ tL z ≠ 0} := by
  have htL0 : 0 < tL := hs0.trans hs
  have htL' : (0 : ℝ) < tL := htL0
  have hs0' : (0 : ℝ) < s := hs0
  have hs' : (s : ℝ) < tL := hs
  set t₀ : ℝ := s / (2 * tL) with ht₀def
  have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩
  have hw₀ : windNum (s2Loop L γ tL) (I / 2) ≠ 0 := by
    rw [windNum_s2Loop_eq_one hγ hγ0 hL htL (by rw [norm_div, norm_I]; norm_num) (by norm_num)]
    norm_num
  have h := mem_closure_windNum_ne_zero (continuousOn_s2Loop hγ hL.ne htL) (s2Loop_loop hγ0 hL.ne htL)
    (injOn_s2Loop hγ hγ0 hL htL htL0) hw₀ ht₀
  have e : s2Loop L γ tL t₀ = s2Nrm L (γ s) := by
    rw [s2Loop, crossLoop_of_le (by rw [ht₀def, div_le_iff₀ (by positivity)]; linarith), s2Arc,
      show (tL : ℝ) * (2 * (s / (2 * tL))) = s by field_simp, Supp9B.seedLine_coe]
  rw [e] at h
  have h2 := image_closure_subset_closure_image (continuous_s2NrmInv L) (mem_image_of_mem (s2NrmInv L) h)
  rw [s2NrmInv_s2Nrm hL.ne] at h2
  refine closure_mono ?_ h2
  rintro _ ⟨u, hu, rfl⟩
  show windNum (s2Loop L γ tL) (s2Nrm L (s2NrmInv L u)) ≠ 0
  rw [s2Nrm_s2NrmInv hL.ne]
  exact hu

/-! ### The history loop and (S2.2) -/

/-- The normalized history path `t ↦ s2Nrm L (p(σ t))`, from `p(0)` to `p(σ)`. -/
def s2PArc (L : ℝ) (p : ℝ → ℂ) (σ : ℝ) (t : ℝ) : ℂ := s2Nrm L (p (σ * t))

/-- The closed walk along the history path `p([0, σ])` and back along the witness prefix `γ([0, t_L])`,
normalized. -/
def s2DLoop (L : ℝ) (p : ℝ → ℂ) (σ : ℝ) (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then s2PArc L p σ (2 * t) else s2Arc L γ tL (2 - 2 * t)

section ALoop

variable {p : ℝ → ℂ} {σ : ℝ}

theorem mapsTo_mul_Icc (hσ : σ ∈ Icc (0 : ℝ) 1) : MapsTo (fun t : ℝ => σ * t) (Icc 0 1) (Icc 0 1) := fun _ ht =>
  ⟨mul_nonneg hσ.1 ht.1, (mul_le_mul hσ.2 ht.2 ht.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem continuousOn_s2PArc (hp : ContinuousOn p (Icc 0 1)) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (s2PArc L p σ) (Icc 0 1) :=
  (continuous_s2Nrm L).comp_continuousOn
    (hp.comp (continuous_const.mul continuous_id).continuousOn (mapsTo_mul_Icc hσ))

theorem s2PArc_zero (hp0 : p 0 = 0) : s2PArc L p σ 0 = -1 := by simp [s2PArc, hp0, s2Nrm_zero]

theorem s2PArc_one (hL : L ≠ 0) (hpσ : p σ = L) : s2PArc L p σ 1 = 1 := by
  rw [s2PArc, mul_one, hpσ, s2Nrm_self hL]

theorem continuousOn_s2DLoop (hγ : Supp9B.IsProperCurve γ) (hp : ContinuousOn p (Icc 0 1))
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hL : L ≠ 0) (htL : γ tL = L) (hpσ : p σ = L) :
    ContinuousOn (s2DLoop L p σ γ tL) (Icc 0 1) := by
  have h1 : ContinuousOn (s2DLoop L p σ γ tL) (Icc 0 (1 / 2)) := by
    refine ContinuousOn.congr (f := fun t => s2PArc L p σ (2 * t)) ?_ fun t ht => by
      simp only [s2DLoop, ht.2, ↓reduceIte]
    exact (continuousOn_s2PArc hp hσ).comp (continuous_const.mul continuous_id).continuousOn fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : ContinuousOn (s2DLoop L p σ γ tL) (Icc (1 / 2) 1) := by
    refine ContinuousOn.congr (f := fun t => s2Arc L γ tL (2 - 2 * t))
      ((continuous_s2Arc hγ).comp (by fun_prop)).continuousOn fun t ht => ?_
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      simp only [s2DLoop, le_refl, ↓reduceIte]
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, s2PArc_one hL hpσ,
        s2Arc_one hL htL]
    · simp only [s2DLoop, not_le.2 h, ↓reduceIte]
  have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this

theorem s2DLoop_loop (hγ0 : γ 0 = 0) (hp0 : p 0 = 0) : s2DLoop L p σ γ tL 0 = s2DLoop L p σ γ tL 1 := by
  simp only [s2DLoop, show (0 : ℝ) ≤ 1 / 2 by norm_num, show ¬ ((1 : ℝ) ≤ 1 / 2) by norm_num, ↓reduceIte,
    mul_zero, mul_one, sub_self]
  rw [s2PArc_zero hp0, s2Arc_zero hγ0]

theorem s2ALoop_ne (hL : L ≠ 0) (hpσ : p σ = L) (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hzp : z ∉ p '' Icc 0 1)
    (hzl : z ∉ s2Lower L) : ∀ t ∈ Icc (0 : ℝ) 1, crossLoop (s2PArc L p σ) t ≠ s2Nrm L z := fun t ht h => by
  rcases image_crossLoop_subset (s2PArc_one hL hpσ) ⟨t, ht, h⟩ with ⟨t', ht', he⟩ | h'
  · exact hzp ⟨σ * t', mapsTo_mul_Icc hσ ht', s2Nrm_injective hL he⟩
  · exact hzl h'

theorem s2DLoop_ne (hL : L ≠ 0) (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hzp : z ∉ p '' Icc 0 1)
    (hzγ : z ∉ γ '' Icc 0 tL) : ∀ t ∈ Icc (0 : ℝ) 1, s2DLoop L p σ γ tL t ≠ s2Nrm L z := fun t ht h => by
  by_cases ht2 : t ≤ 1 / 2
  · simp only [s2DLoop, ht2, ↓reduceIte] at h
    exact hzp ⟨σ * (2 * t), mapsTo_mul_Icc hσ ⟨by linarith [ht.1], by linarith⟩, s2Nrm_injective hL h⟩
  · simp only [s2DLoop, ht2, ↓reduceIte] at h
    obtain ⟨s, hs, -, e⟩ := s2Arc_eq (L := L) (γ := γ) (tL := tL)
      (show 2 - 2 * t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.2], by linarith⟩)
    rw [e] at h
    exact hzγ ⟨s, ⟨zero_le, hs⟩, s2Nrm_injective hL h⟩

/-- **(S2.2), additivity**: the history loop `p([0, σ])` + `S⁻` winds about `z` as often as the closed walk
`p([0, σ]) − γ([0, t_L])` plus the witness loop `γ([0, t_L])` + `S⁻`. -/
theorem windNum_s2ALoop_eq_add (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L)
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hσ : σ ∈ Icc (0 : ℝ) 1) (hpσ : p σ = L) {z : ℂ}
    (hzp : z ∉ p '' Icc 0 1) (hzγ : z ∉ γ '' Icc 0 tL) (hzl : z ∉ s2Lower L) :
    windNum (crossLoop (s2PArc L p σ)) (s2Nrm L z) =
      windNum (s2DLoop L p σ γ tL) (s2Nrm L z) + s2Wind L γ tL z := by
  have hP1 := s2PArc_one (p := p) hL.ne hpσ
  have hα1 := s2Arc_one (γ := γ) (tL := tL) hL.ne htL
  have hPc := continuousOn_s2PArc (L := L) hp hσ
  have hαc : ContinuousOn (s2Arc L γ tL) (Icc 0 1) := (continuous_s2Arc hγ).continuousOn
  have hsc : ContinuousOn (fun s : ℝ => exp (((π * s : ℝ) : ℂ) * I)) (Icc 0 1) := by fun_prop
  have hΛ := s2Loop_ne hL htL hzγ hzl
  have eA := windNum_mul_eq_pathInc_add (continuousOn_crossLoop hPc hP1) (crossLoop_loop (s2PArc_zero hp0) hP1)
    (s2ALoop_ne hL.ne hpσ hσ hzp hzl) hPc hsc (fun t ht => crossLoop_of_le ht.2)
    (fun t ht => crossLoop_of_ge hP1 ht.1)
  have eΛ := windNum_mul_eq_pathInc_add (continuousOn_s2Loop hγ hL.ne htL) (s2Loop_loop hγ0 hL.ne htL) hΛ hαc hsc
    (fun t ht => crossLoop_of_le ht.2) (fun t ht => crossLoop_of_ge hα1 ht.1)
  have hαw : ∀ s ∈ Icc (0 : ℝ) 1, s2Arc L γ tL s ≠ s2Nrm L z := fun s hs => by
    have := hΛ (s / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rwa [s2Loop, crossLoop_of_le (by linarith [hs.2]), show 2 * (s / 2) = s by ring] at this
  have hrc : ContinuousOn (fun s => s2Arc L γ tL (1 - s)) (Icc 0 1) :=
    ((continuous_s2Arc hγ).comp (continuous_const.sub continuous_id)).continuousOn
  have eD := windNum_mul_eq_pathInc_add (continuousOn_s2DLoop hγ hp hσ hL.ne htL hpσ) (s2DLoop_loop hγ0 hp0)
    (s2DLoop_ne hL.ne hσ hzp hzγ) hPc hrc (fun t ht => by simp only [s2DLoop, ht.2, ↓reduceIte]) (fun t ht => by
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]
        simp only [s2DLoop, le_refl, ↓reduceIte]
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - (1 - 1) = 1 by norm_num, hP1, hα1]
      · simp only [s2DLoop, not_le.2 h, ↓reduceIte]
        congr 1
        ring)
  have hrev := pathInc_comp_one_sub hαc hαw
  have key : ((windNum (crossLoop (s2PArc L p σ)) (s2Nrm L z) : ℤ) : ℂ) * (2 * π * I) =
      ((windNum (s2DLoop L p σ γ tL) (s2Nrm L z) + s2Wind L γ tL z : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    rw [add_mul, eA, eD, s2Wind, eΛ, hrev]
    ring
  exact_mod_cast mul_right_cancel₀ QuantumZipper.CA.Topo.two_pi_I_ne_zero' key

/-- The closed walk `p − γ([0, t_L])` winds `0` times about unbounded preconnected sets off
`p([0, 1]) ∪ γ([0, t_L])`. -/
theorem windNum_s2DLoop_eq_zero (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) (hL : L < 0) (htL : γ tL = L)
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hσ : σ ∈ Icc (0 : ℝ) 1) (hpσ : p σ = L) {S : Set ℂ}
    (hSc : IsPreconnected S) (hSu : ¬ IsBounded S) (hS : ∀ z ∈ S, z ∉ p '' Icc 0 1 ∧ z ∉ γ '' Icc 0 tL) {z : ℂ}
    (hz : z ∈ S) : windNum (s2DLoop L p σ γ tL) (s2Nrm L z) = 0 :=
  windNum_eq_zero_of_isPreconnected (continuousOn_s2DLoop hγ hp hσ hL.ne htL hpσ) (s2DLoop_loop hγ0 hp0)
    (hSc.image _ (continuous_s2Nrm L).continuousOn) (not_isBounded_image_s2Nrm hL.ne hSu)
    (disjoint_image_of_forall_ne fun z hz => s2DLoop_ne hL.ne hσ (hS z hz).1 (hS z hz).2) (mem_image_of_mem _ hz)

/-- The history loop winds `0` times about unbounded preconnected sets off `p([0, 1]) ∪ S⁻`. -/
theorem windNum_s2ALoop_eq_zero (hL : L < 0) (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hpσ : p σ = L) {S : Set ℂ} (hSc : IsPreconnected S) (hSu : ¬ IsBounded S)
    (hS : ∀ z ∈ S, z ∉ p '' Icc 0 1 ∧ z ∉ s2Lower L) {z : ℂ} (hz : z ∈ S) :
    windNum (crossLoop (s2PArc L p σ)) (s2Nrm L z) = 0 :=
  windNum_eq_zero_of_isPreconnected (continuousOn_crossLoop (continuousOn_s2PArc hp hσ) (s2PArc_one hL.ne hpσ))
    (crossLoop_loop (s2PArc_zero hp0) (s2PArc_one hL.ne hpσ))
    (hSc.image _ (continuous_s2Nrm L).continuousOn) (not_isBounded_image_s2Nrm hL.ne hSu)
    (disjoint_image_of_forall_ne fun z hz => s2ALoop_ne hL.ne hpσ hσ (hS z hz).1 (hS z hz).2)
    (mem_image_of_mem _ hz)

end ALoop

end Loop

end SB

end Theorem14

end InteractingSLE
