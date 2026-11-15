/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Prop74BChart
import InteractingSLE.Spec.Sec7.Prop74BMain
import InteractingSLE.Foundations.OrientationDisc
import InteractingSLE.Foundations.OrientationCrosscut
import InteractingSLE.Foundations.Loewner.HullKernel

/-!
# Proposition 7.4's pocket chart preserves orientation: `PocketChartOrientationStatement` proved

Packet PROVE-ORIENT. The named input `Sec7.Prop74B.PocketChartOrientationStatement` of PROVE-PROP74B (supplement §2.3,
p. 453: "Let `φ : C → ℍ` send `x₀` to zero and `y₀` to infinity, with the left side sent to the negative half-line")
is proved: **`pocketChartOrientationStatement`**, and PROVE-PROP74B's wiring theorems lose that input
(`lemma71TwoMiddleStatement_of_fixedChart_oriented`, `prop74OrderStatement_of_fixedChart_oriented`).

## Main results

* `discExt` and its properties: the **disc extension** `g` of the inverse of a boundary map (`g(1) = q`,
  `g(w) = (Ψ|_E)⁻¹(cayleyInv w)`) is continuous and injective on the closed disc and holomorphic inside;
* **`re_pos_of_crossLoop`** (the core, for any wall `α` from `−1` to `1` in the closed disc, possibly touching the
  circle): if the pocket is on the left of `α` (the reference loop `Orientation.crossLoop α` winds once about it) and a
  point of the open wall arc is reached from infinity on the right, the boundary map sends the open arc to `(0, ∞)`;
* `pocketChartOrientationStatement`: the core for a crosscut wall (`WangWu.pocket_subset_between`,
  `crossSide_neg_props`).

## Proof of the core

The boundary map `Ψ` is real and nonzero on the open arc `α((a, b))`, so it is either positive or negative on the
whole arc. Suppose it is negative. Then the boundary loop `J(t) = g(e^{2πit})` winds once about every point of the
pocket (`Orientation.windNum_comp_circleMap_one_eq_one`) and runs from `q = α b` to `α a` along `α([a, b])` for
`t ∈ [0, 1/2]` (the negative half-line is covered by the arc), while the reference loop runs along the same arc from
`α a` to `q`. By the crossing lemma (`Orientation.windNum_add_windNum_eq`) at a point `p` of the open arc, the sum of
the two winding numbers is the same at a point of the pocket near `p` (`1 + 1`) and at a point on the right near `p`
(`0 + 0`). Contradiction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Function Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

namespace InteractingSLE.Sec7.Prop74B

/-! ### The Cayley inverse on the unit circle -/

theorem re_sq_add_im_sq_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : w.re ^ 2 + w.im ^ 2 = 1 := by
  have h := Complex.sq_norm w
  rw [hw, Complex.normSq_apply] at h
  nlinarith

theorem re_lt_one_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) : w.re < 1 := by
  have hn := re_sq_add_im_sq_of_norm_eq_one hw
  refine lt_of_le_of_ne (by nlinarith [sq_nonneg w.im]) fun h => hw1 (Complex.ext (by simpa using h) ?_)
  have h2 : w.im ^ 2 = 0 := by rw [h] at hn; linarith
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2

/-- On the unit circle, `cayleyInv w = −Im w / (1 − Re w)` is real. -/
theorem cayleyInv_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    cayleyInv w = ((-w.im / (1 - w.re) : ℝ) : ℂ) := by
  have hn := re_sq_add_im_sq_of_norm_eq_one hw
  have hx : (1 : ℝ) - w.re ≠ 0 := (sub_pos.2 (re_lt_one_of_norm_eq_one hw hw1)).ne'
  have hw1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw1)
  rw [QuantumZipper.CA.cayleyInv, div_eq_iff hw1']
  apply Complex.ext
  · simp only [mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im, ofReal_re, ofReal_im]
    field_simp
    ring
  · simp only [mul_im, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im, ofReal_re, ofReal_im]
    field_simp
    nlinarith

/-- The upper semicircle goes to the closed negative half-line. -/
theorem cayleyInv_nonpos {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (him : 0 ≤ w.im) :
    ∃ x : ℝ, x ≤ 0 ∧ cayleyInv w = x :=
  ⟨_, div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 him) (sub_pos.2 (re_lt_one_of_norm_eq_one hw hw1)).le,
    cayleyInv_of_norm_eq_one hw hw1⟩

/-- The lower semicircle goes to the closed positive half-line. -/
theorem cayleyInv_nonneg {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (him : w.im ≤ 0) :
    ∃ x : ℝ, 0 ≤ x ∧ cayleyInv w = x :=
  ⟨_, div_nonneg (neg_nonneg.2 him) (sub_pos.2 (re_lt_one_of_norm_eq_one hw hw1)).le, cayleyInv_of_norm_eq_one hw hw1⟩

theorem cayleyInv_neg_one : cayleyInv (-1) = 0 := by simp [QuantumZipper.CA.cayleyInv]

/-- `‖cayleyInv w‖ ≥ 1/‖1 − w‖` near `1`. -/
theorem one_div_le_norm_cayleyInv {w : ℂ} (hw1 : w ≠ 1) (hw : ‖w - 1‖ ≤ 1) : 1 / ‖w - 1‖ ≤ ‖cayleyInv w‖ := by
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hw1)
  have h1 : 1 ≤ ‖1 + w‖ := by
    have : ‖(2 : ℂ)‖ ≤ ‖1 + w‖ + ‖w - 1‖ := by
      calc ‖(2 : ℂ)‖ = ‖(1 + w) - (w - 1)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [show ‖(2 : ℂ)‖ = 2 by simp] at this
    linarith
  rw [QuantumZipper.CA.cayleyInv, norm_div, norm_mul, norm_I, one_mul, norm_sub_rev 1 w]
  exact div_le_div_of_nonneg_right h1 hpos.le

/-! ### The disc extension of the inverse of a boundary map -/

/-- The **disc extension** of the inverse of a boundary map `Ψ` on `E`: `g(1) = q` and
`g(w) = (Ψ|_E)⁻¹(cayleyInv w)`. -/
def discExt (Ψ : ℂ → ℂ) (E : Set ℂ) (q w : ℂ) : ℂ := if w = 1 then q else invFunOn Ψ E (cayleyInv w)

theorem discExt_one (Ψ : ℂ → ℂ) (E : Set ℂ) (q : ℂ) : discExt Ψ E q 1 = q := by simp [discExt]

theorem discExt_of_ne (Ψ : ℂ → ℂ) (E : Set ℂ) (q : ℂ) {w : ℂ} (hw : w ≠ 1) :
    discExt Ψ E q w = invFunOn Ψ E (cayleyInv w) := by simp [discExt, hw]

section DiscExt

variable {C : Set ℂ} {f Ψ : ℂ → ℂ} {q : ℂ}
variable (hCH : C ⊆ H) (hf : IsConformalBijection f C H) (hqC : ∀ x ∈ C, cayley x ≠ q)
  (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {q})) (hΨi : InjOn Ψ (closure (cayley '' C) \ {q}))
  (hΨH : MapsTo Ψ (closure (cayley '' C) \ {q}) Hbar)
  (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {q}] q) atTop)
  (hΨf : ∀ x ∈ C, f x = Ψ (cayley x))
include hCH hf hqC hΨc hΨH hΨinf hΨf

theorem discExt_spec {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) (hw1 : w ≠ 1) :
    discExt Ψ (closure (cayley '' C) \ {q}) q w ∈ closure (cayley '' C) \ {q} ∧
      Ψ (discExt Ψ (closure (cayley '' C) \ {q}) q w) = cayleyInv w := by
  rw [discExt_of_ne _ _ _ hw1]
  exact invFunOn_boundaryMap_spec hCH hf hqC hΨc hΨH hΨinf hΨf (QuantumZipper.CA.cayleyInv_mem_Hbar hw)

theorem discExt_mem_closure {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    discExt Ψ (closure (cayley '' C) \ {q}) q w ∈ closure (cayley '' C) ∨ w = 1 := by
  by_cases hw1 : w = 1
  · exact Or.inr hw1
  · exact Or.inl (discExt_spec hCH hf hqC hΨc hΨH hΨinf hΨf hw hw1).1.1

include hΨi in
/-- Inside the disc, the extension is `cayley ∘ f⁻¹ ∘ cayleyInv`. -/
theorem discExt_eq_cayley {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    invFunOn f C (cayleyInv w) ∈ C ∧
      discExt Ψ (closure (cayley '' C) \ {q}) q w = cayley (invFunOn f C (cayleyInv w)) := by
  have hwH : cayleyInv w ∈ H := QuantumZipper.CA.cayleyInv_mem_H hw
  have hw1 : w ≠ 1 := WangWu.ne_one_of_mem_ball hw
  have hz : invFunOn f C (cayleyInv w) ∈ C := invFunOn_mem (hf.2.surjOn hwH)
  have hfz : f (invFunOn f C (cayleyInv w)) = cayleyInv w := invFunOn_eq (hf.2.surjOn hwH)
  refine ⟨hz, ?_⟩
  obtain ⟨h1, h2⟩ := discExt_spec hCH hf hqC hΨc hΨH hΨinf hΨf (ball_subset_closedBall hw) hw1
  refine hΨi h1 ⟨subset_closure ⟨_, hz, rfl⟩, hqC _ hz⟩ ?_
  rw [h2, ← hΨf _ hz, hfz]

include hΨi in
theorem discExt_mem_image {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    discExt Ψ (closure (cayley '' C) \ {q}) q w ∈ cayley '' C := by
  obtain ⟨hz, he⟩ := discExt_eq_cayley hCH hf hqC hΨc hΨi hΨH hΨinf hΨf hw
  exact he ▸ ⟨_, hz, rfl⟩

/-- On the unit circle the extension avoids `cayley '' C` (real points of `Ψ` are not values of `f`). -/
theorem discExt_notMem_image {w : ℂ} (hw : ‖w‖ = 1) : discExt Ψ (closure (cayley '' C) \ {q}) q w ∉ cayley '' C := by
  rintro ⟨c, hc, he⟩
  by_cases hw1 : w = 1
  · rw [hw1, discExt_one] at he
    exact hqC c hc he
  · have hwb : w ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.2 hw.le
    have h2 := (discExt_spec hCH hf hqC hΨc hΨH hΨinf hΨf hwb hw1).2
    rw [← he, ← hΨf c hc, cayleyInv_of_norm_eq_one hw hw1] at h2
    have h3 : (0 : ℝ) < (f c).im := hf.2.mapsTo hc
    rw [h2, ofReal_im] at h3
    exact lt_irrefl 0 h3

theorem injOn_discExt : InjOn (discExt Ψ (closure (cayley '' C) \ {q}) q) (closedBall 0 1) := by
  intro w₁ hw₁ w₂ hw₂ he
  have hspec := fun {w} (hw : w ∈ closedBall (0 : ℂ) 1) (hw1 : w ≠ 1) =>
    discExt_spec hCH hf hqC hΨc hΨH hΨinf hΨf hw hw1
  by_cases h₁ : w₁ = 1 <;> by_cases h₂ : w₂ = 1
  · rw [h₁, h₂]
  · rw [h₁, discExt_one] at he
    exact absurd he.symm (hspec hw₂ h₂).1.2
  · rw [h₂, discExt_one] at he
    exact absurd he (hspec hw₁ h₁).1.2
  · have h := congrArg Ψ he
    rw [(hspec hw₁ h₁).2, (hspec hw₂ h₂).2] at h
    rw [← QuantumZipper.CA.cayley_cayleyInv h₁, ← QuantumZipper.CA.cayley_cayleyInv h₂, h]

include hΨi in
theorem continuousOn_discExt :
    ContinuousOn (discExt Ψ (closure (cayley '' C) \ {q}) q) (closedBall 0 1) := by
  set E := closure (cayley '' C) \ {q} with hE
  have hspec := fun {w} (hw : w ∈ closedBall (0 : ℂ) 1) (hw1 : w ≠ 1) =>
    discExt_spec hCH hf hqC hΨc hΨH hΨinf hΨf hw hw1
  have hinv := continuousOn_invFunOn_boundaryMap hCH hf hqC hΨc hΨi hΨH hΨinf hΨf
  intro w hw
  by_cases hw1 : w = 1
  · -- at `1`: the extension tends to `q`
    rw [hw1, ContinuousWithinAt, discExt_one, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hK : IsCompact (closure (cayley '' C) \ ball q ε) :=
      (isCompact_closure_cayley_image hCH).diff isOpen_ball
    have hKE : closure (cayley '' C) \ ball q ε ⊆ E := fun y hy =>
      ⟨hy.1, fun hyq => hy.2 (by rw [mem_singleton_iff.1 hyq]; exact mem_ball_self hε)⟩
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hΨc.mono hKE)
    set M' := max M 0
    refine ⟨1 / (M' + 1), by positivity, fun v hv hvd => ?_⟩
    by_cases hv1 : v = 1
    · rw [hv1, discExt_one, dist_self]; exact hε
    have hM'1 : 1 / (M' + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [le_max_right M 0]
    rw [dist_eq_norm] at hvd
    have hbig : M < ‖cayleyInv v‖ := by
      have h1 := one_div_le_norm_cayleyInv hv1 (hvd.le.trans hM'1)
      have h2 : M' + 1 < 1 / ‖v - 1‖ := by
        rw [lt_one_div (by positivity) (norm_pos_iff.2 (sub_ne_zero.2 hv1))]
        rw [one_div] at hvd ⊢
        exact hvd
      linarith [le_max_left M 0]
    obtain ⟨h1, h2⟩ := hspec hv hv1
    by_contra hfar
    have hmem : discExt Ψ E q v ∈ closure (cayley '' C) \ ball q ε :=
      ⟨h1.1, fun hb => hfar (by rw [mem_ball] at hb; exact hb)⟩
    have := hM _ hmem
    rw [h2] at this
    linarith
  · -- off `1`: the extension is `(Ψ|_E)⁻¹ ∘ cayleyInv`
    have hc : ContinuousWithinAt (fun v => invFunOn Ψ E (cayleyInv v)) (closedBall 0 1) w :=
      (hinv _ (QuantumZipper.CA.cayleyInv_mem_Hbar hw)).comp
        (WangWu.continuousAt_cayleyInv hw1).continuousWithinAt
        fun v hv => QuantumZipper.CA.cayleyInv_mem_Hbar hv
    refine hc.congr_of_eventuallyEq ?_ (discExt_of_ne _ _ _ hw1)
    filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hw1)] with v hv
    exact discExt_of_ne _ _ _ hv

include hΨi in
theorem differentiableOn_discExt (hCo : IsOpen C) :
    DifferentiableOn ℂ (discExt Ψ (closure (cayley '' C) \ {q}) q) (ball 0 1) := by
  have hinvd : DifferentiableOn ℂ (invFunOn f C) H := (isConformalBijection_invFunOn hCo hf).1
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have hw1 : w ≠ 1 := WangWu.ne_one_of_mem_ball hw
  have hwH : cayleyInv w ∈ H := QuantumZipper.CA.cayleyInv_mem_H hw
  have hz := (discExt_eq_cayley hCH hf hqC hΨc hΨi hΨH hΨinf hΨf hw).1
  have hd : DifferentiableAt ℂ (fun v => cayley (invFunOn f C (cayleyInv v))) w := by
    refine (QuantumZipper.CA.differentiableAt_cayley ?_).comp w
      ((hinvd.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hwH)).comp w
        (QuantumZipper.CA.differentiableAt_cayleyInv hw1))
    exact QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (mem_Hbar_of_mem_H (hCH hz))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hw] with v hv
  exact (discExt_eq_cayley hCH hf hqC hΨc hΨi hΨH hΨinf hΨf hv).2

end DiscExt

/-! ### The orientation of the pocket chart -/

open Lemma71K (IsMarkedPocket wallPt)
open WangWu (IsDiscCrosscut crossSide crossRange semiArc)
open _root_.InteractingSLE.Orientation

theorem im_circleMap_one (θ : ℝ) : (circleMap 0 1 θ).im = Real.sin θ := by
  simp [circleMap, exp_ofReal_mul_I_im]

theorem norm_circleMap_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  rw [norm_circleMap_zero, abs_one]

/-- **The core: orientation of a two-point chart of a pocket on the left of a wall.** In the disc picture let `α` be
a path from `−1` to `1` (continuous and injective on `[0, 1]`; it may touch the circle), and let `C ⊆ ℍ` be an open
preconnected set whose Cayley image `U` avoids `α` and meets the closure of `α` exactly along `α([a, b])`. Let
`f = Ψ ∘ cayley : C → ℍ` be a conformal bijection with a boundary map `Ψ` (continuous and injective on
`cl U \ {α b}`, `ℍ̄`-valued, `Ψ (α a) = 0`, `|Ψ| → ∞` at `α b`). Suppose that `U` is on the **left** of `α` (the
reference loop `crossLoop α` winds once about `U`), and that some point `p` of the open arc `α((a, b))` off the upper
semicircle is reached from infinity without crossing `cl U`, `α` or the upper semicircle (the **right** of `α`). Then
`Ψ` sends the open arc `α((a, b))` to the positive half-line. -/
theorem re_pos_of_crossLoop {α : ℝ → ℂ} (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hα0 : α 0 = -1) (hα1 : α 1 = 1) {C : Set ℂ} (hCo : IsOpen C) (hCpc : IsPreconnected C) (hCH : C ⊆ H)
    (hCα : ∀ x ∈ C, cayley x ∉ α '' Icc 0 1) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hI : {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure (cayley '' C)} = Icc a b) {f Ψ : ℂ → ℂ}
    (hf : IsConformalBijection f C H) (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {α b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {α b})) (hΨH : MapsTo Ψ (closure (cayley '' C) \ {α b}) Hbar)
    (hΨ0 : Ψ (α a) = 0) (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {α b}] (α b)) atTop)
    (hΨf : ∀ x ∈ C, f x = Ψ (cayley x)) (hleft : ∀ z ∈ cayley '' C, windNum (crossLoop α) z = 1)
    (hright : ∃ p ∈ α '' Ioo a b, p ∉ semiArc 1 ∧ ∃ V : Set ℂ, IsPreconnected V ∧ ¬ Bornology.IsBounded V ∧
      p ∈ closure V ∧ Disjoint V (closure (cayley '' C) ∪ α '' Icc 0 1 ∪ semiArc 1)) :
    ∀ s ∈ Ioo a b, 0 < (Ψ (α s)).re := by
  set q := α b with hq
  set U := cayley '' C with hU
  set E := closure U \ {q} with hE
  have hqC : ∀ x ∈ C, cayley x ≠ q := fun x hx h =>
    hCα x hx ⟨b, ⟨ha0.trans hab.le, hb1⟩, h.symm⟩
  have hUpc : IsPreconnected U := hCpc.image _ fun z hz =>
    (WangWu.continuousAt_cayley_of_mem_Hbar (mem_Hbar_of_mem_H (hCH hz))).continuousWithinAt
  have hIcc : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 hb1
  have hcl : ∀ s ∈ Icc a b, α s ∈ closure U := fun s hs => by
    have hmem : s ∈ {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure U} := by rw [hI]; exact hs
    exact hmem.2
  have hwE : ∀ s ∈ Ico a b, α s ∈ E := fun s hs =>
    ⟨hcl s (Ico_subset_Icc_self hs), fun hsq => hs.2.ne
      (hαi (hIcc (Ico_subset_Icc_self hs)) (hIcc (right_mem_Icc.2 hab.le)) hsq)⟩
  have hreal : ∀ s ∈ Ico a b, (Ψ (α s)).im = 0 := fun s hs => by
    have h0 : 0 ≤ (Ψ (α s)).im := hΨH (hwE s hs)
    refine le_antisymm (not_lt.1 fun hpos => ?_) h0
    obtain ⟨z, hz, hzw⟩ := hf.2.surjOn (show Ψ (α s) ∈ H from hpos)
    have hzE : cayley z ∈ E := ⟨subset_closure ⟨z, hz, rfl⟩, hqC z hz⟩
    have h1 : α s = cayley z := hΨi (hwE s hs) hzE (by rw [← hΨf z hz, hzw])
    exact hCα z hz ⟨s, hIcc (Ico_subset_Icc_self hs), h1⟩
  have hUA : ∀ z ∈ U, z ∉ α '' Icc a b := fun z ⟨x, hx, hxz⟩ hzA => hCα x hx (hxz ▸ image_mono hIcc hzA)
  -- the boundary values on the open arc are real, nonzero and continuous
  have hΨne : ∀ s ∈ Ioo a b, Ψ (α s) ≠ 0 := fun s hs h => by
    have := hΨi (hwE s (Ioo_subset_Ico_self hs)) (hwE a ⟨le_rfl, hab⟩) (by rw [h, hΨ0])
    exact hs.1.ne' (hαi (hIcc (Ioo_subset_Icc_self hs)) (hIcc (left_mem_Icc.2 hab.le)) this)
  have hφc : ContinuousOn (fun s => (Ψ (α s)).re) (Ico a b) :=
    Complex.continuous_re.comp_continuousOn (hΨc.comp (hαc.mono (Ico_subset_Icc_self.trans hIcc)) hwE)
  have hre0 : ∀ s ∈ Ioo a b, (Ψ (α s)).re ≠ 0 := fun s hs h0 =>
    hΨne s hs (Complex.ext (by rw [h0]; rfl) (by rw [hreal s (Ioo_subset_Ico_self hs)]; rfl))
  intro s₀ hs₀
  by_contra hneg
  -- **the wrong orientation** along the whole open arc
  have hwrong : ∀ s ∈ Ioo a b, (Ψ (α s)).re < 0 := by
    have hs₀neg : (Ψ (α s₀)).re < 0 := lt_of_le_of_ne (not_lt.1 hneg) (hre0 s₀ hs₀)
    intro s hs
    refine lt_of_not_ge fun hpos => ?_
    have hpos' : 0 < (Ψ (α s)).re := lt_of_le_of_ne hpos (hre0 s hs).symm
    obtain ⟨u, hu, hu0⟩ := isPreconnected_Ioo.intermediate_value hs₀ hs (hφc.mono Ioo_subset_Ico_self)
      ⟨hs₀neg.le, hpos'.le⟩
    exact hre0 u hu hu0
  -- then the negative half-line is covered by the open arc
  have hcover : ∀ x : ℝ, x < 0 → ∃ s ∈ Ioo a b, Ψ (α s) = x := by
    intro x hx
    have hbI : b ∈ Icc (0 : ℝ) 1 := hIcc (right_mem_Icc.2 hab.le)
    have hlimq : Tendsto (fun s => α s) (𝓝[Ioo a b] b) (𝓝[E] q) :=
      tendsto_nhdsWithin_iff.2 ⟨((hαc b hbI).tendsto).mono_left
        (nhdsWithin_mono b (Ioo_subset_Icc_self.trans hIcc)),
        eventually_nhdsWithin_of_forall fun s hs => hwE s (Ioo_subset_Ico_self hs)⟩
    have htend : Tendsto (fun s => ‖Ψ (α s)‖) (𝓝[Ioo a b] b) atTop := hΨinf.comp hlimq
    have := right_nhdsWithin_Ioo_neBot hab
    obtain ⟨s₁, hs₁x, hs₁I⟩ := ((htend.eventually_gt_atTop (-x)).and self_mem_nhdsWithin).exists
    have hn : ‖Ψ (α s₁)‖ = -(Ψ (α s₁)).re := by
      have e : Ψ (α s₁) = ((Ψ (α s₁)).re : ℂ) :=
        Complex.ext (by simp) (by simp [hreal s₁ (Ioo_subset_Ico_self hs₁I)])
      conv_lhs => rw [e]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (hwrong s₁ hs₁I)]
    obtain ⟨s, hs, hsx⟩ := intermediate_value_Icc' hs₁I.1.le
      (hφc.mono (Icc_subset_Ico_right hs₁I.2))
      ⟨show (Ψ (α s₁)).re ≤ x by linarith, show x ≤ (Ψ (α a)).re by rw [hΨ0, zero_re]; exact hx.le⟩
    beta_reduce at hsx
    have hsa : s ≠ a := fun h => by rw [h, hΨ0, zero_re] at hsx; linarith
    have hsI : s ∈ Ico a b := ⟨hs.1, hs.2.trans_lt hs₁I.2⟩
    exact ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), hsI.2⟩,
      Complex.ext (by rw [hsx, ofReal_re]) (by rw [hreal s hsI, ofReal_im])⟩
  -- the disc extension `g` of the inverse chart and its boundary loop `J`
  have hspec := fun {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) (hw1 : w ≠ 1) =>
    discExt_spec hCH hf hqC hΨc hΨH hΨinf hΨf hw hw1
  have hgc := continuousOn_discExt hCH hf hqC hΨc hΨi hΨH hΨinf hΨf
  have hgi := injOn_discExt hCH hf hqC hΨc hΨH hΨinf hΨf
  have hgd := differentiableOn_discExt hCH hf hqC hΨc hΨi hΨH hΨinf hΨf hCo
  set g := discExt Ψ E q with hgdef
  set J : ℝ → ℂ := fun t => g (circleMap 0 1 (2 * π * t)) with hJdef
  have hcm : ∀ t : ℝ, circleMap 0 1 (2 * π * t) ∈ closedBall (0 : ℂ) 1 := fun t =>
    mem_closedBall_zero_iff.2 (norm_circleMap_one _).le
  have hJc : ContinuousOn J (Icc 0 1) :=
    (hgc.comp_continuous (by unfold circleMap; fun_prop) hcm).continuousOn
  have hJl : J 0 = J 1 := by simp only [hJdef, Orientation.circleMap_two_pi_one]
  have hJ0 : J 0 = α b := by
    have hc0 : circleMap 0 1 (2 * π * 0) = 1 := by simp [circleMap]
    change g (circleMap 0 1 (2 * π * 0)) = _
    rw [hc0, hgdef, discExt_one]
  have hEa : α a ∈ E := hwE a ⟨le_rfl, hab⟩
  have hJ_eq : ∀ t : ℝ, circleMap 0 1 (2 * π * t) ≠ 1 → ∀ s ∈ Ico a b,
      cayleyInv (circleMap 0 1 (2 * π * t)) = Ψ (α s) → J t = α s := fun t ht1 s hs he =>
    hΨi (hspec (hcm t) ht1).1 (hwE s hs) (by rw [(hspec (hcm t) ht1).2, he])
  have hJh : J (1 / 2) = α a := by
    have hm1 : circleMap 0 1 (2 * π * (1 / 2)) = -1 := by
      rw [show 2 * π * (1 / 2) = π by ring]; simp [circleMap, exp_pi_mul_I]
    refine hJ_eq _ (by rw [hm1]; norm_num) a ⟨le_rfl, hab⟩ ?_
    rw [hm1, cayleyInv_neg_one, hΨ0]
  have hJcl : J '' Icc 0 1 ⊆ closure U := by
    rintro _ ⟨t, -, rfl⟩
    rcases discExt_mem_closure hCH hf hqC hΨc hΨH hΨinf hΨf (hcm t) with h | h
    · exact h
    · change g _ ∈ _
      rw [h, hgdef, discExt_one]
      exact hcl b (right_mem_Icc.2 hab.le)
  have hJU : Disjoint U (J '' Icc 0 1) := Set.disjoint_right.2 fun _ ⟨t, _, ht⟩ =>
    ht ▸ discExt_notMem_image hCH hf hqC hΨc hΨH hΨinf hΨf (norm_circleMap_one _)
  -- `J` runs along the right-wall arc on `[0, 1/2]` and avoids its interior on `[1/2, 1]`
  have hJA : MapsTo J (Icc 0 (1 / 2)) (α '' Icc a b) := fun t ht => by
    by_cases ht1 : circleMap 0 1 (2 * π * t) = 1
    · refine ⟨b, right_mem_Icc.2 hab.le, ?_⟩
      change α b = g _
      rw [ht1, hgdef, discExt_one]
    have him : 0 ≤ (circleMap 0 1 (2 * π * t)).im := by
      rw [im_circleMap_one]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, ht.1]) (by nlinarith [Real.pi_pos, ht.2])
    obtain ⟨x, hx0, hxw⟩ := cayleyInv_nonpos (norm_circleMap_one _) ht1 him
    rcases eq_or_lt_of_le hx0 with hx | hx
    · exact ⟨a, left_mem_Icc.2 hab.le, (hJ_eq t ht1 a ⟨le_rfl, hab⟩ (by rw [hxw, hx, hΨ0]; simp)).symm⟩
    · obtain ⟨s, hs, hsx⟩ := hcover x hx
      exact ⟨s, Ioo_subset_Icc_self hs, (hJ_eq t ht1 s (Ioo_subset_Ico_self hs) (by rw [hxw, hsx])).symm⟩
  have hJB : ∀ t ∈ Icc (1 / 2 : ℝ) 1, J t ∉ α '' Ioo a b := by
    rintro t ht ⟨s, hs, hst⟩
    by_cases ht1 : circleMap 0 1 (2 * π * t) = 1
    · have hb : J t = α b := by change g _ = _; rw [ht1, hgdef, discExt_one]
      rw [hb] at hst
      exact hs.2.ne (hαi (hIcc (Ioo_subset_Icc_self hs)) (hIcc (right_mem_Icc.2 hab.le)) hst)
    have him : (circleMap 0 1 (2 * π * t)).im ≤ 0 := by
      rw [im_circleMap_one]
      have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * π * t - π) (by nlinarith [Real.pi_pos, ht.1])
        (by nlinarith [Real.pi_pos, ht.2])
      rw [Real.sin_sub_pi] at h
      linarith
    obtain ⟨x, hx0, hxw⟩ := cayleyInv_nonneg (norm_circleMap_one _) ht1 him
    have h1 := (hspec (hcm t) ht1).2
    change Ψ (J t) = _ at h1
    rw [← hst, hxw] at h1
    have h2 := hwrong s hs
    rw [h1, ofReal_re] at h2
    linarith
  -- **`J` winds once about the pocket**
  have hJw : ∀ z ∈ U, windNum J z = 1 := fun z hz => by
    have h0 : g 0 ∈ U := discExt_mem_image hCH hf hqC hΨc hΨi hΨH hΨinf hΨf (mem_ball_self one_pos)
    rw [windNum_eq_of_isPreconnected hJc hJl hUpc hJU hz h0]
    exact windNum_comp_circleMap_one_eq_one hgc hgd hgi (mem_ball_self one_pos)
  -- the crossing at a point `p` of the open right-wall arc
  obtain ⟨p, ⟨sm, hsmI, rfl⟩, hpS, V, hVpc, hVu, hpV, hVd⟩ := hright
  have hpI : α sm ∈ α '' Ioo a b := ⟨sm, hsmI, rfl⟩
  have hinj : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → α t = α sm → t = sm := fun ht he =>
    hαi ht (hIcc (Ioo_subset_Icc_self hsmI)) he
  have hΛ := continuousOn_crossLoop hαc hα1
  have hΛl := crossLoop_loop hα0 hα1
  have hpnot : α sm ∉ J '' Icc 0 0 ∪ J '' Icc (1 / 2) 1 ∪ crossLoop α '' Icc 0 (a / 2) ∪
      crossLoop α '' Icc (b / 2) 1 := by
    rintro (((⟨t, ht, he⟩ | ⟨t, ht, he⟩) | ⟨t, ht, he⟩) | ⟨t, ht, he⟩)
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, hJ0] at he
      have := hinj (hIcc (right_mem_Icc.2 hab.le)) he
      linarith [hsmI.2]
    · exact hJB t ht (he ▸ hpI)
    · rw [crossLoop_of_le (by linarith [ht.2])] at he
      have := hinj ⟨by linarith [ht.1], by linarith [ht.2]⟩ he
      linarith [ht.2, hsmI.1]
    · rcases le_total t (1 / 2) with h | h
      · rw [crossLoop_of_le h] at he
        have := hinj ⟨by linarith [ht.1], by linarith⟩ he
        linarith [ht.1, hsmI.2]
      · exact hpS (he ▸ crossLoop_mem_semiArc hα1 ⟨h, ht.2⟩)
  obtain ⟨ε, hε, hcross⟩ := windNum_add_windNum_eq hJc hΛ hJl hΛl (A := α '' Icc a b)
    (fun w hw => hasLogOn_sub_image_Icc hab (hαc.mono hIcc) (hαi.mono hIcc) hw) le_rfl (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) hJA
    (fun t ht => by
      rw [crossLoop_of_le (by linarith [ht.2])]
      exact ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩)
    (by rw [hJ0, crossLoop_of_le (by linarith), show 2 * (b / 2) = b by ring])
    (by rw [hJh, crossLoop_of_le (by linarith), show 2 * (a / 2) = a by ring]) hpnot
  -- a point of the pocket and a point on the right of the wall, both near `p`
  obtain ⟨z, hzU, hzp⟩ := Metric.mem_closure_iff.1 (hcl sm (Ioo_subset_Icc_self hsmI)) ε hε
  obtain ⟨z', hz'V, hz'p⟩ := Metric.mem_closure_iff.1 hpV ε hε
  have hz'A : z' ∉ α '' Icc a b := fun h =>
    Set.disjoint_left.1 hVd hz'V (Or.inl (Or.inr (image_mono hIcc h)))
  have key := hcross z (by rw [mem_ball, dist_comm]; exact hzp) z' (by rw [mem_ball, dist_comm]; exact hz'p)
    (hUA z hzU) hz'A
  have hJz' : windNum J z' = 0 := windNum_eq_zero_of_isPreconnected hJc hJl hVpc hVu
    (Set.disjoint_left.2 fun v hv hvJ => Set.disjoint_left.1 hVd hv (Or.inl (Or.inl (hJcl hvJ)))) hz'V
  have hΛz' : windNum (crossLoop α) z' = 0 := windNum_eq_zero_of_isPreconnected hΛ hΛl hVpc hVu
    (Set.disjoint_left.2 fun v hv hvΛ => by
      rcases image_crossLoop_subset hα1 hvΛ with h | h
      · exact Set.disjoint_left.1 hVd hv (Or.inl (Or.inr h))
      · exact Set.disjoint_left.1 hVd hv (Or.inr h)) hz'V
  rw [hJw z hzU, hleft z hzU, hJz', hΛz'] at key
  norm_num at key

/-- For a disc crosscut `α`, the component of `−i` outside `α ∪ (upper semicircle)`: preconnected, unbounded, it
contains the lower side, and it avoids the closed upper side. -/
theorem crossSide_neg_props {α : ℝ → ℂ} (hα : IsDiscCrosscut α) :
    IsPreconnected (connectedComponentIn (crossRange α ∪ semiArc 1)ᶜ (-I)) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (crossRange α ∪ semiArc 1)ᶜ (-I)) ∧
      crossSide α (-1) ⊆ connectedComponentIn (crossRange α ∪ semiArc 1)ᶜ (-I) ∧
      Disjoint (connectedComponentIn (crossRange α ∪ semiArc 1)ᶜ (-I))
        (closure (crossSide α 1) ∪ crossRange α ∪ semiArc 1) := by
  set Γ := crossRange α ∪ semiArc 1 with hΓ
  set V := connectedComponentIn Γᶜ (-I) with hV
  have hout := hα.neg_I_mem_jordanOut_upper
  have hS := hα.isPreconnected_crossSide (Or.inr rfl)
  have hIcl : -I ∈ closure (crossSide α (-1)) :=
    hα.semiArc_subset_closure_crossSide (Or.inr rfl) ⟨by simp, by simp⟩
  have hSΓ : crossSide α (-1) ⊆ Γᶜ := fun w hw hwΓ => by
    have hwb := hα.crossSide_subset (Or.inr rfl) hw
    rcases hwΓ with h | h
    · exact hwb.2 h
    · have := hwb.1; rw [mem_ball, dist_zero_right, h.1] at this; exact lt_irrefl _ this
  have hins : IsPreconnected (insert (-I) (crossSide α (-1))) :=
    hS.subset_closure (subset_insert _ _) (insert_subset hIcl subset_closure)
  have hsub : crossSide α (-1) ⊆ V := fun w hw =>
    hins.subset_connectedComponentIn (mem_insert _ _) (insert_subset hout.1 hSΓ) (mem_insert_of_mem _ hw)
  refine ⟨isPreconnected_connectedComponentIn, hout.2, hsub, Set.disjoint_left.2 fun v hv hvc => ?_⟩
  have hvΓ : v ∈ Γᶜ := connectedComponentIn_subset _ _ hv
  have hvU : ¬ Bornology.IsBounded (connectedComponentIn Γᶜ v) := by
    rw [← connectedComponentIn_eq hv]; exact hout.2
  have hvc' : v ∈ closure (crossSide α 1) ∨ v ∈ Γ := by
    rcases hvc with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hvc' with h | h
  · rw [hα.closure_crossSide (Or.inl rfl)] at h
    rcases h with h | h
    · exact hvU h.2
    · exact hvΓ h
  · exact hvΓ h

/-- **The two-point pocket chart preserves orientation** (`PocketChartOrientationStatement`, supplement §2.3, p. 453):
the boundary map of a conformal bijection `f : C → ℍ` of a marked pocket, normalized by `x₀ ↦ 0` and `y₀ ↦ ∞`, sends
the open right-wall arc to the positive half-line. The core `re_pos_of_crossLoop`, with the right wall a crosscut:
the pocket lies in its upper side (`WangWu.pocket_subset_between`), and the lower side is reached from infinity
through `−i`. -/
theorem pocketChartOrientationStatement : PocketChartOrientationStatement := by
  intro R L hR hL hLR C hC a b hM f Ψ hf hΨc hΨi hΨH hΨ0 hΨinf hΨf
  have hα : IsDiscCrosscut (wallPt R) := (Lemma71I.IsSimpleProper.isProperArc hR).isDiscCrosscut_toDisc
  have hCsub := subset_of_mem_betweenComponents hC
  have hCH : C ⊆ H := fun z hz => (hCsub hz).1
  have hRim : ∀ t, 0 ≤ (R t).im := hR.isProperCurve.2.2.1
  have hRc : IsClosed (range R) :=
    Lemma71I.arcRange_realPath R ▸ (Lemma71I.IsSimpleProper.isProperArc hR).isClosed_arcRange
  have hLc : IsClosed (range L) :=
    Lemma71I.arcRange_realPath L ▸ (Lemma71I.IsSimpleProper.isProperArc hL).isClosed_arcRange
  obtain ⟨z₀, -, -, -, hCz⟩ := id hC
  have hCo : IsOpen C := hCz ▸ (QuantumZipper.isOpen_H.sdiff (hRc.union hLc)).connectedComponentIn
  have hCpc : IsPreconnected C := hCz ▸ isPreconnected_connectedComponentIn
  have hCα : ∀ x ∈ C, cayley x ∉ wallPt R '' Icc 0 1 := fun x hx ⟨s, _, hs⟩ =>
    (hCsub hx).2 (Or.inl (mem_range_of_cayley_eq_toDisc hRim (mem_Hbar_of_mem_H (hCH hx)) hs.symm))
  -- the pocket lies on the left of the right wall
  have hU1 : cayley '' C ⊆ crossSide (wallPt R) 1 := by
    have hC' := hC
    rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hC'
    have hord := Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hR.isProperCurve hR.2.2.1 hLR
    rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hord
    obtain ⟨a₁, b₁, hg, hCU⟩ := WangWu.exists_contactGap_of_mem_betweenComponents
      (Lemma71I.IsSimpleProper.isProperArc hR) (Lemma71I.IsSimpleProper.isProperArc hL) hord hC'
    have hord' := (WangWu.disjoint_rightSideOf_iff (Lemma71I.IsSimpleProper.isProperArc hR)
      (Lemma71I.IsSimpleProper.isProperArc hL)).1 hord
    have hsub := WangWu.pocket_subset_between hα
      (Lemma71I.IsSimpleProper.isProperArc hL).isDiscCrosscut_toDisc hord' hg
    rw [hCU]
    exact fun z hz => (hsub hz).1
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := hM
  obtain ⟨hVpc, hVu, hVsub, hVd⟩ := crossSide_neg_props hα
  refine re_pos_of_crossLoop hα.cont hα.inj hα.zero hα.one hCo hCpc hCH hCα ha0 hab hb1 hI hf hΨc hΨi hΨH hΨ0
    hΨinf hΨf (fun z hz => windNum_crossLoop_of_mem_crossSide_one hα (hU1 hz)) ?_
  -- the right of the wall near the midpoint of the arc
  set sm := (a + b) / 2 with hsm
  have hsmI : sm ∈ Ioo a b := ⟨by rw [hsm]; linarith, by rw [hsm]; linarith⟩
  have hsm01 : sm ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hsmI.1], by linarith [hsmI.2]⟩
  refine ⟨wallPt R sm, ⟨sm, hsmI, rfl⟩, fun h => ?_, _, hVpc, hVu,
    closure_mono hVsub (hα.crossRange_subset_closure_crossSide (Or.inr rfl) ⟨sm, Ioo_subset_Icc_self hsm01, rfl⟩),
    ?_⟩
  · have h2 := hα.mem_disc sm hsm01
    rw [mem_ball, dist_zero_right, h.1] at h2
    exact lt_irrefl _ h2
  · refine Set.disjoint_left.2 fun v hv hvc => Set.disjoint_left.1 hVd hv ?_
    rcases hvc with (h | h) | h
    · exact Or.inl (Or.inl (closure_mono hU1 h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-! ### Proposition 7.4's order statement without the orientation input -/

/-- PROVE-PROP74B's `lemma71TwoMiddleStatement_of_fixedChart` with its orientation input discharged
(`pocketChartOrientationStatement`). -/
theorem lemma71TwoMiddleStatement_of_fixedChart_oriented (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hfc : Lemma71FixedChartStatement.{u}) :
    Prop74Pocket.Lemma71TwoMiddleStatement.{u} :=
  lemma71TwoMiddleStatement_of_fixedChart href h55 hfc pocketChartOrientationStatement

/-- PROVE-PROP74B's `prop74OrderStatement_of_fixedChart` with its orientation input discharged. -/
theorem prop74OrderStatement_of_fixedChart_oriented (h75 : Theorem15.Lemma75Statement.{u})
    (href : Lemma71H.Cond44ReferenceStatement.{u}) (h55 : Lemma71H.Prop55HalfPlaneStatement.{u})
    (hfc : Lemma71FixedChartStatement.{u}) : Prop74OrderStatement.{u} :=
  prop74OrderStatement_of_fixedChart h75 href h55 hfc pocketChartOrientationStatement

end InteractingSLE.Sec7.Prop74B
