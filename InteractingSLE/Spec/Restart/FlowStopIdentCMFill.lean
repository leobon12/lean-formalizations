/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFilling

/-!
# Where the hulls of a stopped flow line live: the filling in `ℂ`

Packet PROVE-L1-CM. The Cameron–Martin identification of (L1) for a shift pair (`FlowStopIdentCM`) tilts the law of
the field by a density built from a source supported off an open set `N` (the shift `T` vanishes on `N`). The
conditional law of the field off a hull `K_τ`, which the frozen coupling gives, determines the tilt only when the
source misses `K_τ`, i.e. when `K_τ ⊆ N` (Lemma G3's proof, p. 493: "`f = v` on `U` and on a neighborhood of its
closure"; Aux. lemma 61). The hull of a trace staying in a compact `L ⊆ ℍ̄` is in general **not** in `L`: it also
contains the regions the trace encloses, together with the real line. This file locates it:

* `fillC L`: `L` together with the bounded components of `ℂ ∖ L`;
* `isCompact_fillC`: the filling of a compact set is compact;
* `mem_of_mem_fillC_of_im_eq_zero`: for closed `L ⊆ ℍ̄`, the real points of `fillC L` are those of `L` (a real point
  off `L` is joined to the lower half-plane);
* **`subset_fillC_of_isFilling`**: if `K` fills a compact `A ⊆ L` (`IsFilling K A`, the frozen relation between a
  hull and its trace) and `L` contains every real point between two real points of `A`, then `K ∩ ℍ ⊆ fillC L`.

So for a stopped trace in `closure V ∩ ℍ̄` whose real points lie in a closed interval `J`, every hull lies in the
compact `fillC ((closure V ∩ ℍ̄) ∪ J)`, whose real points are those of `closure V ∪ J`; the shift of
`RLC.exists_shift_isGFFWithBoundaryData` must be built for this compact set (not for `closure V`), and this is possible
when `J ⊆ O`. When the trace touches `ℝ` at two points with a point off `O` between them (for instance in two different
components of `O`), no admissible compact set contains the hull: the swallowed region meets `ℝ ∖ O`, where the two
boundary data differ.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology Filter Topology
open QuantumZipper (H)

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCM

/-- **The filling of `L` in `ℂ`**: `L` together with the bounded components of its complement. -/
def fillC (L : Set ℂ) : Set ℂ := {z | z ∈ L ∨ IsBounded (connectedComponentIn Lᶜ z)}

theorem subset_fillC (L : Set ℂ) : L ⊆ fillC L := fun _ hz => Or.inl hz

/-- A point joined to infinity off `L` by a preconnected set is not in the filling. -/
theorem notMem_fillC_of_isPreconnected {L S : Set ℂ} {z : ℂ} (hzS : z ∈ S) (hS : IsPreconnected S)
    (hSL : S ⊆ Lᶜ) (hSb : ¬ IsBounded S) : z ∉ fillC L := by
  rintro (hz | hb)
  · exact hSL hzS hz
  · exact hSb (hb.subset (hS.subset_connectedComponentIn hzS hSL))

/-- The radial ray `{t z : t ≥ 1}` of a nonzero `z` is unbounded. -/
theorem not_isBounded_ray {z : ℂ} (hz : z ≠ 0) : ¬ IsBounded ((fun t : ℝ => (t : ℂ) * z) '' Ici 1) := by
  intro hb
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨1, mem_Ici.2 le_rfl, rfl⟩)
  have h1 : (1 : ℝ) ≤ M / ‖z‖ + 1 := by
    have : 0 ≤ M / ‖z‖ := by positivity
    linarith
  have := hM _ ⟨M / ‖z‖ + 1, h1, rfl⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
    div_mul_cancel₀ _ hz0.ne'] at this
  linarith

/-- The filling of a set in a closed ball stays in the ball. -/
theorem fillC_subset_closedBall {L : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (hLR : L ⊆ closedBall 0 R) :
    fillC L ⊆ closedBall 0 R := by
  intro z hz
  by_contra hzR
  rw [mem_closedBall, dist_zero_right, not_le] at hzR
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hzR; linarith
  refine notMem_fillC_of_isPreconnected (S := (fun t : ℝ => (t : ℂ) * z) '' Ici 1)
    ⟨1, mem_Ici.2 le_rfl, by simp⟩ (isPreconnected_Ici.image _ (by fun_prop)) ?_ (not_isBounded_ray hz0) hz
  rintro _ ⟨t, ht, rfl⟩ hL
  have ht1 : (1 : ℝ) ≤ t := ht
  have hn := hLR hL
  rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)] at hn
  nlinarith [norm_nonneg z]

/-- The filling of a closed set is closed: off the filling, the (open, unbounded) component is a neighbourhood. -/
theorem isClosed_fillC {L : Set ℂ} (hL : IsClosed L) : IsClosed (fillC L) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hzL, hzb⟩ := not_or.1 hz
  have hC : IsOpen (connectedComponentIn Lᶜ z) := hL.isOpen_compl.connectedComponentIn
  refine Filter.mem_of_superset (hC.mem_nhds (mem_connectedComponentIn hzL)) fun w hw => ?_
  have hwL : w ∉ L := connectedComponentIn_subset _ _ hw
  refine fun h => h.elim hwL fun hb => hzb ?_
  rwa [connectedComponentIn_eq hw]

/-- **The filling of a compact set is compact.** -/
theorem isCompact_fillC {L : Set ℂ} (hL : IsCompact L) : IsCompact (fillC L) := by
  obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
  have hR' : L ⊆ closedBall 0 (max R 0) := hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  exact isCompact_of_isClosed_isBounded (isClosed_fillC hL.isClosed)
    (isBounded_closedBall.subset (fillC_subset_closedBall (le_max_right _ _) hR'))

/-- The open lower half-plane is preconnected. -/
theorem isPreconnected_lowerOpen : IsPreconnected {w : ℂ | w.im < 0} :=
  (convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).isPreconnected

/-- The open lower half-plane is unbounded. -/
theorem not_isBounded_lowerOpen : ¬ IsBounded {w : ℂ | w.im < 0} := by
  intro hb
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (-Complex.I) (by simp))
  have h := hM (-((M + 1 : ℝ) : ℂ) * Complex.I) (by simp; linarith)
  rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos (by linarith)] at h
  linarith

/-- **The real points of the filling of a closed `L ⊆ ℍ̄` are those of `L`**: a real point off `L` has a disc off
`L`, which meets the lower half-plane, an unbounded preconnected set off `L`. -/
theorem mem_of_mem_fillC_of_im_eq_zero {L : Set ℂ} (hL : IsClosed L) (hLH : ∀ w ∈ L, 0 ≤ w.im) {z : ℂ}
    (hz : z ∈ fillC L) (h0 : z.im = 0) : z ∈ L := by
  by_contra hzL
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hL.isOpen_compl z hzL
  have hp : z - ((r / 2 : ℝ) : ℂ) * Complex.I ∈ ball z r ∩ {w : ℂ | w.im < 0} := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
        mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · simp only [mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, h0]
      linarith
  refine notMem_fillC_of_isPreconnected (S := ball z r ∪ {w : ℂ | w.im < 0}) (Or.inl (mem_ball_self hr))
    ((convex_ball z r).isPreconnected.union _ hp.1 hp.2 isPreconnected_lowerOpen) ?_
    (fun hb => not_isBounded_lowerOpen (hb.subset subset_union_right)) hz
  rintro w (hw | hw)
  · exact hball hw
  · exact fun hwL => absurd (hLH w hwL) (not_le.2 hw)

/-! ### Components of `ℍ ∖ A` -/

/-- The components of `ℍ ∖ A` are open. -/
theorem isOpen_connectedComponentIn_H {A : Set ℂ} (hA : IsClosed A) (z : ℂ) :
    IsOpen (connectedComponentIn (H \ A) z) :=
  (QuantumZipper.isOpen_H.sdiff hA).connectedComponentIn

/-- A preconnected set in `ℍ ∖ A` meeting the component of `z` lies in it. -/
theorem subset_connectedComponentIn_of_meets {A S : Set ℂ} {z c : ℂ} (hS : IsPreconnected S) (hSA : S ⊆ H \ A)
    (hc : c ∈ S) (hcz : c ∈ connectedComponentIn (H \ A) z) : S ⊆ connectedComponentIn (H \ A) z := by
  rw [connectedComponentIn_eq hcz]
  exact hS.subset_connectedComponentIn hc hSA

/-- **Two unbounded components of `ℍ ∖ A` coincide** (`A` bounded): each contains a point `w ∈ ℍ` with `‖w‖ > R`, the
vertical ray above `w` and the half-plane `{Im > R}`. -/
theorem connectedComponentIn_eq_of_not_isBounded {A : Set ℂ} {R : ℝ} (hR : 0 ≤ R) (hAR : A ⊆ closedBall 0 R)
    {z₁ z₂ : ℂ} (h₁ : ¬ IsBounded (connectedComponentIn (H \ A) z₁))
    (h₂ : ¬ IsBounded (connectedComponentIn (H \ A) z₂)) :
    connectedComponentIn (H \ A) z₁ = connectedComponentIn (H \ A) z₂ := by
  -- the half-plane above height `R`
  set E : Set ℂ := {w | R < w.im} with hE
  have hEc : IsPreconnected E := (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear R).isPreconnected
  have hEA : E ⊆ H \ A := fun w hw => by
    have hw' : R < w.im := hw
    refine ⟨show 0 < w.im by linarith, fun hwA => ?_⟩
    have := hAR hwA
    rw [mem_closedBall, dist_zero_right] at this
    linarith [Complex.abs_im_le_norm w, le_abs_self w.im]
  have he : ((R + 1 : ℝ) : ℂ) * Complex.I ∈ E := by
    show R < (((R + 1 : ℝ) : ℂ) * Complex.I).im
    simp
  -- every unbounded component contains `E`
  have key : ∀ z, ¬ IsBounded (connectedComponentIn (H \ A) z) → E ⊆ connectedComponentIn (H \ A) z := by
    intro z hz
    obtain ⟨w, hwC, hwR⟩ : ∃ w ∈ connectedComponentIn (H \ A) z, R < ‖w‖ := by
      by_contra hcon
      push Not at hcon
      exact hz ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun w hw => by
        rw [mem_closedBall, dist_zero_right]; exact hcon w hw)
    have hwH : 0 < w.im := (connectedComponentIn_subset _ _ hwC).1
    -- the vertical ray above `w`, joined to `E`
    set S : Set ℂ := (fun t : ℝ => w + (t : ℂ) * Complex.I) '' Ici 0 with hS
    have hSc : IsPreconnected S := isPreconnected_Ici.image _ (by fun_prop)
    have hSA : S ⊆ H \ A := by
      rintro _ ⟨t, ht, rfl⟩
      have ht0 : (0 : ℝ) ≤ t := ht
      have him : (w + (t : ℂ) * Complex.I).im = w.im + t := by simp
      refine ⟨show 0 < (w + (t : ℂ) * Complex.I).im by rw [him]; linarith, fun hA => ?_⟩
      have hn := hAR hA
      rw [mem_closedBall, dist_zero_right] at hn
      have h1 : ‖w‖ ^ 2 ≤ ‖w + (t : ℂ) * Complex.I‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
          Complex.normSq_apply]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
          Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im]
        nlinarith
      nlinarith [norm_nonneg w, norm_nonneg (w + (t : ℂ) * Complex.I)]
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ R < w.im + t₀ := ⟨|R| + 1, by positivity, by
      linarith [le_abs_self R]⟩
    have hp : w + (t₀ : ℂ) * Complex.I ∈ S ∩ E := ⟨⟨t₀, ht₀.1, rfl⟩, by
      show R < (w + (t₀ : ℂ) * Complex.I).im
      simpa using ht₀.2⟩
    have hSE : IsPreconnected (S ∪ E) := hSc.union _ hp.1 hp.2 hEc
    have hsub := subset_connectedComponentIn_of_meets hSE (union_subset hSA hEA)
      (Or.inl ⟨0, mem_Ici.2 le_rfl, by simp⟩) hwC
    exact subset_union_right.trans hsub
  have e₁ := key z₁ h₁ he
  have e₂ := key z₂ h₂ he
  rw [connectedComponentIn_eq e₁, connectedComponentIn_eq e₂]

/-- **The strip beside a real point off a compact set.** If `x ∈ ℝ` is not in the compact `A`, and every real point
of `A` lies strictly on one side of `x` (`s = ±1` gives the side), then some half-disc above `x` lies in an unbounded
preconnected subset of `ℍ ∖ A`: a thin horizontal half-strip running away from `A` on the other side. -/
theorem exists_strip {A : Set ℂ} (hA : IsCompact A) {x : ℂ} (hx0 : x.im = 0) (hxA : x ∉ A) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hside : ∀ a ∈ A, a.im = 0 → s * (a.re - x.re) < 0) :
    ∃ ρ > 0, ∃ S : Set ℂ, ball x ρ ∩ H ⊆ S ∧ IsPreconnected S ∧ S ⊆ H \ A ∧ ¬ IsBounded S := by
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  -- the part of `A` on the far side and the real ray on that side are separated
  set A' : Set ℂ := A ∩ {w | 0 ≤ s * (w.re - x.re)} with hA'
  set T : Set ℂ := {w | w.im = 0 ∧ 0 ≤ s * (w.re - x.re)} with hT
  have hcont : Continuous fun w : ℂ => s * (w.re - x.re) := by fun_prop
  have hA'c : IsCompact A' := hA.inter_right (isClosed_le continuous_const hcont)
  have hTc : IsClosed T := (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const hcont)
  have hdisj : Disjoint A' T := by
    rw [Set.disjoint_left]
    rintro w ⟨hwA, hw⟩ ⟨hw0, -⟩
    exact absurd hw (not_le.2 (hside w hwA hw0))
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hA'c hTc
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 hA.isClosed.isOpen_compl x hxA
  set ε := min δ ρ₀ with hε
  have hε0 : 0 < ε := lt_min hδ hρ₀
  -- the half-strip
  set S₀ : Set ℂ := {w | 0 < s * (w.re - x.re)} ∩ ({w | 0 < w.im} ∩ {w | w.im < ε}) with hS₀
  have hlin : IsLinearMap ℝ fun w : ℂ => s * w.re :=
    ⟨fun a b => by simp [mul_add], fun c a => by simp; ring⟩
  have hS₀c : Convex ℝ S₀ := by
    refine Convex.inter ?_ (Convex.inter ?_ ?_)
    · have e : {w : ℂ | 0 < s * (w.re - x.re)} = {w | s * x.re < s * w.re} := by
        ext w
        show 0 < s * (w.re - x.re) ↔ s * x.re < s * w.re
        constructor <;> intro h' <;> linarith
      rw [e]
      exact convex_halfSpace_gt hlin (s * x.re)
    · exact convex_halfSpace_gt Complex.imLm.isLinear 0
    · exact convex_halfSpace_lt Complex.imLm.isLinear ε
  have hS₀A : S₀ ⊆ H \ A := by
    rintro w ⟨hw1, hw2, hw3⟩
    refine ⟨hw2, fun hwA => ?_⟩
    have hw1' : 0 < s * (w.re - x.re) := hw1
    have hwA' : w ∈ A' := ⟨hwA, show 0 ≤ s * (w.re - x.re) from le_of_lt hw1'⟩
    have hwT : (w.re : ℂ) ∈ T := ⟨by simp, by simpa using le_of_lt hw1⟩
    refine Set.disjoint_left.1 hδd (mem_thickening_iff.2 ⟨w, hwA', by rw [dist_self]; exact hδ⟩)
      (mem_thickening_iff.2 ⟨w.re, hwT, ?_⟩)
    rw [dist_eq_norm]
    have e : w - (w.re : ℂ) = (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hw2]
    exact hw3.trans_le (min_le_left _ _)
  -- the half-disc above `x`
  set B : Set ℂ := ball x ε ∩ {w | 0 < w.im} with hB
  have hBc : Convex ℝ B := (convex_ball x ε).inter (convex_halfSpace_gt Complex.imLm.isLinear 0)
  have hBA : B ⊆ H \ A := fun w hw =>
    ⟨hw.2, hball (ball_subset_ball (min_le_right _ _) hw.1)⟩
  -- a common point
  set p : ℂ := x + ((s * (ε / 4) : ℝ) : ℂ) + ((ε / 4 : ℝ) : ℂ) * Complex.I with hp
  have hpre : p.re - x.re = s * (ε / 4) := by simp [hp]
  have hpim : p.im = ε / 4 := by simp [hp, hx0]
  have hpS : p ∈ S₀ := by
    refine ⟨?_, ?_, ?_⟩
    · show 0 < s * (p.re - x.re)
      rw [hpre, ← mul_assoc, ← sq, show s ^ 2 = 1 by rcases hs with rfl | rfl <;> norm_num]
      positivity
    · show 0 < p.im
      rw [hpim]; positivity
    · show p.im < ε
      rw [hpim]; linarith
  have hpB : p ∈ B := by
    refine ⟨?_, show 0 < p.im by rw [hpim]; positivity⟩
    rw [mem_ball, dist_eq_norm]
    have e : p - x = ((s * (ε / 4) : ℝ) : ℂ) + ((ε / 4 : ℝ) : ℂ) * Complex.I := by rw [hp]; ring
    rw [e]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, hs1, one_mul, abs_of_pos (by positivity)]
    linarith
  refine ⟨ε, hε0, S₀ ∪ B, fun w hw => Or.inr ⟨hw.1, hw.2⟩,
    hS₀c.isPreconnected.union p hpS hpB hBc.isPreconnected, union_subset hS₀A hBA, fun hb => ?_⟩
  -- the half-strip is unbounded
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hb.subset subset_union_left)
  set t : ℝ := M + ‖x‖ + 1 with ht
  have ht0 : 0 < t := by have := norm_nonneg x; have : 0 ≤ M := (norm_nonneg _).trans (hM p hpS); linarith
  set q : ℂ := x + ((s * t : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I with hq
  have hqS : q ∈ S₀ := by
    have hqre : q.re - x.re = s * t := by simp [hq]
    have hqim : q.im = ε / 2 := by simp [hq, hx0]
    refine ⟨?_, ?_, ?_⟩
    · show 0 < s * (q.re - x.re)
      rw [hqre, ← mul_assoc, ← sq, show s ^ 2 = 1 by rcases hs with rfl | rfl <;> norm_num]
      linarith
    · show 0 < q.im
      rw [hqim]; positivity
    · show q.im < ε
      rw [hqim]; linarith
  have hqM := hM q hqS
  have hqre' : |q.re - x.re| = t := by
    have : q.re - x.re = s * t := by simp [hq]
    rw [this, abs_mul, hs1, one_mul, abs_of_pos ht0]
  have h1 : |q.re - x.re| ≤ ‖q‖ + ‖x‖ := by
    refine (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm q) (Complex.abs_re_le_norm x))
  linarith

/-! ### The hull of a trace lies in the filling -/

/-- **The hull of a trace lies in the filling of any compact superset that contains the real segments between its
real points.** Let `K` fill the compact `A` (`IsFilling K A`: `ℍ ∖ K` is the unbounded component of `ℍ ∖ A`),
let `L ⊇ A` be closed, and suppose `L` contains every real point between two real points of `A`. Then `K ∩ ℍ ⊆ fillC L`.

Proof: a point `z ∈ K ∩ ℍ` off `A` lies in a bounded component `C` of `ℍ ∖ A` (two unbounded components coincide). The
component `C'` of `z` in `ℂ ∖ L` stays in `C`: otherwise it meets `closure C ∖ C` at a point `x ∉ L`, which is real
(an interior point of `ℍ ∖ A` in `closure C` is in `C`) and, not being between two real points of `A`, has all real
points of `A` on one side; the half-strip on the other side (`exists_strip`) then lies in `C`, which is bounded. -/
theorem subset_fillC_of_isFilling {K A L : Set ℂ} (hA : IsCompact A) (hAL : A ⊆ L)
    (hconv : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.im = 0 → a₂.im = 0 → ∀ x : ℂ, x.im = 0 → a₁.re ≤ x.re → x.re ≤ a₂.re →
      x ∈ L)
    (hK : IsFilling K A) : K ∩ H ⊆ fillC L := by
  rintro z ⟨hzK, hzH⟩
  by_cases hzL : z ∈ L
  · exact Or.inl hzL
  right
  have hzA : z ∉ A := fun h => hzL (hAL h)
  set C := connectedComponentIn (H \ A) z with hCdef
  have hzC : z ∈ C := mem_connectedComponentIn ⟨hzH, hzA⟩
  have hCH : C ⊆ H \ A := connectedComponentIn_subset _ _
  have hCo : IsOpen C := isOpen_connectedComponentIn_H hA.isClosed z
  -- `C` is bounded
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
  have hR' : A ⊆ closedBall 0 (max R 0) := hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hCb : IsBounded C := by
    by_contra hCb
    obtain ⟨⟨z₀, hz₀, hcomp⟩, hunb⟩ := hK
    have hunb' : ¬ IsBounded (connectedComponentIn (H \ A) z₀) := by rwa [hcomp]
    have e := connectedComponentIn_eq_of_not_isBounded (le_max_right _ _) hR' hCb hunb'
    have hzC' : z ∈ connectedComponentIn (H \ A) z := hzC
    rw [e, hcomp] at hzC'
    exact hzC'.2 hzK
  -- the component of `z` off `L` stays in `C`
  refine hCb.subset ?_
  have hC'c : IsPreconnected (connectedComponentIn Lᶜ z) := isPreconnected_connectedComponentIn
  have hzC' : z ∈ connectedComponentIn Lᶜ z := mem_connectedComponentIn hzL
  have hC'L : connectedComponentIn Lᶜ z ⊆ Lᶜ := connectedComponentIn_subset _ _
  have hclH : closure C ⊆ {w : ℂ | 0 ≤ w.im} :=
    closure_minimal (fun w hw => show 0 ≤ w.im from le_of_lt (hCH hw).1)
      (isClosed_le continuous_const Complex.continuous_im)
  refine hC'c.subset_left_of_subset_union hCo isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.2 subset_closure) (fun x hx => ?_) ⟨z, hzC', hzC⟩
  by_cases hxC : x ∈ C
  · exact Or.inl hxC
  refine Or.inr fun hxcl => ?_
  have hxL : x ∉ L := hC'L hx
  have hxA : x ∉ A := fun h => hxL (hAL h)
  rcases lt_or_eq_of_le (show 0 ≤ x.im from hclH hxcl) with hxpos | hx0
  · -- an interior point of `ℍ ∖ A` in the closure of the component is in it
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (QuantumZipper.isOpen_H.sdiff hA.isClosed) x ⟨hxpos, hxA⟩
    obtain ⟨c, hcC, hcx⟩ := Metric.mem_closure_iff.1 hxcl r hr
    have hsub := subset_connectedComponentIn_of_meets (convex_ball x r).isPreconnected hball
      (show c ∈ ball x r by rw [mem_ball, dist_comm]; exact hcx) hcC
    exact hxC (hsub (mem_ball_self hr))
  · -- a real point: all real points of `A` are on one side of it
    have hx0' : x.im = 0 := hx0.symm
    have hside : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ a ∈ A, a.im = 0 → s * (a.re - x.re) < 0 := by
      by_cases hl : ∃ a ∈ A, a.im = 0 ∧ a.re ≤ x.re
      · obtain ⟨a₁, ha₁, ha₁0, ha₁x⟩ := hl
        refine ⟨1, Or.inl rfl, fun a ha ha0 => ?_⟩
        by_contra hcon
        exact hxL (hconv a₁ ha₁ a ha ha₁0 ha0 x hx0' ha₁x (by linarith))
      · push Not at hl
        exact ⟨-1, Or.inr rfl, fun a ha ha0 => by linarith [hl a ha ha0]⟩
    obtain ⟨s, hs, hside⟩ := hside
    obtain ⟨ρ, hρ, S, hBS, hSc, hSA, hSb⟩ := exists_strip hA hx0' hxA hs hside
    obtain ⟨c, hcC, hcx⟩ := Metric.mem_closure_iff.1 hxcl ρ hρ
    have hcS : c ∈ S := hBS ⟨by rw [mem_ball, dist_comm]; exact hcx, (hCH hcC).1⟩
    exact hSb (hCb.subset (subset_connectedComponentIn_of_meets hSc hSA hcS hcC))

/-! ### The compact set for the shift -/

/-- **The compact set for the Cameron–Martin shift of a stopped flow line** whose real points stay in `[a, b]`: the
filling of `(closure V ∩ ℍ̄) ∪ [a, b]`. -/
def shiftHullSet (V : Set ℂ) (a b : ℝ) : Set ℂ :=
  fillC ((closure V ∩ {w | 0 ≤ w.im}) ∪ (fun x : ℝ => (x : ℂ)) '' Icc a b)

/-- **The shift's compact set is admissible for `RLC.exists_shift_isGFFWithBoundaryData`**: it is compact, and its
real points lie over `O` when those of `closure V` and the interval `[a, b]` do. -/
theorem isCompact_shiftHullSet {V : Set ℂ} (hV : IsBounded V) (a b : ℝ) : IsCompact (shiftHullSet V a b) := by
  refine isCompact_fillC ((hV.isCompact_closure.inter_right ?_).union (isCompact_Icc.image (by fun_prop)))
  exact isClosed_le continuous_const Complex.continuous_im

theorem re_mem_of_mem_shiftHullSet {V : Set ℂ} (hV : IsBounded V) {O : Set ℝ}
    (hVO : ∀ z ∈ closure V, z.im = 0 → z.re ∈ O) {a b : ℝ} (hJO : Icc a b ⊆ O) {z : ℂ}
    (hz : z ∈ shiftHullSet V a b) (h0 : z.im = 0) : z.re ∈ O := by
  have hL : IsClosed ((closure V ∩ {w : ℂ | 0 ≤ w.im}) ∪ (fun x : ℝ => (x : ℂ)) '' Icc a b) :=
    ((hV.isCompact_closure.inter_right (isClosed_le continuous_const Complex.continuous_im)).union
      (isCompact_Icc.image (by fun_prop))).isClosed
  have hLH : ∀ w ∈ (closure V ∩ {w : ℂ | 0 ≤ w.im}) ∪ (fun x : ℝ => (x : ℂ)) '' Icc a b, 0 ≤ w.im := by
    rintro w (hw | ⟨x, -, rfl⟩)
    · exact hw.2
    · simp
  rcases mem_of_mem_fillC_of_im_eq_zero hL hLH hz h0 with hz' | ⟨x, hx, rfl⟩
  · exact hVO z hz'.1 h0
  · simpa using hJO hx

/-- **Every hull of a trace in `closure V ∩ ℍ̄` whose real points lie in `[a, b]` lies in the shift's compact set.** -/
theorem subset_shiftHullSet {V : Set ℂ} {a b : ℝ} {K A : Set ℂ} (hA : IsCompact A)
    (hAV : A ⊆ closure V ∩ {w | 0 ≤ w.im}) (hAJ : ∀ w ∈ A, w.im = 0 → w.re ∈ Icc a b) (hK : IsFilling K A) :
    K ∩ H ⊆ shiftHullSet V a b := by
  refine subset_fillC_of_isFilling hA (hAV.trans subset_union_left) (fun a₁ ha₁ a₂ ha₂ h₁ h₂ x hx0 hx₁ hx₂ => ?_) hK
  refine Or.inr ⟨x.re, ⟨(hAJ a₁ ha₁ h₁).1.trans hx₁, hx₂.trans (hAJ a₂ ha₂ h₂).2⟩, ?_⟩
  apply Complex.ext <;> simp [hx0]

end FlowStopIdentCM

end Restart

end InteractingSLE
