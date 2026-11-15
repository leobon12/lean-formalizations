/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.HullBasic
import QuantumZipper.Proofs.Complex.TopoJaniszewski

/-!
# Janiszewski's theorem in the upper half-plane, and local component labels

Packet PROVE-W4TIP. For a closed bounded set `F ⊆ ℂ`, the unbounded domain `ℍ \ fillH F` is the unbounded component
of `ℍ \ F` (`H_diff_fillH`). This file proves the two planar tools of the trapping classification in the proof of
Lemma G13 (supplement pp. 506–507), for compact sets that may touch the real line:

* **Janiszewski's theorem in `ℍ`** (`H_diff_fillH_inter_subset`): if `F₁, F₂` are compact and every point of
  `F₁ ∩ F₂` lies in a preconnected subset of `F₁ ∩ F₂` that meets `ℝ`, then a point of `ℍ` in the unbounded domains
  of both `F₁` and `F₂` is in the unbounded domain of `F₁ ∪ F₂`. As in the specification ("Take a closed lower
  half-disc `L` large enough …"), the proof applies QuantumZipper's compact-set theorem
  `QuantumZipper.CA.Topo.janiszewski` to `F₁ ∪ L` and `F₂ ∪ L`, whose intersection `(F₁ ∩ F₂) ∪ L` is connected, and
  then returns from `ℂ \ (F₁ ∪ F₂ ∪ L)` to `ℍ`.
* **Local labels** (`IsFreeAt`, `IsTrappedAt`): near a point of `ℍ̄ \ F`, the points of `ℍ` lie either all in the
  unbounded domain of `F` or all outside it (`isFreeAt_or_isTrappedAt`); the label is constant along a preconnected
  subset of `ℍ̄ \ F` (`isFreeAt_or_isTrappedAt_of_isPreconnected`), and every point of an unbounded preconnected subset is
  free (`isFreeAt_of_not_isBounded`). This is the specification's "an original-real point outside the old union has
  only one incident upper component" (p. 532) and "at a real point off `a`, a sufficiently small upper half-disc misses
  `a` and belongs to a single such component" (p. 506).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace HalfPlaneSep

variable {F F₁ F₂ X M : Set ℂ} {z : ℂ}

/-! ### The unbounded domain of a closed set -/

theorem mem_H_diff_fillH_of_isClosed (hF : IsClosed F) :
    z ∈ H \ fillH F ↔ z ∈ H \ F ∧ ¬ IsBounded (connectedComponentIn (H \ F) z) := by
  have hcl : closure F = F := hF.closure_eq
  constructor
  · rintro ⟨hz, hzf⟩
    have hzF : z ∉ F := fun h => hzf ⟨hz, Or.inl (by rw [hcl]; exact h)⟩
    exact ⟨⟨hz, hzF⟩, fun hb => hzf ⟨hz, Or.inr (by rw [hcl]; exact hb)⟩⟩
  · rintro ⟨⟨hz, hzF⟩, hb⟩
    refine ⟨hz, fun hzf => ?_⟩
    rcases hzf.2 with h | h
    · rw [hcl] at h; exact hzF h
    · rw [hcl] at h; exact hb h

theorem H_diff_fillH_subset_H_diff (hF : IsClosed F) : H \ fillH F ⊆ H \ F := fun _ hz =>
  ((mem_H_diff_fillH_of_isClosed hF).1 hz).1

/-- A preconnected unbounded subset of `ℍ \ F` lies in the unbounded domain of `F`. -/
theorem subset_H_diff_fillH_of_not_isBounded (hF : IsClosed F) (hX : IsPreconnected X)
    (hXu : ¬ IsBounded X) (hXF : X ⊆ H \ F) : X ⊆ H \ fillH F := by
  intro w hw
  refine (mem_H_diff_fillH_of_isClosed hF).2 ⟨hXF hw, fun hb => hXu (hb.subset ?_)⟩
  exact hX.subset_connectedComponentIn hw hXF

/-- The unbounded domain is saturated: it contains the component of each of its points. -/
theorem connectedComponentIn_subset_H_diff_fillH (hF : IsClosed F) (hz : z ∈ H \ fillH F) :
    connectedComponentIn (H \ F) z ⊆ H \ fillH F := by
  intro w hw
  have hz' := (mem_H_diff_fillH_of_isClosed hF).1 hz
  refine (mem_H_diff_fillH_of_isClosed hF).2 ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz'.2

/-- The unbounded domain of a closed bounded set is the component of `(R + 1) i` in `ℍ \ F`. -/
theorem exists_H_diff_fillH_eq (hF : IsClosed F) (hFb : IsBounded F) :
    ∃ R : ℝ, 0 < R ∧ F ⊆ ball 0 R ∧
      H \ fillH F = connectedComponentIn (H \ F) (((R + 1 : ℝ) : ℂ) * I) := by
  obtain ⟨R, hR, hFR⟩ := exists_closure_subset_ball hFb
  rw [hF.closure_eq] at hFR
  refine ⟨R, hR, hFR, ?_⟩
  have := H_diff_fillH hR (show closure F ⊆ ball 0 R by rwa [hF.closure_eq])
  rwa [hF.closure_eq] at this

theorem isPreconnected_H_diff_fillH (hF : IsClosed F) (hFb : IsBounded F) :
    IsPreconnected (H \ fillH F) := by
  obtain ⟨R, -, -, hEq⟩ := exists_H_diff_fillH_eq hF hFb
  rw [hEq]
  exact isPreconnected_connectedComponentIn

theorem not_isBounded_H_diff_fillH (hF : IsClosed F) (hFb : IsBounded F) :
    ¬ IsBounded (H \ fillH F) := by
  obtain ⟨R, hR, hFR, hEq⟩ := exists_H_diff_fillH_eq hF hFb
  rw [hEq]
  exact not_isBounded_connectedComponentIn_of_lt hR hFR

/-- If `A` misses the unbounded domain of `Y`, the unbounded domain of `Y` is also that of `Y ∪ A`. -/
theorem H_diff_fillH_subset_union_of_disjoint {Y A : Set ℂ} (hY : IsClosed Y) (hYb : IsBounded Y)
    (hA : IsClosed A) (hd : Disjoint A (H \ fillH Y)) : H \ fillH Y ⊆ H \ fillH (Y ∪ A) := by
  refine subset_H_diff_fillH_of_not_isBounded (hY.union hA) (isPreconnected_H_diff_fillH hY hYb)
    (not_isBounded_H_diff_fillH hY hYb) fun w hw => ⟨hw.1, ?_⟩
  rintro (h | h)
  · exact (H_diff_fillH_subset_H_diff hY hw).2 h
  · exact Set.disjoint_left.1 hd h hw

/-- A point of `ℍ` far from a closed bounded set is in its unbounded domain. -/
theorem mem_H_diff_fillH_of_le_norm (hF : IsClosed F) {R : ℝ} (hR : 0 < R) (hFR : F ⊆ ball 0 R)
    (hz : z ∈ H) (hzR : R ≤ ‖z‖) : z ∈ H \ fillH F := by
  have hEq := H_diff_fillH hR (show closure F ⊆ ball 0 R by rwa [hF.closure_eq])
  rw [hF.closure_eq] at hEq
  rw [hEq]
  exact mem_connectedComponentIn_of_le_norm hR hFR hz hzR


/-! ### Janiszewski's theorem in `ℍ` -/

/-- The closed lower half-disc of radius `R`. -/
def lowerDisc (R : ℝ) : Set ℂ := closedBall 0 R ∩ {w | w.im ≤ 0}

theorem isCompact_lowerDisc (R : ℝ) : IsCompact (lowerDisc R) :=
  (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_im continuous_const)

theorem isPreconnected_lowerDisc (R : ℝ) : IsPreconnected (lowerDisc R) :=
  ((convex_closedBall 0 R).inter
    (convex_halfSpace_le (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0)).isPreconnected

theorem notMem_lowerDisc_of_mem_H {R : ℝ} {w : ℂ} (hw : w ∈ H) : w ∉ lowerDisc R := fun h =>
  absurd h.2 (not_le.2 (show 0 < w.im from hw))

/-- **Janiszewski's theorem in `ℍ`** (supplement p. 506, "Neither branch is trapped": "The two compact plane sets
`a ∪ L` and `b ∪ L` have connected intersection exactly `L` … Hence, in the upper half-plane, the joint filled hull is
precisely the union of the two individual filled hulls"). Let `F₁, F₂` be compact, and let every point of `F₁ ∩ F₂`
lie in a preconnected subset of `F₁ ∩ F₂` meeting `ℝ`. Then a point of `ℍ` in the unbounded domains of `F₁` and of
`F₂` lies in the unbounded domain of `F₁ ∪ F₂`. -/
theorem H_diff_fillH_inter_subset (hF₁ : IsCompact F₁) (hF₂ : IsCompact F₂)
    (hC : ∀ w ∈ F₁ ∩ F₂, ∃ P ⊆ F₁ ∩ F₂, IsPreconnected P ∧ w ∈ P ∧ ∃ x ∈ P, x.im = 0) :
    (H \ fillH F₁) ∩ (H \ fillH F₂) ⊆ H \ fillH (F₁ ∪ F₂) := by
  rintro z ⟨hz₁, hz₂⟩
  have hF : IsCompact (F₁ ∪ F₂) := hF₁.union hF₂
  obtain ⟨R, hR, hFR, hEq⟩ := exists_H_diff_fillH_eq hF.isClosed hF.isBounded
  set b : ℂ := ((R + 1 : ℝ) : ℂ) * I with hb
  set L := lowerDisc R with hL
  have hbH : b ∈ H := by
    show 0 < b.im
    simp only [hb, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hbR : R ≤ ‖b‖ := by
    rw [hb, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith [le_abs_self (R + 1)]
  have hF₁R : F₁ ⊆ ball 0 R := subset_union_left.trans hFR
  have hF₂R : F₂ ⊆ ball 0 R := subset_union_right.trans hFR
  have hbG : ∀ {G : Set ℂ}, G ⊆ ball 0 R → b ∉ G := fun hGR h =>
    absurd (mem_ball_zero_iff.1 (hGR h)) (not_lt.2 hbR)
  -- `b` is joined to `z` off `Fᵢ ∪ L`
  have hjoin : ∀ {G : Set ℂ}, IsClosed G → G ⊆ ball 0 R → z ∈ H \ fillH G →
      b ∈ connectedComponentIn (G ∪ L)ᶜ z := by
    intro G hG hGR hzG
    have hEqG := H_diff_fillH hR (show closure G ⊆ ball 0 R by rwa [hG.closure_eq])
    rw [hG.closure_eq] at hEqG
    rw [hEqG] at hzG
    have hbz : b ∈ connectedComponentIn (H \ G) z := by
      rw [← connectedComponentIn_eq hzG]
      exact mem_connectedComponentIn ⟨hbH, hbG hGR⟩
    refine connectedComponentIn_mono z ?_ hbz
    rintro w ⟨hwH, hwG⟩ (h | h)
    · exact hwG h
    · exact notMem_lowerDisc_of_mem_H hwH h
  have h0L : (0 : ℂ) ∈ L := ⟨mem_closedBall_self hR.le, by simp⟩
  have hXY : IsPreconnected ((F₁ ∪ L) ∩ (F₂ ∪ L)) := by
    have he : (F₁ ∪ L) ∩ (F₂ ∪ L) = (F₁ ∩ F₂) ∪ L := by
      ext w; simp only [mem_inter_iff, mem_union]; tauto
    rw [he]
    refine isPreconnected_of_forall (0 : ℂ) fun w hw => ?_
    rcases hw with hw | hw
    · obtain ⟨P, hPF, hP, hwP, x, hxP, hx0⟩ := hC w hw
      have hxL : x ∈ L :=
        ⟨mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 (hF₁R (hPF hxP).1)).le, hx0.le⟩
      exact ⟨P ∪ L, union_subset_union_left _ hPF, Or.inr h0L, Or.inl hwP,
        hP.union x hxP hxL (isPreconnected_lowerDisc R)⟩
    · exact ⟨L, subset_union_right, h0L, hw, isPreconnected_lowerDisc R⟩
  have hzX : z ∉ (F₁ ∪ L) ∪ (F₂ ∪ L) := by
    rintro ((h | h) | (h | h))
    · exact (H_diff_fillH_subset_H_diff hF₁.isClosed hz₁).2 h
    · exact notMem_lowerDisc_of_mem_H hz₁.1 h
    · exact (H_diff_fillH_subset_H_diff hF₂.isClosed hz₂).2 h
    · exact notMem_lowerDisc_of_mem_H hz₁.1 h
  have hbX : b ∉ (F₁ ∪ L) ∪ (F₂ ∪ L) := by
    rintro ((h | h) | (h | h))
    · exact hbG hF₁R h
    · exact notMem_lowerDisc_of_mem_H hbH h
    · exact hbG hF₂R h
    · exact notMem_lowerDisc_of_mem_H hbH h
  have hJ := QuantumZipper.CA.Topo.janiszewski (hF₁.union (isCompact_lowerDisc R))
    (hF₂.union (isCompact_lowerDisc R)) hXY hzX hbX (hjoin hF₁.isClosed hF₁R hz₁)
    (hjoin hF₂.isClosed hF₂R hz₂)
  -- back to `ℍ`
  set C := connectedComponentIn ((F₁ ∪ L) ∪ (F₂ ∪ L))ᶜ z with hCdef
  set P := connectedComponentIn (H \ (F₁ ∪ F₂)) b with hPdef
  have hPo : IsOpen P := (QuantumZipper.isOpen_H.sdiff hF.isClosed).connectedComponentIn
  have hbP : b ∈ P := mem_connectedComponentIn ⟨hbH, fun h => (hbG hFR) h⟩
  have hfar : ∀ w ∈ H, R ≤ ‖w‖ → w ∈ P := fun w hw hwR =>
    mem_connectedComponentIn_of_le_norm hR hFR hw hwR
  have hclP : ∀ w ∈ H \ (F₁ ∪ F₂), w ∈ closure P → w ∈ P := by
    intro w hw hwc
    obtain ⟨ε, hε, hεw⟩ := Metric.isOpen_iff.1 (QuantumZipper.isOpen_H.sdiff hF.isClosed) w hw
    obtain ⟨u, huP, hu⟩ := Metric.mem_closure_iff.1 hwc ε hε
    have hub : u ∈ ball w ε := by rw [mem_ball, dist_comm]; exact hu
    have hsub := (convex_ball w ε).isPreconnected.subset_connectedComponentIn hub hεw
    rw [← connectedComponentIn_eq huP] at hsub
    exact hsub (mem_ball_self hε)
  have hCsub : C ⊆ P ∪ {w | R < ‖w‖} ∪ ((closure P)ᶜ ∩ ball 0 R) := by
    intro w hwC
    have hw : w ∉ (F₁ ∪ L) ∪ (F₂ ∪ L) := connectedComponentIn_subset _ _ hwC
    have hwF : w ∉ F₁ ∪ F₂ := fun h => h.elim (fun h => hw (Or.inl (Or.inl h)))
      fun h => hw (Or.inr (Or.inl h))
    have hwL : w ∉ L := fun h => hw (Or.inl (Or.inr h))
    by_cases hwR : R ≤ ‖w‖
    · by_cases hwH : w ∈ H
      · exact Or.inl (Or.inl (hfar w hwH hwR))
      · refine Or.inl (Or.inr (lt_of_le_of_ne hwR fun he => hwL ⟨?_, ?_⟩))
        · rw [mem_closedBall_zero_iff, ← he]
        · exact not_lt.1 (show ¬ (0 < w.im) from hwH)
    · have hwH : w ∈ H := by
        by_contra hwH
        exact hwL ⟨mem_closedBall_zero_iff.2 (not_le.1 hwR).le, not_lt.1 (show ¬ (0 < w.im) from hwH)⟩
      by_cases hwc : w ∈ closure P
      · exact Or.inl (Or.inl (hclP w ⟨hwH, hwF⟩ hwc))
      · exact Or.inr ⟨hwc, mem_ball_zero_iff.2 (not_le.1 hwR)⟩
  have hCP : C ⊆ P ∪ {w | R < ‖w‖} := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (hPo.union (isOpen_lt continuous_const continuous_norm))
      (isClosed_closure.isOpen_compl.inter isOpen_ball) ?_ hCsub ⟨b, hJ, Or.inl hbP⟩
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    rcases hw with hw | hw
    · exact hw'.1 (subset_closure hw)
    · exact absurd (mem_ball_zero_iff.1 hw'.2) (not_lt.2 (le_of_lt hw))
  rw [hEq]
  rcases hCP (mem_connectedComponentIn hzX) with h | h
  · exact h
  · exact hfar z hz₁.1 (le_of_lt h)

/-! ### Local labels -/

/-- Near `z`, every point of `ℍ` lies in the unbounded domain of `F`. -/
def IsFreeAt (F : Set ℂ) (z : ℂ) : Prop := ∃ ε > 0, ball z ε ∩ H ⊆ H \ fillH F

/-- Near `z`, no point lies in the unbounded domain of `F`. -/
def IsTrappedAt (F : Set ℂ) (z : ℂ) : Prop := ∃ ε > 0, Disjoint (ball z ε) (H \ fillH F)

theorem isPreconnected_ball_inter_H (z : ℂ) (ε : ℝ) : IsPreconnected (ball z ε ∩ H) :=
  ((convex_ball z ε).inter
    (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0)).isPreconnected

/-- **The label dichotomy** off a closed set. -/
theorem isFreeAt_or_isTrappedAt (hF : IsClosed F) (hz : z ∉ F) : IsFreeAt F z ∨ IsTrappedAt F z := by
  obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.1 hF.isOpen_compl z hz
  by_cases h : ∃ w ∈ ball z ε ∩ H, w ∈ H \ fillH F
  · obtain ⟨w, hw, hwU⟩ := h
    refine Or.inl ⟨ε, hε, fun u hu => ?_⟩
    have hsub : ball z ε ∩ H ⊆ H \ F := fun v hv => ⟨hv.2, hεF hv.1⟩
    exact connectedComponentIn_subset_H_diff_fillH hF hwU
      ((isPreconnected_ball_inter_H z ε).subset_connectedComponentIn hw hsub hu)
  · exact Or.inr ⟨ε, hε, Set.disjoint_left.2 fun w hw hwU => h ⟨w, ⟨hw, hwU.1⟩, hwU⟩⟩

theorem isOpen_setOf_isFreeAt (F : Set ℂ) : IsOpen {z | IsFreeAt F z} := by
  refine Metric.isOpen_iff.2 fun z hz => ?_
  obtain ⟨ε, hε, h⟩ := hz
  refine ⟨ε / 2, half_pos hε, fun w hw => ⟨ε / 2, half_pos hε, fun u hu => h ⟨?_, hu.2⟩⟩⟩
  refine ball_subset_ball' ?_ hu.1
  have : dist w z < ε / 2 := hw
  linarith

theorem isOpen_setOf_isTrappedAt (F : Set ℂ) : IsOpen {z | IsTrappedAt F z} := by
  refine Metric.isOpen_iff.2 fun z hz => ?_
  obtain ⟨ε, hε, h⟩ := hz
  refine ⟨ε / 2, half_pos hε, fun w hw => ⟨ε / 2, half_pos hε, h.mono_left (ball_subset_ball' ?_)⟩⟩
  have : dist w z < ε / 2 := hw
  linarith

theorem IsFreeAt.not_isTrappedAt (hf : IsFreeAt F z) (hz : 0 ≤ z.im) : ¬ IsTrappedAt F z := by
  rintro ⟨ε', hε', hd⟩
  obtain ⟨ε, hε, h⟩ := hf
  set δ : ℝ := min ε ε' / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hdist : dist (z + (δ : ℂ) * I) z = δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ0]
  have hδε : δ < ε := by
    have := min_le_left ε ε'; rw [hδ]; linarith [lt_min hε hε']
  have hδε' : δ < ε' := by
    have := min_le_right ε ε'; rw [hδ]; linarith [lt_min hε hε']
  have hwH : z + (δ : ℂ) * I ∈ H := by
    show 0 < (z + (δ : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  exact Set.disjoint_left.1 hd (show _ ∈ ball z ε' by rw [mem_ball, hdist]; exact hδε')
    (h ⟨show _ ∈ ball z ε by rw [mem_ball, hdist]; exact hδε, hwH⟩)

theorem IsTrappedAt.notMem (h : IsTrappedAt F z) : z ∉ H \ fillH F := fun hz => by
  obtain ⟨ε, hε, hd⟩ := h
  exact Set.disjoint_left.1 hd (mem_ball_self hε) hz

/-- **Constancy of the label** along a preconnected subset of `ℍ̄ \ F`. -/
theorem isFreeAt_or_isTrappedAt_of_isPreconnected (hF : IsClosed F) (hX : IsPreconnected X)
    (hXF : X ⊆ {w | 0 ≤ w.im} \ F) : (∀ w ∈ X, IsFreeAt F w) ∨ (∀ w ∈ X, IsTrappedAt F w) := by
  rcases isPreconnected_iff_subset_of_disjoint.1 hX {w | IsFreeAt F w} {w | IsTrappedAt F w}
      (isOpen_setOf_isFreeAt F) (isOpen_setOf_isTrappedAt F)
      (fun w hw => isFreeAt_or_isTrappedAt hF (hXF hw).2)
      (eq_empty_iff_forall_notMem.2 fun w hw => hw.2.1.not_isTrappedAt (hXF hw.1).1 hw.2.2) with h | h
  · exact Or.inl fun w hw => h hw
  · exact Or.inr fun w hw => h hw

/-- Every point of an unbounded preconnected subset of `ℍ̄ \ F` is free. -/
theorem isFreeAt_of_not_isBounded (hF : IsClosed F) (hFb : IsBounded F) (hX : IsPreconnected X)
    (hXu : ¬ IsBounded X) (hXF : X ⊆ {w | 0 ≤ w.im} \ F) : ∀ w ∈ X, IsFreeAt F w := by
  obtain ⟨R, hR, hFR, -⟩ := exists_H_diff_fillH_eq hF hFb
  obtain ⟨z₀, hz₀X, hz₀R⟩ : ∃ z₀ ∈ X, R + 1 < ‖z₀‖ := by
    by_contra h
    push Not at h
    exact hXu ((isBounded_closedBall (x := (0 : ℂ)) (r := R + 1)).subset fun w hw =>
      mem_closedBall_zero_iff.2 (h w hw))
  have hfree : IsFreeAt F z₀ := by
    refine ⟨1, one_pos, fun u hu => mem_H_diff_fillH_of_le_norm hF hR hFR hu.2 ?_⟩
    have h1 : dist u z₀ < 1 := hu.1
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le z₀ u
    rw [norm_sub_rev] at h2
    linarith
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hF hX hXF with h | h
  · exact h
  · exact absurd (h z₀ hz₀X) (hfree.not_isTrappedAt (hXF hz₀X).1)

/-- A point in the closure of `M ⊆ ℍ` at which `F` is free is in the closure of the part of `M` in the unbounded
domain of `F`. -/
theorem mem_closure_inter_of_isFreeAt (hz : z ∈ closure M) (hM : M ⊆ H) (hf : IsFreeAt F z) :
    z ∈ closure (M ∩ (H \ fillH F)) := by
  obtain ⟨ε, hε, h⟩ := hf
  rw [Metric.mem_closure_iff] at hz ⊢
  intro δ hδ
  obtain ⟨m, hm, hmz⟩ := hz (min δ ε) (lt_min hδ hε)
  refine ⟨m, ⟨hm, h ⟨?_, hM hm⟩⟩, lt_of_lt_of_le hmz (min_le_left _ _)⟩
  rw [mem_ball, dist_comm]
  exact lt_of_lt_of_le hmz (min_le_right _ _)

end HalfPlaneSep

end InteractingSLE
