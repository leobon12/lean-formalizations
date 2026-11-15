/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberTraverse
import InteractingSLE.Frozen.Spec.betweenComponents

/-!
# Chambers between ordered proper arcs of `ℍ` (Wang–Wu Proposition 4.20, Lemma 4.22; specification Lemma 7.1)

Packet PROVE-WW-B4. The disc results of `ChamberPocket.lean` and `ChamberTraverse.lean` transported back to `ℍ` by the
Cayley map. Setting (`IsOrderedArcs R M L`): three simple proper arcs of `ℍ` from `0` to `∞` (`IsProperArc`), the
middle arc `M` avoiding the right side of the right wall `R`, and the left wall `L` avoiding the right side of `M`
(Wang–Wu Proposition 4.19: "`γ_{u₂}` lies to the left of `γ_{u₁}`").

* `image_cayley_connectedComponentIn`: the Cayley map carries components of subsets of `ℍ` to components;
* `exists_contactGap_of_mem_betweenComponents`: **every component between the walls** (the frozen
  `betweenComponents`, Lemma GW3) **is the Cayley preimage of a pocket** `α[a, b] ∪ β[j a, j b]` — the Jordan domain
  of Wang–Wu Proposition 4.20 ("A component between two ordered simple arcs is bounded by one subarc of each, with
  common endpoints and disjoint interiors … It is a Jordan domain in the sphere");
* `interior_contact_toDisc`: Wang–Wu Lemma 4.21's conclusion (no common nontrivial arc: the contact times have empty
  interior) transfers to the disc;
* `IsOrderedArcs.traverse_disc`: **the traversal of every chamber** in the disc coordinates of the arcs.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.WangWu

/-! ### Components under the Cayley map -/

theorem cayley_cayleyInv_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : cayley (cayleyInv w) = w := by
  refine QuantumZipper.CA.cayley_cayleyInv fun h => ?_
  rw [h, mem_ball, dist_zero_right, norm_one] at hw
  exact lt_irrefl 1 hw

theorem cayleyInv_cayley_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : cayleyInv (cayley z) = z :=
  QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz)

theorem ne_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := fun h => by
  rw [h, mem_ball, dist_zero_right, norm_one] at hw; exact lt_irrefl 1 hw

/-- **The Cayley map carries components to components.** -/
theorem image_cayley_connectedComponentIn {E : Set ℂ} (hE : E ⊆ H) {z : ℂ} (hz : z ∈ E) :
    cayley '' connectedComponentIn E z = connectedComponentIn (cayley '' E) (cayley z) := by
  have hHbar : ∀ e ∈ E, e ∈ Hbar := fun e he => le_of_lt (show (0 : ℝ) < e.im from hE he)
  refine Subset.antisymm ?_ ?_
  · refine (isPreconnected_connectedComponentIn.image _ fun e he =>
      (continuousAt_cayley_of_mem_Hbar (hHbar e (connectedComponentIn_subset _ _ he))).continuousWithinAt
      ).subset_connectedComponentIn ⟨z, mem_connectedComponentIn hz, rfl⟩
        (image_mono (connectedComponentIn_subset _ _))
  · set K := connectedComponentIn (cayley '' E) (cayley z)
    have hKE : K ⊆ cayley '' E := connectedComponentIn_subset _ _
    have hKball : ∀ w ∈ K, w ∈ ball (0 : ℂ) 1 := fun w hw => by
      obtain ⟨e, he, rfl⟩ := hKE hw
      exact QuantumZipper.CA.cayley_mem_ball (hE he)
    have hinvK : cayleyInv '' K ⊆ E := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨e, he, rfl⟩ := hKE hw
      rw [cayleyInv_cayley_of_mem_Hbar (hHbar e he)]
      exact he
    have hpre : IsPreconnected (cayleyInv '' K) :=
      isPreconnected_connectedComponentIn.image _ fun w hw =>
        (continuousAt_cayleyInv (ne_one_of_mem_ball (hKball w hw))).continuousWithinAt
    have hzK : z ∈ cayleyInv '' K :=
      ⟨cayley z, mem_connectedComponentIn ⟨z, hz, rfl⟩, cayleyInv_cayley_of_mem_Hbar (hHbar z hz)⟩
    have hsub := hpre.subset_connectedComponentIn hzK hinvK
    intro w hw
    exact ⟨cayleyInv w, hsub ⟨w, hw, rfl⟩, cayley_cayleyInv_of_mem_ball (hKball w hw)⟩

/-- The Cayley image of `ℍ` minus two proper arcs is the disc minus their crosscuts. -/
theorem image_cayley_H_diff {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L) :
    cayley '' (H \ (arcRange R ∪ arcRange L)) =
      ball 0 1 \ (crossRange (toDisc R) ∪ crossRange (toDisc L)) := by
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hzRL⟩, rfl⟩
    have hzH : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)
    refine ⟨QuantumZipper.CA.cayley_mem_ball hz, fun h => hzRL ?_⟩
    rcases h with h | h
    · exact Or.inl ((hR.cayley_mem_crossRange_iff hzH).1 h)
    · exact Or.inr ((hL.cayley_mem_crossRange_iff hzH).1 h)
  · rintro ⟨hw, hwRL⟩
    have hzH := QuantumZipper.CA.cayleyInv_mem_H hw
    have hzHbar : cayleyInv w ∈ Hbar := le_of_lt (show (0 : ℝ) < (cayleyInv w).im from hzH)
    refine ⟨cayleyInv w, ⟨hzH, fun h => hwRL ?_⟩, cayley_cayleyInv_of_mem_ball hw⟩
    rw [← cayley_cayleyInv_of_mem_ball hw]
    rcases h with h | h
    · exact Or.inl ((hR.cayley_mem_crossRange_iff hzHbar).2 h)
    · exact Or.inr ((hL.cayley_mem_crossRange_iff hzHbar).2 h)

/-- **Every component between two ordered proper arcs is (the Cayley preimage of) a pocket.** -/
theorem exists_contactGap_of_mem_betweenComponents {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R))) {C : Set ℂ}
    (hC : C ∈ betweenComponents (arcRange R) (arcRange L)) :
    ∃ a b, IsContactGap (toDisc R) (toDisc L) a b ∧
      cayley '' C = jordanIn (pocketCurve (toDisc R) (toDisc L) a b) := by
  obtain ⟨z, ⟨hzH, hzRL⟩, hzR, hzL, rfl⟩ := hC
  have hzHbar : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hzH)
  have hzR' : z ∉ arcRange R := fun h => hzRL (Or.inl h)
  have hzL' : z ∉ arcRange L := fun h => hzRL (Or.inr h)
  have hz₁ : cayley z ∈ crossSide (toDisc R) 1 := by
    rcases hR.mem_leftSideOf_or_mem_rightSideOf hzH hzR' with h | h
    · exact (hR.mem_leftSideOf_iff hzH).1 h
    · exact absurd h hzR
  have hz₂ : cayley z ∈ crossSide (toDisc L) (-1) := by
    rcases hL.mem_leftSideOf_or_mem_rightSideOf hzH hzL' with h | h
    · exact absurd h hzL
    · exact (hL.mem_rightSideOf_iff hzH).1 h
  have hzβ : cayley z ∉ crossRange (toDisc L) := fun h => hzL' ((hL.cayley_mem_crossRange_iff hzHbar).1 h)
  obtain ⟨a, b, hg, hcomp⟩ := exists_contactGap_of_between hR.isDiscCrosscut_toDisc hL.isDiscCrosscut_toDisc
    ((disjoint_rightSideOf_iff hR hL).1 hord) hz₁ hz₂ hzβ
  refine ⟨a, b, hg, ?_⟩
  rw [image_cayley_connectedComponentIn sdiff_subset ⟨hzH, hzRL⟩, image_cayley_H_diff hR hL, hcomp]

/-- **A chamber exists when the walls differ** (Wang–Wu, proof of Proposition 4.24: "The absence of common arcs
guarantees a nonempty chamber"). If the right wall `R` has a point off the left wall `L`, there is a component between
them. -/
theorem nonempty_betweenComponents {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R))) (hne : ¬ arcRange R ⊆ arcRange L) :
    (betweenComponents (arcRange R) (arcRange L)).Nonempty := by
  have hα := hR.isDiscCrosscut_toDisc
  have hβ := hL.isDiscCrosscut_toDisc
  have hordD := (disjoint_rightSideOf_iff hR hL).1 hord
  obtain ⟨p, ⟨t, ht, rfl⟩, hpL⟩ := not_subset.1 hne
  have ht0 : 0 < t := lt_of_le_of_ne (mem_Ici.1 ht) fun h => hpL (by
    rw [← h, hR.zero, ← hL.zero]; exact ⟨0, mem_Ici.2 le_rfl, rfl⟩)
  have hpH := hR.mem_H t ht0
  have hpHbar : R t ∈ Hbar := le_of_lt (show (0 : ℝ) < (R t).im from hpH)
  set q := cayley (R t)
  have hqα : q ∈ crossRange (toDisc R) := (hR.cayley_mem_crossRange_iff hpHbar).2 ⟨t, ht, rfl⟩
  have hqβ : q ∉ crossRange (toDisc L) := fun h => hpL ((hL.cayley_mem_crossRange_iff hpHbar).1 h)
  have hqD : q ∈ ball (0 : ℂ) 1 := QuantumZipper.CA.cayley_mem_ball hpH
  have hq2 : q ∈ crossSide (toDisc L) (-1) := hβ.mem_crossSide_neg_of hqD hqβ fun h =>
    Set.disjoint_left.1 (hα.disjoint_crossRange_crossSide_swap hβ hordD) hqα h
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 (hβ.isOpen_crossSide (Or.inr rfl)) q hq2
  obtain ⟨w, hw1, hwq⟩ := Metric.mem_closure_iff.1 (hα.crossRange_subset_closure_crossSide (Or.inl rfl) hqα) r hr
  have hw2 : w ∈ crossSide (toDisc L) (-1) := hrS (by rw [mem_ball, dist_comm]; exact hwq)
  have hwα := hα.crossSide_subset (Or.inl rfl) hw1
  have hwβ := hβ.crossSide_subset (Or.inr rfl) hw2
  set z := cayleyInv w
  have hzH : z ∈ H := QuantumZipper.CA.cayleyInv_mem_H hwα.1
  have hzHbar : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hzH)
  have hcz : cayley z = w := cayley_cayleyInv_of_mem_ball hwα.1
  refine ⟨_, z, ⟨hzH, fun h => ?_⟩, fun h => ?_, fun h => ?_, rfl⟩
  · rcases h with h | h
    · exact hwα.2 (hcz ▸ (hR.cayley_mem_crossRange_iff hzHbar).2 h)
    · exact hwβ.2 (hcz ▸ (hL.cayley_mem_crossRange_iff hzHbar).2 h)
  · have := (hR.mem_rightSideOf_iff hzH).1 h
    rw [hcz] at this
    exact Set.disjoint_left.1 hα.disjoint_crossSide hw1 this
  · have := (hL.mem_leftSideOf_iff hzH).1 h
    rw [hcz] at this
    exact Set.disjoint_left.1 hβ.disjoint_crossSide this hw2

/-! ### Contact times -/

theorem discTime_lt_discTime {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t') : discTime t < discTime t' := by
  rw [discTime, discTime, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Lemma 4.21's conclusion in disc time.** If the times at which a proper arc `M` lies on the proper arc `R`
have empty interior, so do the corresponding times of their crosscuts. -/
theorem interior_contact_toDisc {M R : ℝ → ℂ} (hM : IsProperArc M) (hR : IsProperArc R)
    (h : interior {t ∈ Ici (0 : ℝ) | M t ∈ arcRange R} = ∅) :
    interior {s ∈ Icc (0 : ℝ) 1 | toDisc M s ∈ crossRange (toDisc R)} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hεX⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hX : ∀ s ∈ ball x ε, s ∈ Icc (0 : ℝ) 1 ∧ toDisc M s ∈ crossRange (toDisc R) :=
    fun s hs => by
      have h' := interior_subset (s := {s ∈ Icc (0 : ℝ) 1 | toDisc M s ∈ crossRange (toDisc R)}) (hεX hs)
      exact h'
  have hx1 : x < 1 := by
    have := (hX (x + ε / 2) (by rw [mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)).1.2
    linarith
  set c := max (x - ε / 2) 0
  have hc : c < x := max_lt (by linarith) (by
    have := (hX x (mem_ball_self hε)).1.1
    rcases eq_or_lt_of_le this with h0 | h0
    · exfalso
      have := (hX (x - ε / 2) (by rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]; linarith)).1.1
      linarith
    · exact h0)
  have hc0 : 0 ≤ c := le_max_right _ _
  have hJ : Ioo (arcTime c) (arcTime x) ⊆ {t ∈ Ici (0 : ℝ) | M t ∈ arcRange R} := by
    intro t ht
    have ht0 : 0 ≤ t := (arcTime_nonneg ⟨hc0, hc.trans hx1⟩).trans ht.1.le
    have hs1 : discTime t ∈ Ioo c x := by
      constructor
      · have := discTime_lt_discTime (arcTime_nonneg ⟨hc0, hc.trans hx1⟩) ht.1
        rwa [discTime_arcTime (hc.trans hx1)] at this
      · have := discTime_lt_discTime ht0 ht.2
        rwa [discTime_arcTime hx1] at this
    have hsball : discTime t ∈ ball x ε := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs1.1, hs1.2, le_max_left (x - ε / 2) 0]
    have hmem := (hX _ hsball).2
    rw [toDisc_discTime M ht0] at hmem
    exact ⟨ht0, (hR.cayley_mem_crossRange_iff (hM.mem_Hbar ht0)).1 hmem⟩
  have hsub := interior_maximal hJ isOpen_Ioo
  rw [h, subset_empty_iff] at hsub
  exact (nonempty_Ioo.2 (strictMonoOn_arcTime ⟨hc0, hc.trans hx1⟩ ⟨hc0.trans hc.le, hx1⟩ hc)).ne_empty hsub

/-! ### Three ordered proper arcs -/

/-- **Three ordered proper arcs** (Wang–Wu Lemma 4.22: "three seed lines of heights `u₁ < 0 < u₂` … ordered"): the
middle arc `M` avoids the right side of the right wall `R`, the left wall `L` avoids the right side of `M`. -/
structure IsOrderedArcs (R M L : ℝ → ℂ) : Prop where
  right : IsProperArc R
  middle : IsProperArc M
  left : IsProperArc L
  right_middle : Disjoint (arcRange M) (rightSideOf (arcRange R))
  middle_left : Disjoint (arcRange L) (rightSideOf (arcRange M))

namespace IsOrderedArcs

variable {R M L : ℝ → ℂ}

theorem toTriple (h : IsOrderedArcs R M L) : IsOrderedTriple (toDisc R) (toDisc M) (toDisc L) :=
  ⟨h.right.isDiscCrosscut_toDisc, h.middle.isDiscCrosscut_toDisc, h.left.isDiscCrosscut_toDisc,
    (disjoint_rightSideOf_iff h.right h.middle).1 h.right_middle,
    (disjoint_rightSideOf_iff h.middle h.left).1 h.middle_left⟩

theorem right_left (h : IsOrderedArcs R M L) : Disjoint (arcRange L) (rightSideOf (arcRange R)) :=
  (disjoint_rightSideOf_iff h.right h.left).2 h.toTriple.lower_upper

/-- **The traversal of every chamber, in disc coordinates** (Wang–Wu Lemma 4.22, first part). For every component
`C` between the walls, with no nontrivial common arc of `M` with either wall: `C` is the Cayley preimage of a pocket
`U` with corners `α a = M̃ σ`, `α b = M̃ τ` (`α`, `M̃` the crosscuts of `R`, `M`), `σ < τ`, the middle crosscut lies in
`closure U` exactly on `[σ, τ]`, and its times in `(σ, τ]` outside `U` have empty interior. -/
theorem traverse_disc (h : IsOrderedArcs R M L) (hcR : interior {t ∈ Ici (0 : ℝ) | M t ∈ arcRange R} = ∅)
    (hcL : interior {t ∈ Ici (0 : ℝ) | M t ∈ arcRange L} = ∅) {C : Set ℂ}
    (hC : C ∈ betweenComponents (arcRange R) (arcRange L)) :
    ∃ a b, IsContactGap (toDisc R) (toDisc L) a b ∧
      cayley '' C = jordanIn (pocketCurve (toDisc R) (toDisc L) a b) ∧
      ∃ σ τ, 0 ≤ σ ∧ σ < τ ∧ τ ≤ 1 ∧ toDisc M σ = toDisc R a ∧ toDisc M τ = toDisc R b ∧
        (∀ t ∈ Icc σ τ, toDisc M t ∈ closure (jordanIn (pocketCurve (toDisc R) (toDisc L) a b))) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, t ∉ Icc σ τ →
          toDisc M t ∉ closure (jordanIn (pocketCurve (toDisc R) (toDisc L) a b))) ∧
        interior {t ∈ Icc σ τ | σ < t ∧ toDisc M t ∉ jordanIn (pocketCurve (toDisc R) (toDisc L) a b)} = ∅ := by
  obtain ⟨a, b, hg, hC'⟩ := exists_contactGap_of_mem_betweenComponents h.right h.left h.right_left hC
  exact ⟨a, b, hg, hC', h.toTriple.traverse (interior_contact_toDisc h.middle h.right hcR)
    (interior_contact_toDisc h.middle h.left hcL) hg⟩

end IsOrderedArcs

end InteractingSLE.WangWu
