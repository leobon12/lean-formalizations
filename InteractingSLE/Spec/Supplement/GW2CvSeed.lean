/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# GW2's root cover: admissible initial angles and the first low right arc

Packet PROVE-GW2-COVER. Lemma GW2's proof, "An initial positive interior prefix always exists"
(`source/spec/p577-624.md` L1001–L1010): if the lower extreme is initially admissible, a fixed angle
`θ₀ ∈ Θ` with an admissible seed at the original target exists; if instead the lower extreme is
immediately inadmissible, the first right interval is low, `−λ − πχ/2 < H₀ ≤ −λ + πχ/2` (GW2.1), and
the interval (GW2.2) of angles with an admissible seed at an interior point `v` of that interval is
nonempty, so it meets `Θ`.

This file is the deterministic part, from the ambient bounds of GW1 (`GW1Conn.ambient_bounds`):

* `exists_mem_isAdmissibleSeed`: an admissible seed angle in `Θ` exists whenever the explicit
  admissible interval of angles is nonempty (three strict inequalities);
* `exists_root_angle`: the dichotomy of GW2 (admissible lower extreme at `0`, or the low first right
  interval with an admissible angle for the common height `H₀`);
* `exists_pos_jumpFree`, `lims_eq_of_jumpFree`: a right arc `(0, a)` free of jump candidates, on which
  both one-sided limits at every point equal `b(0⁺)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootCv

open PiecewiseConstantBoundaryData (leftLim rightLim)

/-! ### Admissible angles -/

/-- **An admissible seed angle in a dense angle set.** For heights `L = b(x⁻)`, `R = b(x⁺)` with
`L − R < 2λ`, `L − πχ/2 < λ` and `−λ < R + πχ/2`, the angles `θ ∈ (−π/2, π/2)` with
`L + θχ < λ` and `−λ < R + θχ` form a nonempty open set, which meets every set `Θ` dense in
`(−π/2, π/2)`. -/
theorem exists_mem_isAdmissibleSeed {κ L R : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Θ : Set ℝ}
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ)
    (hLR : L - R < 2 * sleLambda κ) (hL : L + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : -sleLambda κ < R + Real.pi / 2 * chiC κ) :
    ∃ θ ∈ Θ, θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧ ExplState.IsAdmissibleSeed κ L R θ := by
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  set a : ℝ := (-sleLambda κ - R) / chiC κ with ha
  set b' : ℝ := (sleLambda κ - L) / chiC κ with hb'
  have hab : a < b' := by
    rw [ha, hb']
    exact div_lt_div_of_pos_right (by linarith) hχ
  have ha2 : a < Real.pi / 2 := by
    rw [ha, div_lt_iff₀ hχ]
    linarith
  have hb2 : -(Real.pi / 2) < b' := by
    rw [hb', lt_div_iff₀ hχ]
    linarith
  have hpi : -(Real.pi / 2) < Real.pi / 2 := by linarith [Real.pi_pos]
  set lo : ℝ := max a (-(Real.pi / 2))
  set hi : ℝ := min b' (Real.pi / 2)
  have hlohi : lo < hi := max_lt (lt_min hab ha2) (lt_min hb2 hpi)
  obtain ⟨θ₁, h1, h2⟩ := exists_between hlohi
  let U : Set ℝ := {θ | L + θ * chiC κ < sleLambda κ ∧ -sleLambda κ < R + θ * chiC κ} ∩
    Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hU : IsOpen U := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) isOpen_Ioo
    · exact isOpen_lt (continuous_const.add (continuous_id.mul continuous_const)) continuous_const
    · exact isOpen_lt continuous_const (continuous_const.add (continuous_id.mul continuous_const))
  have hθ₁ : θ₁ ∈ U := by
    have hθa : a < θ₁ := (le_max_left _ _).trans_lt h1
    have hθb : θ₁ < b' := h2.trans_le (min_le_left _ _)
    refine ⟨⟨?_, ?_⟩, (le_max_right _ _).trans_lt h1, h2.trans_le (min_le_right _ _)⟩
    · have := (lt_div_iff₀ hχ).1 (hb' ▸ hθb)
      linarith
    · have := (div_lt_iff₀ hχ).1 (ha ▸ hθa)
      linarith
  obtain ⟨θ, hθU, hθΘ⟩ := mem_closure_iff.1 (hΘd hθ₁.2) U hU hθ₁
  exact ⟨θ, hθΘ, hθU.2, hθU.1⟩

/-- **GW2's dichotomy at the original target** (Lemma GW2's proof, (GW2.1)–(GW2.2)). Under the
ambient bounds `b(0⁻) − πχ/2 < λ` and `−λ < b(0⁺) + πχ/2`, either the lower extreme is initially
admissible and some `θ₀ ∈ Θ` has an admissible seed at `0`, or the first right height is low,
`b(0⁺) − πχ/2 ≤ −λ`, and some `θ₀ ∈ Θ` has an admissible seed for the common height `b(0⁺)` on both
sides. -/
theorem exists_root_angle {κ L R : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Θ : Set ℝ}
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ)
    (hL : L + -(Real.pi / 2) * chiC κ < sleLambda κ) (hR : -sleLambda κ < R + Real.pi / 2 * chiC κ) :
    (-sleLambda κ < R + -(Real.pi / 2) * chiC κ ∧
        ∃ θ ∈ Θ, θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧ ExplState.IsAdmissibleSeed κ L R θ) ∨
      (R + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ ∧
        ∃ θ ∈ Θ, θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧ ExplState.IsAdmissibleSeed κ R R θ) := by
  have hΛ : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  have hpχ : 0 < Real.pi / 2 * chiC κ := mul_pos (by linarith [Real.pi_pos]) hχ
  rcases lt_or_ge (-sleLambda κ) (R + -(Real.pi / 2) * chiC κ) with h | h
  · refine Or.inl ⟨h, exists_mem_isAdmissibleSeed hκ hκ4 hΘd ?_ hL hR⟩
    linarith
  · refine Or.inr ⟨h, exists_mem_isAdmissibleSeed hκ hκ4 hΘd (by linarith) ?_ hR⟩
    linarith

/-! ### The first right arc -/

/-- **A jump-free right arc.** For a finite set `J` of jump candidates there is `a > 0` with no
candidate in `(0, a)`. -/
theorem exists_pos_jumpFree (J : Finset ℝ) : ∃ a : ℝ, 0 < a ∧ ∀ y ∈ J, y ∉ Ioo 0 a := by
  classical
  let T : Finset ℝ := insert 1 (J.filter fun y => 0 < y)
  have hT : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨T.min' hT, ?_, fun y hy hya => ?_⟩
  · rcases Finset.mem_insert.1 (T.min'_mem hT) with h1 | h1
    · rw [h1]
      exact one_pos
    · exact (Finset.mem_filter.1 h1).2
  · have hyT : y ∈ T := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy, hya.1⟩)
    exact (not_lt.2 (T.min'_le y hyT)) hya.2

/-- A point `v > 0` with no jump candidate in `(0, v]` has a jump-free neighbourhood `(0, a)`,
`v < a`. -/
theorem exists_jumpFree_of_Ioc (J : Finset ℝ) {v : ℝ} (hJ : ∀ y ∈ J, y ∉ Ioc 0 v) :
    ∃ a : ℝ, v < a ∧ ∀ y ∈ J, y ∉ Ioo 0 a := by
  classical
  let T : Finset ℝ := insert (v + 1) (J.filter fun y => v < y)
  have hT : T.Nonempty := ⟨v + 1, Finset.mem_insert_self _ _⟩
  have hvT : ∀ m ∈ T, v < m := fun m hm => by
    rcases Finset.mem_insert.1 hm with h1 | h1
    · rw [h1]; linarith
    · exact (Finset.mem_filter.1 h1).2
  refine ⟨T.min' hT, hvT _ (T.min'_mem hT), fun y hy hya => ?_⟩
  rcases le_or_gt y v with hyv | hyv
  · exact hJ y hy ⟨hya.1, hyv⟩
  · have hyT : y ∈ T := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy, hyv⟩)
    exact (not_lt.2 (T.min'_le y hyT)) hya.2

/-- **On the first right arc both one-sided limits are `b(0⁺)`.** If no jump candidate lies in
`(0, v]`, `v > 0`, then `b(v⁻) = b(v⁺) = b(0⁺)`. -/
theorem lims_eq_of_jumpFree {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {v : ℝ} (hv : 0 < v) (hJ : ∀ y ∈ J, y ∉ Ioc 0 v) :
    leftLim b v = rightLim b 0 ∧ rightLim b v = rightLim b 0 := by
  obtain ⟨a, hva, ha⟩ := exists_jumpFree_of_Ioc J hJ
  have hv' : v ∈ Ioo 0 a := ⟨hv, hva⟩
  have hc : ∀ t ∈ Ioo 0 a, b t = b v := fun t ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb ha hv' ht
  have h0 : rightLim b 0 = b v := Sec4.rightLim_eq_of_forall (hv.trans hva) hc
  refine ⟨?_, ?_⟩
  · rw [h0]
    exact Sec4.leftLim_eq_of_forall hv fun t ht => hc t ⟨ht.1, ht.2.trans hva⟩
  · rw [h0]
    exact Sec4.rightLim_eq_of_forall hva fun t ht => hc t ⟨hv.trans ht.1, ht.2⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootCv
