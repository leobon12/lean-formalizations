/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopType

/-!
# GB6's conditional words have countably many types

Packet PROVE-Q3-REL4 (step (D)). The relative chain is run type by type (`Q3StopType`); the types are combined
almost surely because, for fixed `(κ, θ, c)`, the conditional words `β(r) = gb6WordOfRec κ θ c r` take only countably
many types:

* the stop word of `(c, θ, r)` has fixed count and fixed heights (only its positions depend on the record), so its
  boundary function takes finitely many values; the returned word's heights `−f(−1/x) + πχ + χ ℓ(x)` take finitely
  many values (`ℓ ∈ {−2π, 0}`), and its count is at most twice the count plus one (`gb6WordOfRec_bounded`);
* a word with heights in a set `H` and count `N` has a type in `typeSet κ H (N + 1)`: at most `N + 1` marks on each
  side and weights in `weightSet κ H` (one-sided limits of a word's function are heights), padded by zeros
  (`wordType_mem_typeSet`);
* `typeSet κ H N` is countable when `H` is finite (`countable_typeSet`);
* **`countable_range_wordType_gb6`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.Q3Stop

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 Theorem14.GW2JointKernel Sec7.StripSysField
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-! ### Weights of a word with heights in a set -/

/-- The possible weights of the flow-line word (at `0`, angle `0`) of a word with heights in `H`. -/
def weightSet (κ : ℝ) (H : Set ℝ) : Set ℝ :=
  insert 0 (((fun u => -u / sleLambda κ - 1) '' H ∪ (fun u => u / sleLambda κ - 1) '' H) ∪
    image2 (fun u v => (u - v) / sleLambda κ) H H)

theorem finite_weightSet (κ : ℝ) {H : Set ℝ} (hH : H.Finite) : (weightSet κ H).Finite :=
  (((hH.image _).union (hH.image _)).union (hH.image2 _ hH)).insert 0

theorem flowLineRhoL_mem_weightSet (κ : ℝ) (c : BoundaryWord) {H : Set ℝ} (hH : ∀ j, c.2.2 j ∈ H)
    (i : Fin (flowLineNL c.fn c.jumps 0)) : flowLineRhoL κ c.fn c.jumps 0 0 i ∈ weightSet κ H := by
  have hl : ∀ y, leftLim c.fn y ∈ H := fun y => (Restart.BoundaryWord.leftLim_fn c y).symm ▸ hH _
  have hr : ∀ y, rightLim c.fn y ∈ H := fun y => (Restart.BoundaryWord.rightLim_fn c y).symm ▸ hH _
  obtain ⟨k, hk⟩ := i
  rcases k with _ | k
  · have e : flowLineRhoL κ c.fn c.jumps 0 0 ⟨0, hk⟩ = -leftLim c.fn 0 / sleLambda κ - 1 := by
      change -(leftLim c.fn 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1 = _
      rw [zero_mul, add_zero]
    rw [e]
    exact mem_insert_of_mem _ (Or.inl (Or.inl ⟨_, hl 0, rfl⟩))
  · obtain ⟨y, hy⟩ : ∃ y, flowLineRhoL κ c.fn c.jumps 0 0 ⟨k + 1, hk⟩ =
        (rightLim c.fn y - leftLim c.fn y) / sleLambda κ := ⟨_, rfl⟩
    rw [hy]
    exact mem_insert_of_mem _ (Or.inr ⟨_, hr y, _, hl y, rfl⟩)

theorem flowLineRhoR_mem_weightSet (κ : ℝ) (c : BoundaryWord) {H : Set ℝ} (hH : ∀ j, c.2.2 j ∈ H)
    (j : Fin (flowLineNR c.fn c.jumps 0)) : flowLineRhoR κ c.fn c.jumps 0 0 j ∈ weightSet κ H := by
  have hl : ∀ y, leftLim c.fn y ∈ H := fun y => (Restart.BoundaryWord.leftLim_fn c y).symm ▸ hH _
  have hr : ∀ y, rightLim c.fn y ∈ H := fun y => (Restart.BoundaryWord.rightLim_fn c y).symm ▸ hH _
  obtain ⟨k, hk⟩ := j
  rcases k with _ | k
  · have e : flowLineRhoR κ c.fn c.jumps 0 0 ⟨0, hk⟩ = rightLim c.fn 0 / sleLambda κ - 1 := by
      change (rightLim c.fn 0 + 0 * QuantumZipper.chiC κ) / sleLambda κ - 1 = _
      rw [zero_mul, add_zero]
    rw [e]
    exact mem_insert_of_mem _ (Or.inl (Or.inr ⟨_, hr 0, rfl⟩))
  · obtain ⟨y, hy⟩ : ∃ y, flowLineRhoR κ c.fn c.jumps 0 0 ⟨k + 1, hk⟩ =
        (rightLim c.fn y - leftLim c.fn y) / sleLambda κ := ⟨_, rfl⟩
    rw [hy]
    exact mem_insert_of_mem _ (Or.inr ⟨_, hr y, _, hl y, rfl⟩)

theorem flowLineNL_le (c : BoundaryWord) : flowLineNL c.fn c.jumps 0 ≤ c.1 + 1 := by
  unfold flowLineNL
  have h1 := Finset.card_le_card (Finset.filter_subset (· < (0 : ℝ))
    (PiecewiseConstantBoundaryData.jumpSet c.fn c.jumps))
  have h2 : (PiecewiseConstantBoundaryData.jumpSet c.fn c.jumps).card ≤ c.jumps.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h3 : c.jumps.card ≤ c.1 := (Finset.card_image_le).trans (Finset.card_range c.1).le
  omega

theorem flowLineNR_le (c : BoundaryWord) : flowLineNR c.fn c.jumps 0 ≤ c.1 + 1 := by
  unfold flowLineNR
  have h1 := Finset.card_le_card (Finset.filter_subset ((0 : ℝ) < ·)
    (PiecewiseConstantBoundaryData.jumpSet c.fn c.jumps))
  have h2 : (PiecewiseConstantBoundaryData.jumpSet c.fn c.jumps).card ≤ c.jumps.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h3 : c.jumps.card ≤ c.1 := (Finset.card_image_le).trans (Finset.card_range c.1).le
  omega

/-! ### Countably many types -/

/-- Types with at most `N` marks on each side, weights in `weightSet κ H`, padded by zeros from `N` on. -/
def typeSet (κ : ℝ) (H : Set ℝ) (N : ℕ) : Set WordType :=
  {w | w.1 ≤ N ∧ w.2.1 ≤ N ∧ (∀ i, w.2.2.1 i ∈ weightSet κ H) ∧ (∀ i, N ≤ i → w.2.2.1 i = 0) ∧
    (∀ j, w.2.2.2 j ∈ weightSet κ H) ∧ ∀ j, N ≤ j → w.2.2.2 j = 0}

/-- Zero-padded sequences with values in a finite set form a countable set. -/
theorem countable_padded {D : Set ℝ} (hD : D.Finite) (N : ℕ) :
    {a : ℕ → ℝ | (∀ i, a i ∈ D) ∧ ∀ i, N ≤ i → a i = 0}.Countable := by
  have : Finite D := hD.to_subtype
  refine (countable_range fun f : Fin N → D => fun i : ℕ => if h : i < N then (f ⟨i, h⟩ : ℝ) else 0).mono ?_
  rintro a ⟨ha, ha0⟩
  refine ⟨fun i => ⟨a i, ha i⟩, funext fun i => ?_⟩
  by_cases h : i < N
  · simp only [h, ↓reduceDIte]
  · simp only [h, ↓reduceDIte]
    exact (ha0 i (not_lt.1 h)).symm

theorem countable_typeSet (κ : ℝ) {H : Set ℝ} (hH : H.Finite) (N : ℕ) : (typeSet κ H N).Countable := by
  have hA := countable_padded (finite_weightSet κ hH) N
  refine (((finite_Iic N).countable.prod ((finite_Iic N).countable.prod (hA.prod hA)))).mono ?_
  rintro w ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

theorem wordType_mem_typeSet (κ : ℝ) (c : BoundaryWord) {H : Set ℝ} (hH : ∀ j, c.2.2 j ∈ H) {N : ℕ}
    (hN : c.1 ≤ N) : wordType κ c ∈ typeSet κ H (N + 1) := by
  have hL := flowLineNL_le c
  have hR := flowLineNR_le c
  refine ⟨by simp only [wordType]; omega, by simp only [wordType]; omega, fun i => ?_, fun i hi => ?_,
    fun j => ?_, fun j hj => ?_⟩
  · simp only [wordType, padFL]
    split_ifs with h
    · exact flowLineRhoL_mem_weightSet κ c hH ⟨i, h⟩
    · exact mem_insert 0 _
  · simp only [wordType, padFL]
    rw [dite_eq_right_iff]
    intro h
    omega
  · simp only [wordType, padFL]
    split_ifs with h
    · exact flowLineRhoR_mem_weightSet κ c hH ⟨j, h⟩
    · exact mem_insert 0 _
  · simp only [wordType, padFL]
    rw [dite_eq_right_iff]
    intro h
    omega

/-! ### GB6's conditional words -/

/-- **GB6's conditional words have finitely many heights and bounded count.** -/
theorem gb6WordOfRec_bounded (κ θ : ℝ) (c : BoundaryWord) :
    ∃ H : Set ℝ, H.Finite ∧ ∃ N : ℕ, ∀ r : RecData,
      (∀ j, (gb6WordOfRec κ θ c r).2.2 j ∈ H) ∧ (gb6WordOfRec κ θ c r).1 ≤ N := by
  set n₀ : ℕ := flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0 with hn₀
  set h₀ : ℕ → ℝ := wordHeight κ (flowLineNL c.fn c.jumps 0) (padFL κ θ c.fn c.jumps).2.1
    (padFL κ θ c.fn c.jumps).2.2 (θ * QuantumZipper.chiC κ) with hh₀
  set H₀ : Set ℝ := h₀ '' Iic n₀ with hH₀
  have hH₀f : H₀.Finite := (finite_Iic n₀).image h₀
  set H : Set ℝ := image2 (fun v e => -v + Real.pi * QuantumZipper.chiC κ + QuantumZipper.chiC κ * e) H₀
    {-(2 * Real.pi), 0} with hH
  refine ⟨H, hH₀f.image2 _ (toFinite _), 2 * n₀ + 1, fun r => ⟨fun j => ?_, ?_⟩⟩
  · set c' := stopWord κ (c, θ, r) with hc'
    have hc'1 : c'.1 = n₀ := rfl
    have hc'2 : c'.2.2 = h₀ := rfl
    have hfn : ∀ z, c'.fn z ∈ H₀ := fun z => by
      refine ⟨c'.index z, ?_, ?_⟩
      · change c'.index z ≤ n₀
        rw [← hc'1]
        exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
      · rw [← hc'2]
        rfl
    set x := midPt (retCount c') (retPos c') j
    change returnData (Real.pi * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) c'.fn x ∈ H
    refine ⟨c'.fn (-x⁻¹), hfn _, liftBoundary x, ?_, ?_⟩
    · unfold liftBoundary
      split_ifs
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ rfl
    · simp only [returnData]
  · set c' := stopWord κ (c, θ, r) with hc'
    have hc'1 : c'.1 = n₀ := rfl
    change retCount c' ≤ 2 * n₀ + 1
    have h1 : nNeg c' ≤ n₀ := by
      rw [← hc'1]
      exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have h2 : nPos c' ≤ n₀ := by
      rw [← hc'1]
      exact Nat.sub_le _ _
    unfold retCount
    omega

/-- **GB6's conditional words take countably many types.** -/
theorem countable_range_wordType_gb6 (k κ θ : ℝ) (c : BoundaryWord) :
    (range fun r : RecData => wordType k (gb6WordOfRec κ θ c r)).Countable := by
  obtain ⟨H, hH, N, hN⟩ := gb6WordOfRec_bounded κ θ c
  refine (countable_typeSet k hH (N + 1)).mono ?_
  rintro _ ⟨r, rfl⟩
  exact wordType_mem_typeSet k _ (hN r).1 (hN r).2

end InteractingSLE.Supp8.Q3Stop
