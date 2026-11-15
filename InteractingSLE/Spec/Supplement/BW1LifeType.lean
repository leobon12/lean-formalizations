/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopCount

/-!
# Returned stop words take countably many word types

Packet PROVE-BW1-LIFE. The stopped K2 on the canonical relative space (`Supp8.Q3Stop`) runs word type by word type
and needs the conditional words to take countably many types. `Q3Stop.countable_range_wordType_gb6` proves this for
GB6's conditional words `retWord (πχ) χ (stopWord …)`; the same proof works for a stop word returned through
`R(z) = −1/z` with **any** constants `a` (additive) and `l` (lift coefficient), which covers BW1's conditional word
`GW1Laws.cfWordOf κ (stopWord …) = retWord (cfOffset κ − 2π cfCoeff κ) (−cfCoeff κ) (stopWord …)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Life

open Restart Exist.Staged Exist.StagedLaw Supp8.Q3Stop Theorem14.GW2JointKernel Sec7.StripSysField

/-- **Returned stop words have finitely many heights and bounded count** (uniformly in the record). -/
theorem retStopWord_bounded (κ θ a l : ℝ) (c : BoundaryWord) :
    ∃ H : Set ℝ, H.Finite ∧ ∃ N : ℕ, ∀ r : RecData,
      (∀ j, (retWord a l (stopWord κ (c, θ, r))).2.2 j ∈ H) ∧ (retWord a l (stopWord κ (c, θ, r))).1 ≤ N := by
  set n₀ : ℕ := flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0 with hn₀
  set h₀ : ℕ → ℝ := wordHeight κ (flowLineNL c.fn c.jumps 0) (padFL κ θ c.fn c.jumps).2.1
    (padFL κ θ c.fn c.jumps).2.2 (θ * QuantumZipper.chiC κ) with hh₀
  set H₀ : Set ℝ := h₀ '' Iic n₀ with hH₀
  have hH₀f : H₀.Finite := (finite_Iic n₀).image h₀
  set H : Set ℝ := image2 (fun v e => -v + a + l * e) H₀ {-(2 * Real.pi), 0} with hH
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
    change returnData a l c'.fn x ∈ H
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

/-- **Returned stop words take countably many word types.** -/
theorem countable_range_wordType_retStop (k κ θ a l : ℝ) (c : BoundaryWord) :
    (range fun r : RecData => wordType k (retWord a l (stopWord κ (c, θ, r)))).Countable := by
  obtain ⟨H, hH, N, hN⟩ := retStopWord_bounded κ θ a l c
  refine (countable_typeSet k hH (N + 1)).mono ?_
  rintro _ ⟨r, rfl⟩
  exact wordType_mem_typeSet k _ (hN r).1 (hN r).2

end InteractingSLE.Theorem14.BW1Life
