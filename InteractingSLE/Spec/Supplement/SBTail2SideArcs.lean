/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContArc

/-! # Closed real connectors and their measurable dense codes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Side

open Exist.Staged Exist.StagedLaw GW2aCont

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem isClosed_newArc_contStep (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    IsClosed (newArc s (ExplState.contStep κ b jumps s vStop pref)) := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s vStop pref with
    e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e]
  · rw [newArc_of_arcs_eq (s := s) (s' := s) rfl]
    exact isClosed_empty
  · rw [newArc_of_arcs_eq (s := s) (s' := setDead s) rfl]
    exact isClosed_empty
  · rw [newArc_moveAlong]
    cases r <;> exact isClosed_Icc
  · rw [newArc_moveToEnd]
    cases r
    · exact isClosed_Iic
    · exact isClosed_Ici

/-- Every recorded real connector is closed, without any regularity premise. -/
theorem isClosed_arcAt (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    IsClosed (arcAt κ b jumps spec D k) := by
  rw [arcAt_eq_newArc, run_succ]
  cases hk : spec.2.2[k]? with
  | none =>
    rw [newArc_of_arcs_eq (s := _) (s' := _) rfl]
    exact isClosed_empty
  | some ins =>
    simp only
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · change IsClosed (newArc (ExplState.run κ b jumps spec D k)
        (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t))
      rw [newArc_of_arcs_eq (arcs_flowStep (κ := κ) (b := b) spec.2.1 _ k (D k) θ t)]
      exact isClosed_empty
    · exact isClosed_newArc_contStep _ none pref
    · exact isClosed_newArc_contStep _ (some v) pref

/-- Rational membership of a connector supplies a full-plane dense code.
The root provides a harmless value when a rational point is absent. -/
theorem exists_measurable_arc_dense_code (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {Ω : Type u} [MeasurableSpace Ω] {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∃ F : ℕ → Ω → Unit ⊕ ℚ → ℂ, (∀ j i, Measurable fun ω => F j ω i) ∧ ∀ ω j,
      closure (range (F j ω)) = {(spec.1 : ℂ)} ∪
        ((↑) : ℝ → ℂ) '' arcAt κ b jumps spec (fun i => E i ω) j := by
  classical
  let F : ℕ → Ω → Unit ⊕ ℚ → ℂ := fun j ω => Sum.elim (fun _ => (spec.1 : ℂ))
    (fun q => if (q : ℝ) ∈ arcAt κ b jumps spec (fun i => E i ω) j then ((q : ℝ) : ℂ) else spec.1)
  refine ⟨F, ?_, ?_⟩
  · intro j i
    cases i with
    | inl _ => exact measurable_const
    | inr q =>
      exact Measurable.ite (measurableSet_mem_arcAt hb spec hEm hreg j q)
        measurable_const measurable_const
  · intro ω j
    have hc : IsClosed (((↑) : ℝ → ℂ) '' arcAt κ b jumps spec (fun i => E i ω) j) :=
      Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap _ (isClosed_arcAt spec _ j)
    refine subset_antisymm (closure_minimal ?_ (isClosed_singleton.union hc)) (union_subset ?_ ?_)
    · rintro _ ⟨i, rfl⟩
      cases i with
      | inl _ => exact Or.inl rfl
      | inr q =>
        change (if (q : ℝ) ∈ arcAt κ b jumps spec (fun i => E i ω) j then ((q : ℝ) : ℂ) else spec.1) ∈ _
        split_ifs with hq
        · exact Or.inr ⟨q, hq, rfl⟩
        · exact Or.inl rfl
    · rintro _ rfl
      exact subset_closure ⟨Sum.inl (), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxcl := arcAt_subset_closure_rat (κ := κ) (b := b) (jumps := jumps) spec
        (fun i => E i ω) j hx
      have hs : ((↑) : ℝ → ℂ) '' (arcAt κ b jumps spec (fun i => E i ω) j ∩
          range ((↑) : ℚ → ℝ)) ⊆ range (F j ω) := by
        rintro _ ⟨_, ⟨hq, q, rfl⟩, rfl⟩
        exact ⟨Sum.inr q, ite_eq_left hq⟩
      exact closure_mono hs (mem_closure_image Complex.continuous_ofReal.continuousAt hxcl)

end InteractingSLE.Theorem14.SB.Side
