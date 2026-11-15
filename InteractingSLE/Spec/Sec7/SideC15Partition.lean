/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14Offset

/-!
# R90a: the countable partition by the original source branch

PROVE-SIDE-COLLAR2. Branch fibres partition a test measurably. Removing
zero-measure fibres loses only a null set, and almost-sure statements on
the remaining fibres assemble back to the original test.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter

namespace InteractingSLE.Sec7.SideC15

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The part of a test on which its source integer is `k` (R90a). -/
def branchEvent (A : Set Ω) (n : Ω → ℤ) (k : ℤ) : Set Ω :=
  A ∩ n ⁻¹' {k}

omit [MeasurableSpace Ω] in
@[simp] theorem mem_branchEvent {A : Set Ω} {n : Ω → ℤ} {k : ℤ} {ω : Ω} :
    ω ∈ branchEvent A n k ↔ ω ∈ A ∧ n ω = k := Iff.rfl

/-- Branch refinement preserves measurability for the original record. -/
theorem measurableSet_branchEvent {A : Set Ω} {n : Ω → ℤ}
    (hA : MeasurableSet A) (hn : Measurable n) (k : ℤ) :
    MeasurableSet (branchEvent A n k) := hA.inter (hn (measurableSet_singleton k))

omit [MeasurableSpace Ω] in
/-- Every sample belongs to exactly its own branch fibre. -/
theorem iUnion_branchEvent (A : Set Ω) (n : Ω → ℤ) :
    (⋃ k : ℤ, branchEvent A n k) = A := by
  ext ω
  simp only [mem_iUnion, mem_branchEvent]
  exact ⟨fun h => h.choose_spec.1, fun h => ⟨n ω, h, rfl⟩⟩

omit [MeasurableSpace Ω] in
/-- Distinct branch fibres are disjoint. -/
theorem disjoint_branchEvent (A : Set Ω) (n : Ω → ℤ) {k l : ℤ} (h : k ≠ l) :
    Disjoint (branchEvent A n k) (branchEvent A n l) := by
  exact disjoint_left.2 fun _ hk hl => h (hk.2.symm.trans hl.2)

/-- Discarding null branch fibres preserves the test almost surely. No
measurability of the branch is needed for this outer-measure fact. -/
theorem ae_mem_positive_branchEvent (P : Measure Ω) (A : Set Ω) (n : Ω → ℤ) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < P (branchEvent A n (n ω)) := by
  have hall : ∀ k : ℤ, ∀ᵐ ω ∂P,
      ω ∈ branchEvent A n k → 0 < P (branchEvent A n k) := by
    intro k
    by_cases h : P (branchEvent A n k) = 0
    · exact (measure_eq_zero_iff_ae_notMem.1 h).mono fun _ hω hmem => (hω hmem).elim
    · exact ae_of_all _ fun _ _ => bot_lt_iff_ne_bot.2 h
  filter_upwards [ae_all_iff.2 hall] with ω hω hA
  exact hω (n ω) ⟨hA, rfl⟩

/-- Statements on the positive-probability refined tests imply the original
almost-sure statement, and conversely. This retains the original measure. -/
theorem ae_on_branchEvent_iff (P : Measure Ω) (A : Set Ω) (n : Ω → ℤ) (Q : Ω → Prop) :
    (∀ k : ℤ, 0 < P (branchEvent A n k) →
      ∀ᵐ ω ∂P, ω ∈ branchEvent A n k → Q ω) ↔ ∀ᵐ ω ∂P, ω ∈ A → Q ω := by
  constructor
  · intro h
    have hall : ∀ᵐ ω ∂P, ∀ k : ℤ,
        0 < P (branchEvent A n k) → ω ∈ branchEvent A n k → Q ω :=
      ae_all_iff.2 fun k => ae_all_iff.2 fun hk => h k hk
    filter_upwards [hall, ae_mem_positive_branchEvent P A n] with ω hω hp hA
    exact hω (n ω) (hp hA) ⟨hA, rfl⟩
  · intro h k _
    exact h.mono fun _ hω hmem => hω hmem.1

/-- The exact test for whether one common branch suffices. Otherwise no
integer gives an almost-sure constant branch on the original event. -/
theorem branch_constant_or_nonconstant (P : Measure Ω) (A : Set Ω) (n : Ω → ℤ) :
    (∃ k : ℤ, ∀ᵐ ω ∂P, ω ∈ A → n ω = k) ∨
      ∀ k : ℤ, 0 < P (A \ n ⁻¹' {k}) := by
  by_cases h : ∃ k : ℤ, ∀ᵐ ω ∂P, ω ∈ A → n ω = k
  · exact Or.inl h
  · right
    intro k
    apply bot_lt_iff_ne_bot.2
    intro he
    apply h
    refine ⟨k, (measure_eq_zero_iff_ae_notMem.1 he).mono fun ω hω hA => ?_⟩
    by_contra hn
    exact hω ⟨hA, hn⟩

end InteractingSLE.Sec7.SideC15
