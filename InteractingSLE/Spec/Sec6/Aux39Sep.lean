/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Arc

/-!
# The exterior-face separation of the fixed-chart gate lemma

Lemma 1.3 of the ZTip-elimination note (ruling R41;
`source/external/AstraIG1/ig1_ztip_elimination.txt`
L140–L186), finite-junction case: "the union of the two selected arms is a crosscut from `q₁` to
`q₂`. Its bounded side is `F`; its other side is split by the third arm from `z` to infinity. The
crosscut form of Jordan separation gives two exterior faces `U₁, U₂`. The gate `qᵢ` is incident to
`Uᵢ`. Away from the removed incoming tree and infinity, their closures are disjoint ... A connected
image cannot join the two gates."

This file proves the separation in an abstract form, from the Jordan curve theorem and
Janiszewski's theorem (QuantumZipper `CA.Topo.janiszewski`). Three Jordan curves in `ℍ̄` are given:
the face boundary `Γ` and two exterior curves `Ξᵢ = Sᵢ ∪ T₃` (in the application `T₃` is the
truncated third arm and `Sᵢ` the rest of `Ξᵢ`: the arm `i`, a real segment and a circular arc of
radius `R`). The exterior faces are `Uᵢ = innerSide Ξᵢ`.

## Main result

* `false_of_isPreconnected_gates`: a preconnected set in `ℍ̄ ∩ ball 0 R` avoiding `T₃`, the inner
  side of `Γ` and `Γ \ (Ξ₁ ∪ Ξ₂)` cannot contain both gates.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

/-- The open upper half-disc is a clopen piece of the complement of its boundary. -/
theorem connectedComponentIn_subset_halfDisc {K : Set ℂ} {R : ℝ}
    (hK : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ R → z ∉ ball 0 R ∩ H → z ∈ K) {w : ℂ}
    (hw : w ∈ ball 0 R ∩ H) (hwK : w ∉ K) : connectedComponentIn Kᶜ w ⊆ ball 0 R ∩ H := by
  have hu : IsOpen (ball (0 : ℂ) R ∩ H) := isOpen_ball.inter QuantumZipper.isOpen_H
  set V : Set ℂ := {z : ℂ | R < ‖z‖} ∪ {z : ℂ | z.im < 0} with hV
  have hv : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).union (isOpen_lt Complex.continuous_im
      continuous_const)
  have hdisj : Disjoint (ball (0 : ℂ) R ∩ H) V := by
    rw [Set.disjoint_left]
    rintro z ⟨hzb, hzH⟩ (hz | hz)
    · rw [mem_ball, dist_zero_right] at hzb
      exact lt_asymm hzb hz
    · have : (0 : ℝ) < z.im := hzH
      exact lt_asymm this hz
  have hcov : Kᶜ ⊆ (ball (0 : ℂ) R ∩ H) ∪ V := by
    intro z hzK
    by_cases h1 : z.im < 0
    · exact Or.inr (Or.inr h1)
    by_cases h2 : R < ‖z‖
    · exact Or.inr (Or.inl h2)
    push Not at h1 h2
    by_contra hz
    exact hzK (hK z h1 h2 fun hz' => hz (Or.inl hz'))
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hu hv hdisj
    ((connectedComponentIn_subset _ _).trans hcov)
    ⟨w, mem_connectedComponentIn hwK, hw⟩

theorem isCompact_of_isJordanCurve {J : Set ℂ} (hJ : LQGMetric.JordanMap.IsJordanCurve J) :
    IsCompact J := by
  obtain ⟨γ, hγc, -, rfl⟩ := hJ
  exact (isCompact_sphere 0 1).image_of_continuousOn hγc

/-- **The exterior-face separation** (abstract form of Lemma 1.3's planar step). Let
`Γ, Ξ₁, Ξ₂ ⊆ ℍ̄`
be Jordan curves with `Ξᵢ = Sᵢ ∪ T₃`, where `Sᵢ` is preconnected, contains the real gate `xᵢ` and
misses the other exterior curve. Suppose `Γ ∩ Ξ₁` and `(Γ ∪ Ξ₁) ∩ Ξ₂` are preconnected and the three
curves cover the boundary of the upper half-disc of radius `R`. Then no preconnected subset of
`ℍ̄ ∩ ball 0 R` which avoids `T₃`, the inner side of `Γ` and `Γ \ (Ξ₁ ∪ Ξ₂)` contains both gates. -/
theorem false_of_isPreconnected_gates {Γ Ξ₁ Ξ₂ S₁ S₂ T₃ P : Set ℂ} {x₁ x₂ R : ℝ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΞ₁ : LQGMetric.JordanMap.IsJordanCurve Ξ₁)
    (hΞ₂ : LQGMetric.JordanMap.IsJordanCurve Ξ₂) (hΓH : Γ ⊆ Hbar) (hΞ₁H : Ξ₁ ⊆ Hbar)
    (hΞ₂H : Ξ₂ ⊆ Hbar) (hΞ₁eq : Ξ₁ = S₁ ∪ T₃) (hΞ₂eq : Ξ₂ = S₂ ∪ T₃)
    (hS₁ : IsPreconnected S₁) (hS₂ : IsPreconnected S₂) (hx₁S : (x₁ : ℂ) ∈ S₁)
    (hx₂S : (x₂ : ℂ) ∈ S₂) (hS₁Ξ₂ : Disjoint S₁ Ξ₂) (hS₂Ξ₁ : Disjoint S₂ Ξ₁)
    (hΓΞ₁ : IsPreconnected (Γ ∩ Ξ₁)) (hΓΞ₁Ξ₂ : IsPreconnected ((Γ ∪ Ξ₁) ∩ Ξ₂))
    (hcover : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ R → z ∉ ball 0 R ∩ H → z ∈ Γ ∪ Ξ₁ ∪ Ξ₂)
    (hP : IsPreconnected P) (hPB : P ⊆ ball 0 R) (hPH : P ⊆ Hbar) (hx₁P : (x₁ : ℂ) ∈ P)
    (hx₂P : (x₂ : ℂ) ∈ P) (hPT : Disjoint P T₃) (hPF : Disjoint P (innerSide Γ))
    (hPΓ : Disjoint P (Γ \ (Ξ₁ ∪ Ξ₂))) : False := by
  obtain ⟨-, -, hfrI₁, -, -, hO₁o, -, hI₁p, -⟩ := jordan_sides hΞ₁ hΞ₁H
  obtain ⟨-, -, hfrI₂, -, -, hO₂o, -, hI₂p, -⟩ := jordan_sides hΞ₂ hΞ₂H
  have hΓc := isCompact_of_isJordanCurve hΓ
  have hΞ₁c := isCompact_of_isJordanCurve hΞ₁
  have hΞ₂c := isCompact_of_isJordanCurve hΞ₂
  -- `Sᵢ` lies on the outer side of the other exterior curve
  have hx₁O₂ : (x₁ : ℂ) ∈ outerSide Ξ₂ :=
    ofReal_mem_outerSide hΞ₂ hΞ₂H fun h => Set.disjoint_left.1 hS₁Ξ₂ hx₁S h
  have hx₂O₁ : (x₂ : ℂ) ∈ outerSide Ξ₁ :=
    ofReal_mem_outerSide hΞ₁ hΞ₁H fun h => Set.disjoint_left.1 hS₂Ξ₁ hx₂S h
  have hS₁O₂ : S₁ ⊆ outerSide Ξ₂ := by
    have h1 := hS₁.subset_connectedComponentIn hx₁S fun z hz hzΞ =>
      Set.disjoint_left.1 hS₁Ξ₂ hz hzΞ
    rw [outerSide, connectedComponentIn_eq hx₁O₂]; exact h1
  have hS₂O₁ : S₂ ⊆ outerSide Ξ₁ := by
    have h1 := hS₂.subset_connectedComponentIn hx₂S fun z hz hzΞ =>
      Set.disjoint_left.1 hS₂Ξ₁ hz hzΞ
    rw [outerSide, connectedComponentIn_eq hx₂O₁]; exact h1
  -- the two exterior faces: `U₁ ⊆ O₂`, `U₂ ⊆ O₁`
  have hI₁O₂ : innerSide Ξ₁ ⊆ outerSide Ξ₂ := by
    have hx₁fr : (x₁ : ℂ) ∈ frontier (innerSide Ξ₁) := by
      rw [hfrI₁, hΞ₁eq]; exact Or.inl hx₁S
    obtain ⟨p, hpO, hpI⟩ :=
      mem_closure_iff.1 (frontier_subset_closure hx₁fr) _ hO₂o hx₁O₂
    have hI₁Ξ₂ : innerSide Ξ₁ ⊆ Ξ₂ᶜ := by
      intro z hz hzΞ
      rw [hΞ₂eq] at hzΞ
      rcases hzΞ with h | h
      · exact disjoint_innerSide_outerSide.le_bot ⟨hz, hS₂O₁ h⟩
      · exact innerSide_subset_compl hz (by rw [hΞ₁eq]; exact Or.inr h)
    have := hI₁p.subset_connectedComponentIn hpI hI₁Ξ₂
    rw [outerSide, connectedComponentIn_eq hpO]; exact this
  have hI₂O₁ : innerSide Ξ₂ ⊆ outerSide Ξ₁ := by
    have hx₂fr : (x₂ : ℂ) ∈ frontier (innerSide Ξ₂) := by
      rw [hfrI₂, hΞ₂eq]; exact Or.inl hx₂S
    obtain ⟨p, hpO, hpI⟩ :=
      mem_closure_iff.1 (frontier_subset_closure hx₂fr) _ hO₁o hx₂O₁
    have hI₂Ξ₁ : innerSide Ξ₂ ⊆ Ξ₁ᶜ := by
      intro z hz hzΞ
      rw [hΞ₁eq] at hzΞ
      rcases hzΞ with h | h
      · exact disjoint_innerSide_outerSide.le_bot ⟨hz, hS₁O₂ h⟩
      · exact innerSide_subset_compl hz (by rw [hΞ₂eq]; exact Or.inr h)
    have := hI₂p.subset_connectedComponentIn hpI hI₂Ξ₁
    rw [outerSide, connectedComponentIn_eq hpO]; exact this
  have hclI₁ : closure (innerSide Ξ₁) = innerSide Ξ₁ ∪ Ξ₁ := by
    rw [closure_eq_self_union_frontier, hfrI₁]
  have hclI₂ : closure (innerSide Ξ₂) = innerSide Ξ₂ ∪ Ξ₂ := by
    rw [closure_eq_self_union_frontier, hfrI₂]
  -- the closures of the two exterior faces are disjoint on `P`
  have hdisjP : ∀ w ∈ P, w ∈ closure (innerSide Ξ₁) → w ∈ closure (innerSide Ξ₂) → False := by
    intro w hwP h1 h2
    rw [hclI₁] at h1
    rw [hclI₂] at h2
    have hwT : w ∉ T₃ := fun h => Set.disjoint_left.1 hPT hwP h
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact disjoint_innerSide_outerSide.le_bot ⟨h2, hI₁O₂ h1⟩
    · rw [hΞ₂eq] at h2
      rcases h2 with h2 | h2
      · exact disjoint_innerSide_outerSide.le_bot ⟨h1, hS₂O₁ h2⟩
      · exact hwT h2
    · rw [hΞ₁eq] at h1
      rcases h1 with h1 | h1
      · exact disjoint_innerSide_outerSide.le_bot ⟨h2, hS₁O₂ h1⟩
      · exact hwT h1
    · rw [hΞ₁eq] at h1
      rcases h1 with h1 | h1
      · exact outerSide_subset_compl (hS₁O₂ h1) h2
      · exact hwT h1
  -- every point of `P` lies in the closure of an exterior face (Janiszewski twice)
  have hcov : P ⊆ closure (innerSide Ξ₁) ∪ closure (innerSide Ξ₂) := by
    intro w hwP
    by_contra hw
    rw [hclI₁, hclI₂] at hw
    simp only [mem_union, not_or] at hw
    obtain ⟨⟨hwI₁, hwΞ₁⟩, hwI₂, hwΞ₂⟩ := hw
    have hwΓ : w ∉ Γ := fun h =>
      Set.disjoint_left.1 hPΓ hwP ⟨h, by simp only [mem_union, not_or]; exact ⟨hwΞ₁, hwΞ₂⟩⟩
    have hwOΓ : w ∈ outerSide Γ := by
      have h : w ∈ Γᶜ := hwΓ
      rw [compl_eq_innerSide_union_outerSide] at h
      exact h.resolve_left fun h' => Set.disjoint_left.1 hPF hwP h'
    have hwO₁ : w ∈ outerSide Ξ₁ := by
      have h : w ∈ Ξ₁ᶜ := hwΞ₁
      rw [compl_eq_innerSide_union_outerSide] at h
      exact h.resolve_left hwI₁
    have hwO₂ : w ∈ outerSide Ξ₂ := by
      have h : w ∈ Ξ₂ᶜ := hwΞ₂
      rw [compl_eq_innerSide_union_outerSide] at h
      exact h.resolve_left hwI₂
    have hnIΓ : (-I : ℂ) ∉ Γ := lowerHalf_subset_compl hΓH neg_I_im
    have hnIΞ₁ : (-I : ℂ) ∉ Ξ₁ := lowerHalf_subset_compl hΞ₁H neg_I_im
    have hnIΞ₂ : (-I : ℂ) ∉ Ξ₂ := lowerHalf_subset_compl hΞ₂H neg_I_im
    have j1 := QuantumZipper.CA.Topo.janiszewski hΓc hΞ₁c hΓΞ₁ (a := w) (b := -I)
      (by simp only [mem_union, not_or]; exact ⟨hwΓ, hwΞ₁⟩)
      (by simp only [mem_union, not_or]; exact ⟨hnIΓ, hnIΞ₁⟩)
      (neg_I_mem_of_mem_outerSide hwOΓ) (neg_I_mem_of_mem_outerSide hwO₁)
    have j2 := QuantumZipper.CA.Topo.janiszewski (hΓc.union hΞ₁c) hΞ₂c hΓΞ₁Ξ₂ (a := w) (b := -I)
      (by simp only [mem_union, not_or]; exact ⟨⟨hwΓ, hwΞ₁⟩, hwΞ₂⟩)
      (by simp only [mem_union, not_or]; exact ⟨⟨hnIΓ, hnIΞ₁⟩, hnIΞ₂⟩) j1
      (neg_I_mem_of_mem_outerSide hwO₂)
    have hwnot : w ∉ Γ ∪ Ξ₁ ∪ Ξ₂ := by
      simp only [mem_union, not_or]; exact ⟨⟨hwΓ, hwΞ₁⟩, hwΞ₂⟩
    have hwB : w ∈ ball 0 R ∩ H := by
      refine ⟨hPB hwP, ?_⟩
      by_contra hwH
      exact hwnot (hcover w (hPH hwP) (le_of_lt (mem_ball_zero_iff.1 (hPB hwP)))
        fun h => hwH h.2)
    have hsub := connectedComponentIn_subset_halfDisc hcover hwB hwnot
    have hH := (hsub j2).2
    have : (0 : ℝ) < (-I : ℂ).im := hH
    simp only [neg_im, I_im] at this
    linarith
  have hx₁cl : (x₁ : ℂ) ∈ closure (innerSide Ξ₁) := by
    rw [hclI₁, hΞ₁eq]; exact Or.inr (Or.inl hx₁S)
  have hx₂cl : (x₂ : ℂ) ∈ closure (innerSide Ξ₂) := by
    rw [hclI₂, hΞ₂eq]; exact Or.inr (Or.inl hx₂S)
  obtain ⟨w, hwP, hw1, hw2⟩ := isPreconnected_closed_iff.1 hP _ _ isClosed_closure isClosed_closure
    hcov ⟨_, hx₁P, hx₁cl⟩ ⟨_, hx₂P, hx₂cl⟩
  exact hdisjP w hwP hw1 hw2

end InteractingSLE.Sec6
