/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TreeExtractPaths

/-!
# Measurable enumeration of available nodes and their closed descendant cones

Unavailable deterministic schedules duplicate the first available node. Thus
every selected node is available whenever at least one is, and every available
node occurs. Inactive descendant portions contribute only the root to its cone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology

namespace InteractingSLE.Sec5.Prop513TreeExtract

def AvailablePred {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) (k : ℕ) : Prop :=
  ω ∈ A k ∨ ∀ j, ω ∉ A j

theorem exists_availablePred {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) :
    ∃ k, AvailablePred A ω k := by
  by_cases h : ∃ k, ω ∈ A k
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr fun j hj => h ⟨j, hj⟩⟩

def firstAvailable {Ω : Type*} (A : ℕ → Set Ω) (ω : Ω) : ℕ := by
  classical
  exact Nat.find (exists_availablePred A ω)

theorem measurable_firstAvailable {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet[𝒢] (A n)) :
    Measurable[𝒢] (firstAvailable A) := by
  classical
  refine measurable_find (p := AvailablePred A) (exists_availablePred A) fun k => ?_
  simp only [AvailablePred, ofPred_or, ofPred_forall]
  exact (hA k).union (MeasurableSet.iInter fun j => (hA j).compl)

theorem firstAvailable_mem {Ω : Type*} {A : ℕ → Set Ω} {ω : Ω}
    (h : ∃ n, ω ∈ A n) : ω ∈ A (firstAvailable A ω) := by
  classical
  rcases Nat.find_spec (exists_availablePred A ω) with ha | hn
  · exact ha
  · obtain ⟨n, hm⟩ := h
    exact False.elim (hn n hm)

def availableIndex {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ := by
  classical
  exact if ω ∈ A n then n else firstAvailable A ω

theorem measurable_availableIndex {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet[𝒢] (A n)) (n : ℕ) :
    Measurable[𝒢] (availableIndex A n) := by
  classical
  exact Measurable.ite (hA n) measurable_const (measurable_firstAvailable hA)

theorem availableIndex_eq_self {Ω : Type*} {A : ℕ → Set Ω} {n : ℕ} {ω : Ω}
    (h : ω ∈ A n) : availableIndex A n ω = n := by
  classical
  exact ite_eq_left h

theorem availableIndex_mem {Ω : Type*} {A : ℕ → Set Ω} {ω : Ω}
    (h : ∃ n, ω ∈ A n) (n : ℕ) : ω ∈ A (availableIndex A n ω) := by
  classical
  by_cases hn : ω ∈ A n
  · rw [availableIndex_eq_self hn]
    exact hn
  · simpa only [availableIndex, hn, ite_false] using firstAvailable_mem h

/-- Root path followed by the available closed descendant portions. -/
def conePath {Ω : Type*} (ξ : ℕ → Ω → ℝ → ℂ) (A : ℕ → Set Ω)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → Ω → ℝ → ℂ
  | 0, ω, _ => ξ n ω (τ n)
  | m + 1, ω, t => by
      classical
      exact if ω ∈ A (d n m) then ξ (d n m) ω (τ n + (τ (d n m) - τ n) * t)
        else ξ n ω (τ n)

def availableCone {Ω : Type*} (ξ : ℕ → Ω → ℝ → ℂ) (A : ℕ → Set Ω)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) (ω : Ω) : Set ℂ :=
  closure (⋃ m, conePath ξ A τ d n m ω '' Icc 0 1)

theorem measurable_availableCone {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {ξ : ℕ → Ω → ℝ → ℂ} {A : ℕ → Set Ω}
    (hm : ∀ n t, Measurable[𝒢] fun ω => ξ n ω t)
    (hc : ∀ n ω, Continuous (ξ n ω)) (hA : ∀ n, MeasurableSet[𝒢] (A n))
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) :
    @Measurable Ω (Set ℂ) 𝒢 hittingSigma (availableCone ξ A τ d n) := by
  classical
  refine measurable_closure_iUnion_image (γ := conePath ξ A τ d n) ?_ ?_
  · rintro (_ | m) t
    · exact hm n (τ n)
    · exact Measurable.ite (hA (d n m)) (hm (d n m) _) (hm n (τ n))
  · rintro (_ | m) ω
    · exact continuousOn_const
    · change ContinuousOn (fun t => if ω ∈ A (d n m) then
        ξ (d n m) ω (τ n + (τ (d n m) - τ n) * t) else ξ n ω (τ n)) (Icc 0 1)
      by_cases ha : ω ∈ A (d n m)
      · simp only [ha, ite_true]
        exact ((hc (d n m) ω).comp
          (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
      · simp only [ha, ite_false]
        exact continuousOn_const

/-- Selecting the available nodes preserves measurability of their positions. -/
theorem measurable_selectedNode {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {ξ : ℕ → Ω → ℝ → ℂ} {A : ℕ → Set Ω}
    (hm : ∀ n t, Measurable[𝒢] fun ω => ξ n ω t)
    (hA : ∀ n, MeasurableSet[𝒢] (A n)) (τ : ℕ → ℝ) (n : ℕ) :
    Measurable[𝒢] fun ω => ξ (availableIndex A n ω) ω (τ (availableIndex A n ω)) :=
  measurable_apply_index (fun j => hm j (τ j)) (measurable_availableIndex hA n)

/-- The cones of the selected available roots are hitting-measurable. -/
theorem measurable_selectedCone {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {ξ : ℕ → Ω → ℝ → ℂ} {A : ℕ → Set Ω}
    (hm : ∀ n t, Measurable[𝒢] fun ω => ξ n ω t)
    (hc : ∀ n ω, Continuous (ξ n ω)) (hA : ∀ n, MeasurableSet[𝒢] (A n))
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) :
    @Measurable Ω (Set ℂ) 𝒢 hittingSigma
      (fun ω => availableCone ξ A τ d (availableIndex A n ω) ω) :=
  @measurable_apply_index Ω 𝒢 (Set ℂ) hittingSigma
    (availableCone ξ A τ d) (fun j => measurable_availableCone hm hc hA τ d j)
    (availableIndex A n) (measurable_availableIndex hA n)

end InteractingSLE.Sec5.Prop513TreeExtract
