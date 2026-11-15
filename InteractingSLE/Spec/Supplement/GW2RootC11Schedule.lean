/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC11Capacity
import InteractingSLE.Spec.Supplement.GW2RootTwin

/-!
# The running maximum is the last physical prefix capacity

Packet PROVE-T14-GW2ROOT2. Actual canonical prefixes are nested. Hence the
running maximum defining GW2's schedule capacity is redundant on an
admissible history whose prefix images are bounded and attached.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC11

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
  (s : ℝ≥0) (Θ : Set ℝ) (Q : Set ℝ≥0)

/-- The geometric condition needed at exactly the initial segments of one history.
The list is latest first, so its earlier histories are its suffixes. -/
def HasAttachedHistory (x : ℝ) (e₀ : ℝ × ℝ≥0)
    (xs : List (ℝ × ℝ≥0)) (ω : Ω) : Prop :=
  ∀ ys, ys.IsSuffix xs →
    Bornology.IsBounded (prefixImage hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ ys) ω) ∧
    IsPreconnected (prefixImage hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ ys) ω ∪
      {z : ℂ | z.im ≤ 0})

/-- Collapse of the running maximum, using the proved physical prefix inclusion. -/
theorem schedCap_eq_capOf (x : ℝ) (e₀ : ℝ × ℝ≥0)
    (xs : List (ℝ × ℝ≥0)) (ω : Ω)
    (hadm : SchedAdm b jumps Θ Q (κ := κ) x e₀ xs)
    (hG : HasAttachedHistory hκ h12p βA b jumps c₀ h W' s x e₀ xs ω) :
    schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω =
      capOf (prefixImage hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ xs) ω) := by
  induction xs with
  | nil => simp only [schedCap, capV, ite_eq_left hadm]
  | cons y xs ih =>
    have ht : xs.IsSuffix (y :: xs) := ⟨[y], rfl⟩
    have hprev := hG xs ht
    have hlast := hG (y :: xs) List.suffix_rfl
    have ih' := ih (SchedAdm.of_cons b jumps Θ Q hadm)
      (fun ys hys => hG ys (hys.trans ht))
    rw [schedCap, ih', capV, ite_eq_left hadm]
    apply max_eq_right
    apply capOf_mono _ hprev.1 hprev.2 hlast.1 hlast.2
    rw [schedOf_cons]
    exact prefixImage_subset_append hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ xs) y ω

section Root

variable (ζ' : Ω → ℝ≥0∞)

/-- The actual prefix image used by the repaired scaled capacity. -/
abbrev rootImage (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) (ω : Ω) : Set ℂ :=
  prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s
    (rootPt r.1) (schedOf (rootEntry r.1) (entryList l)) ω

/-- On an attached admissible history, `capR` is exactly its final image's scaled half capacity. -/
theorem capR_eq_scaled_capOf (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) (ω : Ω)
    (hadm : SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) (entryList l))
    (hG : HasAttachedHistory hκ h12p βA b jumps c₀ h (regW s W' ζ') s
      (rootPt r.1) (rootEntry r.1) (entryList l) ω) :
    capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω =
      4 ^ r.2 * capOf (rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r l ω) := by
  exact congrArg (fun v : ℝ => 4 ^ r.2 * v)
    (schedCap_eq_capOf hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q
      (rootPt r.1) (rootEntry r.1) (entryList l) ω hadm hG)

/-- Inclusion of the actual repaired root images under an entry extension. -/
theorem rootImage_subset_cons (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (e : EntryIdx Θ Q) (ω : Ω) :
    rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r l ω ⊆
      rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r (e :: l) ω := by
  unfold rootImage
  rw [entryList_cons, schedOf_cons]
  exact prefixImage_subset_append hκ h12p βA b jumps c₀ h (regW s W' ζ') s _ _ _ ω

end Root

end InteractingSLE.Theorem14.GW2TipSystem.RootC11
