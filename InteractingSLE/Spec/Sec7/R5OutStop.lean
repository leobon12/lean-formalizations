/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefStop
import InteractingSLE.Spec.Sec7.HOuterMarkedInf

/-!
# R.5 references before the left stop in outer pockets

PROVE-R5-OUTER. Adapters of `R5RefStop` using the already proved erasure-pocket
clock identities. No reverse visitation of the walls is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open Sec6 PocketTraversal Lemma71C PocketStopMarked PocketStopWallsFin PocketUnionPt
  PocketStopMarked.Outer

section Bounded

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **Before the left stop the relative capacity is below `q`** (bounded pocket). -/
theorem relCap_lt_of_lt_ambTime0 (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) {t : ℝ} (ht : t ∈ Ico τ σ)
    (htT : t < ambTime0 η C τ σ ψ q) : relCap η C τ σ ψ t < q :=
  lt_of_not_ge fun h => (not_le.2 htT) ((PocketStopMarked.Outer.ambTime0_le_iff hP hq0 hq ht).2 h)

/-- **The left stop of a positive live capacity is after the entrance** (bounded pocket). -/
theorem lt_ambTime0 (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) : τ < ambTime0 η C τ σ ψ q := by
  have hm := PocketStopMarked.Outer.ambTime0_mem_Ico hP hq0.le hq
  refine lt_of_le_of_ne hm.1 fun h => ?_
  have h1 := (PocketStopMarked.Outer.ambTime0_le_iff hP hq0.le hq ⟨le_rfl, hP.erase.lt⟩).1 h.symm.le
  rw [PocketStopMarked.Outer.relCap_τ hP] at h1
  linarith

/-- Interior visits accumulate at the left stop from below: every interval `(a, T⁰(q))`
contains a rational interior visit when `q` is positive and live (bounded pocket). -/
theorem exists_rat_visit_lt_ambTime0 (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) {a : ℝ} (ha : a < ambTime0 η C τ σ ψ q) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < ambTime0 η C τ σ ψ q ∧ (s : ℝ) ∈ visitSet η C τ σ := by
  set T := ambTime0 η C τ σ ψ q with hTdef
  have hm : T ∈ Ico τ σ := PocketStopMarked.Outer.ambTime0_mem_Ico hP hq0.le hq
  have hτT : τ < T := lt_ambTime0 hP hq0 hq
  have ha'T : max a τ < T := max_lt ha hτT
  have ha'I : max a τ ∈ Ico τ σ := ⟨le_max_right _ _, ha'T.trans hm.2⟩
  have hlt := relCap_lt_of_lt_ambTime0 hP hq0.le hq ha'I ha'T
  have hge : q ≤ relCap η C τ σ ψ T :=
    (PocketStopMarked.Outer.ambTime0_le_iff hP hq0.le hq hm).1 le_rfl
  have hne : pocketClock η C τ σ (max a τ) ≠ pocketClock η C τ σ T := by
    intro h
    have hc : relCap η C τ σ ψ (max a τ) = relCap η C τ σ ψ T := by simp only [relCap, relTime, h]
    linarith
  have hnd : ¬ Disjoint (Ioo (max a τ) T) (visitSet η C τ σ) := fun hd =>
    hne ((erasureClock_eq_iff hP.erase.isOpen_visitSet ha'T).2 hd)
  obtain ⟨t, ht, htv⟩ := not_disjoint_iff.1 hnd
  obtain ⟨s, hs⟩ := R5Ref.exists_rat_mem (isOpen_Ioo.inter hP.erase.isOpen_visitSet) ⟨t, ht, htv⟩
  exact ⟨s, (le_max_left _ _).trans_lt hs.1.1, hs.1.2, hs.2⟩

/-- **The relative capacity vanishes up to the entrance time** (bounded pocket). -/
theorem relCap_eq_zero_of_le (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {t : ℝ} (htτ : t ≤ τ) :
    relCap η C τ σ ψ t = 0 := by
  rcases htτ.lt_or_eq with h | h
  · have hclk : pocketClock η C τ σ t = pocketClock η C τ σ τ :=
      (erasureClock_eq_iff hP.erase.isOpen_visitSet h).2
        (disjoint_left.2 fun u hu hv => lt_asymm hu.2 hv.1.1)
    rw [← PocketStopMarked.Outer.relCap_τ hP]
    simp only [relCap, relTime, hclk]
  · rw [h]
    exact PocketStopMarked.Outer.relCap_τ hP

end Bounded

section Inf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- Before the left stop the relative capacity is below `q` (seed pocket). -/
theorem relCapInf_lt_of_lt_ambTime0Inf (hP : IsOuterPocketInf W η C y₀ τ ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ)) {t : ℝ} (ht : τ ≤ t)
    (htT : t < ambTime0Inf η C τ ψ q) : relCapInf η C τ ψ t < q :=
  lt_of_not_ge fun h => (not_le.2 htT) 
    ((PocketStopMarked.Outer.ambTime0Inf_le_iff hP hq0 hq ht).2 h)

/-- The left stop of a positive live capacity is after the entrance (seed pocket). -/
theorem lt_ambTime0Inf (hP : IsOuterPocketInf W η C y₀ τ ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ)) : τ < ambTime0Inf η C τ ψ q := by
  refine lt_of_le_of_ne (le_ambTime0Inf' hP ψ q) fun h => ?_
  have h1 := (PocketStopMarked.Outer.ambTime0Inf_le_iff hP hq0.le hq le_rfl).1 h.symm.le
  rw [PocketStopMarked.Outer.relCapInf_τ hP] at h1
  linarith

/-- **Interior visits accumulate at the left stop from below** (pocket opening at the flow seed). -/
theorem exists_rat_visitInf_lt_ambTime0Inf (hP : IsOuterPocketInf W η C y₀ τ ψ)
    {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ)) {a : ℝ} (ha : a < ambTime0Inf η C τ ψ q) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < ambTime0Inf η C τ ψ q ∧ (s : ℝ) ∈ visitSetInf η C τ := by
  set T := ambTime0Inf η C τ ψ q with hTdef
  have hτT : τ < T := lt_ambTime0Inf hP hq0 hq
  have ha'T : max a τ < T := max_lt ha hτT
  have hlt := relCapInf_lt_of_lt_ambTime0Inf hP hq0.le hq (le_max_right a τ) ha'T
  have hge : q ≤ relCapInf η C τ ψ T :=
    (PocketStopMarked.Outer.ambTime0Inf_le_iff hP hq0.le hq hτT.le).1 le_rfl
  have hne : pocketClockInf η C τ (max a τ) ≠ pocketClockInf η C τ T := by
    intro h
    have hc : relCapInf η C τ ψ (max a τ) = relCapInf η C τ ψ T := by
      simp only [relCapInf, relTimeInf, h]
    linarith
  have hnd : ¬ Disjoint (Ioo (max a τ) T) (visitSetInf η C τ) := fun hd =>
    hne ((erasureClock_eq_iff hP.erase.isOpen_visitSet ha'T).2 hd)
  obtain ⟨t, ht, htv⟩ := not_disjoint_iff.1 hnd
  obtain ⟨s, hs⟩ := R5Ref.exists_rat_mem (isOpen_Ioo.inter hP.erase.isOpen_visitSet) ⟨t, ht, htv⟩
  exact ⟨s, (le_max_left _ _).trans_lt hs.1.1, hs.1.2, hs.2⟩

/-- **The relative capacity vanishes up to the entrance time** (pocket opening at the flow seed). -/
theorem relCapInf_eq_zero_of_le (hP : IsOuterPocketInf W η C y₀ τ ψ) {t : ℝ} (htτ : t ≤ τ) :
    relCapInf η C τ ψ t = 0 := by
  rcases htτ.lt_or_eq with h | h
  · have hclk : pocketClockInf η C τ t = pocketClockInf η C τ τ :=
      (erasureClock_eq_iff hP.erase.isOpen_visitSet h).2
        (disjoint_left.2 fun u hu hv => lt_asymm hu.2 hv.1)
    rw [← PocketStopMarked.Outer.relCapInf_τ hP]
    simp only [relCapInf, relTimeInf, hclk]
  · rw [h]
    exact PocketStopMarked.Outer.relCapInf_τ hP

end Inf

end InteractingSLE.Sec7.R5Out
