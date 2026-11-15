/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedPath
import InteractingSLE.Spec.Sec7.PocketStopMarkedPathInf

/-!
# Lemma R.5's references: interior visits before the left stop `T⁰(q)`

Packet PROVE-R5-REFCHART. Proof of Lemma R.5 (spec p. 475): "Since `p ≠ η(T)`, choose an original rational time
`s < T` … such that the final ambient range `η([s, T])` avoids a physical ball". The rational times used as
references must be interior visits of the pocket (their relative chart is then the chart of `C ∖ R_s`). This file
proves, for a reverse pocket (bounded, or opening at the flow seed), that interior visits accumulate at the LEFT end
`T⁰(q)` of the erasure fibre of every positive live relative capacity `q` (ruling R67), and that before `T⁰(q)` the
relative capacity is below `q`:

* `relCap_lt_of_lt_ambTime0`, `lt_ambTime0`, **`exists_rat_visit_lt_ambTime0`** (bounded pocket);
* `relCap_eq_zero_of_le`: the relative capacity vanishes up to the entrance time;
* the same for the pocket opening at the flow seed (`…Inf`).

Pure pocket geometry; ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Ref

open Sec6 PocketTraversal Lemma71C PocketStopMarked PocketStopWallsFin PocketUnionPt

/-- A nonempty open set of reals contains a rational. -/
theorem exists_rat_mem {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty) : ∃ s : ℚ, (s : ℝ) ∈ U :=
  Rat.denseRange_cast.exists_mem_open hU hne

section Bounded

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **Before the left stop the relative capacity is below `q`** (bounded pocket). -/
theorem relCap_lt_of_lt_ambTime0 (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) {t : ℝ} (ht : t ∈ Ico τ σ)
    (htT : t < ambTime0 η C τ σ ψ q) : relCap η C τ σ ψ t < q :=
  lt_of_not_ge fun h => (not_le.2 htT) ((ambTime0_le_iff hP hAC hψ hq0 hq ht).2 h)

/-- **The left stop of a positive live capacity is after the entrance** (bounded pocket). -/
theorem lt_ambTime0 (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) : τ < ambTime0 η C τ σ ψ q := by
  have hm := ambTime0_mem_Ico hP hAC hψ hq0.le hq
  refine lt_of_le_of_ne hm.1 fun h => ?_
  have h1 := (ambTime0_le_iff hP hAC hψ hq0.le hq ⟨le_rfl, hP.τ_lt_σ⟩).1 h.symm.le
  rw [relCap_τ hP hAC hψ] at h1
  linarith

/-- **Interior visits accumulate at the left stop from below** (bounded pocket): for a positive live relative
capacity `q`, every interval `(a, T⁰(q))` contains a rational interior visit. -/
theorem exists_rat_visit_lt_ambTime0 (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) {a : ℝ} (ha : a < ambTime0 η C τ σ ψ q) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < ambTime0 η C τ σ ψ q ∧ (s : ℝ) ∈ visitSet η C τ σ := by
  set T := ambTime0 η C τ σ ψ q with hTdef
  have hm : T ∈ Ico τ σ := ambTime0_mem_Ico hP hAC hψ hq0.le hq
  have hτT : τ < T := lt_ambTime0 hP hAC hψ hq0 hq
  have ha'T : max a τ < T := max_lt ha hτT
  have ha'I : max a τ ∈ Ico τ σ := ⟨le_max_right _ _, ha'T.trans hm.2⟩
  have hlt := relCap_lt_of_lt_ambTime0 hP hAC hψ hq0.le hq ha'I ha'T
  have hge : q ≤ relCap η C τ σ ψ T := (ambTime0_le_iff hP hAC hψ hq0.le hq hm).1 le_rfl
  have hne : pocketClock η C τ σ (max a τ) ≠ pocketClock η C τ σ T := by
    intro h
    have hc : relCap η C τ σ ψ (max a τ) = relCap η C τ σ ψ T := by simp only [relCap, relTime, h]
    linarith
  have hnd : ¬ Disjoint (Ioo (max a τ) T) (visitSet η C τ σ) := fun hd =>
    hne ((erasureClock_eq_iff hP.isOpen_visitSet ha'T).2 hd)
  obtain ⟨t, ht, htv⟩ := not_disjoint_iff.1 hnd
  obtain ⟨s, hs⟩ := exists_rat_mem (isOpen_Ioo.inter hP.isOpen_visitSet) ⟨t, ht, htv⟩
  exact ⟨s, (le_max_left _ _).trans_lt hs.1.1, hs.1.2, hs.2⟩

/-- **The relative capacity vanishes up to the entrance time** (bounded pocket). -/
theorem relCap_eq_zero_of_le (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {t : ℝ} (htτ : t ≤ τ) :
    relCap η C τ σ ψ t = 0 := by
  rcases htτ.lt_or_eq with h | h
  · have hclk : pocketClock η C τ σ t = pocketClock η C τ σ τ :=
      (erasureClock_eq_iff hP.isOpen_visitSet h).2
        (disjoint_left.2 fun u hu hv => lt_asymm hu.2 hv.1.1)
    rw [← relCap_τ hP hAC hψ]
    simp only [relCap, relTime, hclk]
  · rw [h]
    exact relCap_τ hP hAC hψ

end Bounded

section Inf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- **Before the left stop the relative capacity is below `q`** (pocket opening at the flow seed). -/
theorem relCapInf_lt_of_lt_ambTime0Inf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ)) {t : ℝ} (ht : τ ≤ t)
    (htT : t < ambTime0Inf η C τ ψ q) : relCapInf η C τ ψ t < q :=
  lt_of_not_ge fun h => (not_le.2 htT) ((ambTime0Inf_le_iff hP hAC hψ hq0 hq ht).2 h)

/-- **The left stop of a positive live capacity is after the entrance** (pocket opening at the flow seed). -/
theorem lt_ambTime0Inf (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ)) : τ < ambTime0Inf η C τ ψ q := by
  refine lt_of_le_of_ne (le_ambTime0Inf hP hAC ψ q) fun h => ?_
  have h1 := (ambTime0Inf_le_iff hP hAC hψ hq0.le hq le_rfl).1 h.symm.le
  rw [relCapInf_τ hP hAC hψ] at h1
  linarith

/-- **Interior visits accumulate at the left stop from below** (pocket opening at the flow seed). -/
theorem exists_rat_visitInf_lt_ambTime0Inf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {q : ℝ} (hq0 : 0 < q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ)) {a : ℝ} (ha : a < ambTime0Inf η C τ ψ q) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < ambTime0Inf η C τ ψ q ∧ (s : ℝ) ∈ visitSetInf η C τ := by
  set T := ambTime0Inf η C τ ψ q with hTdef
  have hτT : τ < T := lt_ambTime0Inf hP hAC hψ hq0 hq
  have ha'T : max a τ < T := max_lt ha hτT
  have hlt := relCapInf_lt_of_lt_ambTime0Inf hP hAC hψ hq0.le hq (le_max_right a τ) ha'T
  have hge : q ≤ relCapInf η C τ ψ T := (ambTime0Inf_le_iff hP hAC hψ hq0.le hq hτT.le).1 le_rfl
  have hne : pocketClockInf η C τ (max a τ) ≠ pocketClockInf η C τ T := by
    intro h
    have hc : relCapInf η C τ ψ (max a τ) = relCapInf η C τ ψ T := by simp only [relCapInf, relTimeInf, h]
    linarith
  have hnd : ¬ Disjoint (Ioo (max a τ) T) (visitSetInf η C τ) := fun hd =>
    hne ((erasureClock_eq_iff hP.isOpen_visitSet ha'T).2 hd)
  obtain ⟨t, ht, htv⟩ := not_disjoint_iff.1 hnd
  obtain ⟨s, hs⟩ := exists_rat_mem (isOpen_Ioo.inter hP.isOpen_visitSet) ⟨t, ht, htv⟩
  exact ⟨s, (le_max_left _ _).trans_lt hs.1.1, hs.1.2, hs.2⟩

/-- **The relative capacity vanishes up to the entrance time** (pocket opening at the flow seed). -/
theorem relCapInf_eq_zero_of_le (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {t : ℝ} (htτ : t ≤ τ) :
    relCapInf η C τ ψ t = 0 := by
  rcases htτ.lt_or_eq with h | h
  · have hclk : pocketClockInf η C τ t = pocketClockInf η C τ τ :=
      (erasureClock_eq_iff hP.isOpen_visitSet h).2
        (disjoint_left.2 fun u hu hv => lt_asymm hu.2 hv.1)
    rw [← relCapInf_τ hP hAC hψ]
    simp only [relCapInf, relTimeInf, hclk]
  · rw [h]
    exact relCapInf_τ hP hAC hψ

end Inf

end InteractingSLE.Sec7.R5Ref
