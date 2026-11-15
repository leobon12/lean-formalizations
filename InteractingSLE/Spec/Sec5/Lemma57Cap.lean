/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartExit

/-!
# Lemma 5.7's statements in the capacity chart

The completed E-chart path reads the M_q-chart trace at capacity time `s / (1 - s)`. This file converts range
containment and the pathwise reverse-order conclusion for that completed path into statements for the M_q-chart
trace.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Real NNReal
open QuantumZipper (H)

namespace InteractingSLE.Sec5

open Sec4
open CrossRestart

/-- Convert the E-chart range containment in Lemma 5.7 into capacity-chart containment for every positive-time
point of the explored path. -/
theorem lemma57_containment_capacityChart {q : ℝ} {γ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {T : ℝ}
    (hq : 0 < q) (hγ0 : γ 0 = 0) (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H)
    (hηH : ∀ t : ℝ, 0 < t → η t ∈ H)
    (hcontain : (fun s : ℝ => η s.toNNReal) '' Icc (0 : ℝ) T ⊆
      stripCounterflowPath q γ '' Icc (0 : ℝ) 1)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    ∃ v : ℝ≥0, γ v = (stripCounterflowChart q).1 (η t) := by
  have htmem : (fun s : ℝ => η s.toNNReal) t ∈
      (fun s : ℝ => η s.toNNReal) '' Icc (0 : ℝ) T :=
    ⟨t, ⟨ht0.le, htT⟩, rfl⟩
  have hηtH : η t ∈ H := hηH t ht0
  obtain ⟨u, hu, hhitRaw⟩ := hcontain htmem
  have htcast : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht0.le
  have hhit : stripCounterflowPath q γ u = η t := by
    rw [← htcast]
    exact hhitRaw
  have hu1 : u < 1 := by
    by_contra hn
    have huEq : u = 1 := le_antisymm hu.2 (not_lt.1 hn)
    subst u
    rw [stripCounterflowPath_one] at hhit
    have hηt0 : η t = 0 := hhit.symm
    rw [hηt0] at hηtH
    exact (by simpa [H] using hηtH)
  have hu0 : 0 ≤ u := hu.1
  let v : ℝ≥0 := (u / (1 - u)).toNNReal
  have hvco : (v : ℝ) = u / (1 - u) :=
    Real.coe_toNNReal _ (div_nonneg hu0 (by linarith))
  have hpath : stripCounterflowPath q γ u =
      (stripCounterflowChart q).2.1 (γ v) := by
    rw [stripCounterflowPath_of_lt hu1]
  have hhitInv : (stripCounterflowChart q).2.1 (γ v) = η t := by
    rw [← hpath]
    exact hhit
  have hne : γ v ≠ -1 := by
    intro hneg
    by_cases hv0 : v = 0
    · rw [hv0, hγ0] at hneg
      norm_num at hneg
    · have hvpos : 0 < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv0)
      have hmem := hγH v hvpos
      rw [hneg] at hmem
      change 0 < (-1 : ℂ).im at hmem
      norm_num at hmem
  refine ⟨v, ?_⟩
  calc
    γ v = (stripCounterflowChart q).1 ((stripCounterflowChart q).2.1 (γ v)) :=
      (stripCounterflowChart_fwd_inv hq hne).symm
    _ = (stripCounterflowChart q).1 (η t) := by rw [hhitInv]

/-- Almost-sure form of `lemma57_containment_capacityChart`. -/
theorem ae_lemma57_containment_capacityChart {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {q : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} {T : Ω → ℝ}
    (hq : 0 < q)
    (hγ0 : ∀ᵐ ω ∂P, γ ω 0 = 0)
    (hγH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hηH : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ∈ H)
    (hcontain : ∀ᵐ ω ∂P, (fun s : ℝ => η ω s.toNNReal) '' Icc (0 : ℝ) (T ω) ⊆
      stripCounterflowPath q (γ ω) '' Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → t ≤ T ω →
      ∃ v : ℝ≥0, γ ω v = (stripCounterflowChart q).1 (η ω t) := by
  filter_upwards [hγ0, hγH, hηH, hcontain] with ω hγ0ω hγHω hηHω hcontainω
  intro t ht0 htT
  exact lemma57_containment_capacityChart hq hγ0ω hγHω hηHω hcontainω ht0 htT

/-- Convert Lemma 5.7's reverse chronological order for the completed E-chart path into reverse chronological order
for the capacity-parametrized trace in chart `M_q`. -/
theorem lemma57_reverseOrder_capacityChart {q : ℝ} {γ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {T : ℝ}
    (hq : 0 < q) (hγ0 : γ 0 = 0) (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H)
    (hη0 : η 0 = 0) (hηH : ∀ t : ℝ, 0 < t → η t ∈ H)
    (h57 : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      ∃ u ∈ Icc (0 : ℝ) 1, stripCounterflowPath q γ u = η t ∧
        ∀ r ∈ Icc (0 : ℝ) u, stripCounterflowPath q γ r ≠ η s)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    ∃ v : ℝ≥0, γ v = (stripCounterflowChart q).1 (η t) ∧
      ∀ w ≤ v, γ w ≠ (stripCounterflowChart q).1 (η s) := by
  have htpos : 0 < t := lt_of_le_of_lt hs hst
  obtain ⟨u, hu, hhit, hbefore⟩ := h57 s t hs hst ht
  have hu1 : u < 1 := by
    by_contra hn
    have huEq : u = 1 := le_antisymm hu.2 (not_lt.1 hn)
    subst u
    rw [stripCounterflowPath_one] at hhit
    have hηnot : η t ∉ H := by
      rw [← hhit]
      simp [H]
    exact hηnot (hηH t htpos)
  have hu0 : 0 ≤ u := hu.1
  let v : ℝ≥0 := (u / (1 - u)).toNNReal
  have hvco : (v : ℝ) = u / (1 - u) :=
    Real.coe_toNNReal _ (div_nonneg hu0 (by linarith))
  have hvparam : physTime (v : ℝ) = u := by
    rw [hvco]
    exact physTime_div_one_sub hu1
  have hvtime : physTime (v : ℝ) / (1 - physTime (v : ℝ)) = (v : ℝ) :=
    physTime_div v.coe_nonneg
  have huv : u / (1 - u) = (v : ℝ) := by
    rw [← hvparam]
    exact hvtime
  have hvto : (u / (1 - u)).toNNReal = v := by
    apply NNReal.coe_inj.mp
    rw [Real.coe_toNNReal _ (div_nonneg hu0 (by linarith))]
  have hu_path : stripCounterflowPath q γ u =
      (stripCounterflowChart q).2.1 (γ v) := by
    rw [stripCounterflowPath_of_lt hu1, hvto]
  have hhitInv : (stripCounterflowChart q).2.1 (γ v) = η t := by
    rw [← hu_path]
    exact hhit
  have htarget : γ v = (stripCounterflowChart q).1 (η t) := by
    have hne : γ v ≠ -1 := by
      intro hneg
      have hz : (stripCounterflowChart q).2.1 (γ v) = 0 := by
        rw [hneg, stripCounterflowChart_inv]
        simp
      rw [hhitInv] at hz
      have hz0 : η t = 0 := hz
      have hmem := hηH t htpos
      rw [hz0] at hmem
      exact (by simpa [H] using hmem)
    calc
      γ v = (stripCounterflowChart q).1 ((stripCounterflowChart q).2.1 (γ v)) :=
        (stripCounterflowChart_fwd_inv hq hne).symm
      _ = (stripCounterflowChart q).1 (η t) := by rw [hhitInv]
  refine ⟨v, htarget, ?_⟩
  intro w hw hEq
  let r : ℝ := physTime (w : ℝ)
  have hr0 : 0 ≤ r := physTime_nonneg w.coe_nonneg
  have hr1 : r < 1 := physTime_lt_one w.coe_nonneg
  have hrtime : r / (1 - r) = (w : ℝ) := physTime_div w.coe_nonneg
  have hrto : (r / (1 - r)).toNNReal = w := by
    apply NNReal.coe_inj.mp
    rw [Real.coe_toNNReal _ (div_nonneg hr0 (by linarith))]
    exact hrtime
  have hrle : r ≤ u := by
    calc
      r = physTime (w : ℝ) := rfl
      _ ≤ physTime (v : ℝ) :=
        strictMonoOn_physTime.monotoneOn (mem_Ici.2 w.coe_nonneg)
          (mem_Ici.2 v.coe_nonneg) hw
      _ = u := hvparam
  have hpath : stripCounterflowPath q γ r = η s := by
    rw [stripCounterflowPath_of_lt hr1, hrto, hEq]
    by_cases hspos : 0 < s
    · exact stripCounterflowChart_inv_fwd hq (DerivLog.ne_zero_of_mem_H (hηH s hspos))
    · have hs0 : s = 0 := le_antisymm (not_lt.1 hspos) hs
      have hEq0 : γ w = -1 := by simpa [hs0, hη0, stripCounterflowChart_fwd] using hEq
      by_cases hw0 : w = 0
      · rw [hw0, hγ0] at hEq0
        exact False.elim (by norm_num at hEq0)
      · have hwpos : 0 < w := lt_of_le_of_ne w.coe_nonneg (Ne.symm hw0)
        have : γ w ∈ H := hγH w hwpos
        rw [hEq0] at this
        have hfalse : False := by
          change 0 < (-1 : ℂ).im at this
          norm_num at this
        exact hfalse.elim
  exact (hbefore r ⟨hr0, hrle⟩) hpath

/-- Almost-sure form of `lemma57_reverseOrder_capacityChart`: an E-chart reverse-order statement transfers to
capacity time in the `M_q` chart on the same full-measure event. -/
theorem ae_lemma57_reverseOrder_capacityChart {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {q : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} {T : Ω → ℝ}
    (hq : 0 < q)
    (hγ0 : ∀ᵐ ω ∂P, γ ω 0 = 0)
    (hγH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hη0 : ∀ᵐ ω ∂P, η ω 0 = 0)
    (hηH : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ∈ H)
    (h57 : ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T ω →
      ∃ u ∈ Icc (0 : ℝ) 1, stripCounterflowPath q (γ ω) u = η ω t ∧
        ∀ r ∈ Icc (0 : ℝ) u, stripCounterflowPath q (γ ω) r ≠ η ω s) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T ω →
      ∃ v : ℝ≥0, γ ω v = (stripCounterflowChart q).1 (η ω t) ∧
        ∀ w ≤ v, γ ω w ≠ (stripCounterflowChart q).1 (η ω s) := by
  filter_upwards [hγ0, hγH, hη0, hηH, h57] with ω hγ0ω hγHω hη0ω hηHω h57ω
  intro s t hs hst ht
  exact lemma57_reverseOrder_capacityChart hq hγ0ω hγHω hη0ω hηHω h57ω hs hst ht

end InteractingSLE.Sec5

end
