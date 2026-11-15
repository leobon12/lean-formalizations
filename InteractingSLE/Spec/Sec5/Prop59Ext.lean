/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma57Visit

/-!
# Proposition 5.9, extreme-angle version: the light cone at a root from the tips at rational times

Packet PROVE-PROP513. Specification §5.2, Proposition 5.9 and its proof (`source/spec/p097-144.md` L911,
L978–L1004; `p145-192.md` L1–L72, pp. 140–148), extreme-angle version (`Θ_* = {−π/2, π/2}`), as used in the proof of
Proposition 5.13 (`p145-192.md` L134–L138): "Let `L_z` be the closure of the post-`σ` portions
`η_desc([σ, τ_terminal])` of its descendants … include the root `z` itself. The extreme-angle version of
Proposition 5.9 gives `L_z = η'([0, T_z])`."

The proof of Proposition 5.9's reverse inclusion ends (p. 148): "Apply the conclusion to positive rational `r` on the
event that `r` precedes the first hit of the initial exploration. Countability and continuity of the counterflow,
including the terminal limit, show that the entire stopped counterflow range lies in the closed accessible set.
Together with the first inclusion this proves the extreme-angle version". This file proves that last step and the
assembly of the identity:

* **`image_Icc_subset_of_rat`** (pathwise): a continuous path whose tips `γ(r)` at the rational times `r < T` lie in
  a closed set `L` containing `γ(T)` has `γ([0, T]) ⊆ L`;
* **`ae_image_Icc_subset_of_rat`**: the same almost surely, from one almost sure statement per rational time (the
  form in which the alternating construction proves it: "It therefore contains `η'(r)` with conditional probability
  at least `1 − ε`. Since `ε > 0` was arbitrary, this probability is one");
* **`range_subset_of_rat`**: the root-`0` case on `[0, ∞)` (Corollary 5.12: the closure of the allowed prefixes
  contains the whole counterflow range);
* **`lightCone_eq_image_Icc`** (the identity at a root): with `L_z = closure ({z} ∪ S)`, Lemma 5.7's reverse
  chronological order for `S` (the post-`σ` portions of the descendants) gives `L_z ⊆ η'([0, T_z])`, and the tips at
  rational times before `T_z` give the reverse inclusion.

The per-time tip membership itself ("for every `ε > 0` … the closed accessible set … contains `η'(r)` with
conditional probability at least `1 − ε`") is the alternating construction of pp. 143–148; it is the input of the
conditional helpers here and in `Prop513.lean`, not proved in this file.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

/-- The nonnegative rationals are dense in `ℝ≥0`, below any bound: every `t < T` is a limit of rationals `< T`. -/
theorem mem_closure_rat_lt {t T : ℝ≥0} (ht : t < T) :
    t ∈ closure {s : ℝ≥0 | (∃ q : ℚ, (s : ℝ) = q) ∧ s < T} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < min ((t : ℝ) + ε) T from lt_min (by linarith)
    (by exact_mod_cast ht))
  have hq0 : (0 : ℝ) ≤ q := (t.coe_nonneg).trans hq1.le
  refine ⟨(q : ℝ).toNNReal, ⟨⟨q, Real.coe_toNNReal _ hq0⟩, ?_⟩, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq2.trans_le (min_le_right _ _)
  · rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_sub_lt_iff]
    constructor <;> linarith [hq2.trans_le (min_le_left _ _)]

/-- **The last step of Proposition 5.9's proof, pathwise.** If `γ` is continuous, `L` is closed, `γ(T) ∈ L` and the
tips `γ(r)` at the nonnegative rational times `r < T` lie in `L`, then `γ([0, T]) ⊆ L`. -/
theorem image_Icc_subset_of_rat {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {L : Set ℂ} (hL : IsClosed L) {T : ℝ≥0}
    (hT : γ T ∈ L) (hrat : ∀ q : ℚ, 0 ≤ q → (q : ℝ) < T → γ (q : ℝ).toNNReal ∈ L) :
    γ '' Icc 0 T ⊆ L := by
  rintro _ ⟨t, ht, rfl⟩
  rcases ht.2.lt_or_eq with hlt | rfl
  · have hsub : γ '' {s : ℝ≥0 | (∃ q : ℚ, (s : ℝ) = q) ∧ s < T} ⊆ L := by
      rintro _ ⟨s, ⟨⟨q, hq⟩, hsT⟩, rfl⟩
      have hq0 : (0 : ℝ) ≤ q := hq ▸ s.coe_nonneg
      have hs : s = (q : ℝ).toNNReal := by rw [← NNReal.coe_inj, Real.coe_toNNReal _ hq0, hq]
      rw [hs]
      exact hrat q (by exact_mod_cast hq0) (by rw [← hq]; exact_mod_cast hsT)
    exact hL.closure_subset_iff.2 hsub (image_closure_subset_closure_image hγ ⟨t, mem_closure_rat_lt hlt, rfl⟩)
  · exact hT

/-- **The last step of Proposition 5.9's proof, almost surely**: one almost sure tip statement per rational time. -/
theorem ae_image_Icc_subset_of_rat {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : Ω → ℝ≥0 → ℂ}
    {L : Ω → Set ℂ} {T : Ω → ℝ≥0} (hγ : ∀ᵐ ω ∂P, Continuous (γ ω)) (hL : ∀ᵐ ω ∂P, IsClosed (L ω))
    (hT : ∀ᵐ ω ∂P, γ ω (T ω) ∈ L ω)
    (hrat : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, (q : ℝ) < T ω → γ ω (q : ℝ).toNNReal ∈ L ω) :
    ∀ᵐ ω ∂P, γ ω '' Icc 0 (T ω) ⊆ L ω := by
  have hrat' : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ q → (q : ℝ) < T ω → γ ω (q : ℝ).toNNReal ∈ L ω := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ q
    · filter_upwards [hrat q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hγ, hL, hT, hrat'] with ω hγω hLω hTω hω
  exact image_Icc_subset_of_rat hγω hLω hTω hω

/-- **Corollary 5.12's inclusion, pathwise** (root `0`, whole time line): if the tips `γ(r)` at the nonnegative
rational times lie in a closed set `L`, the whole range of `γ` does. -/
theorem range_subset_of_rat {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {L : Set ℂ} (hL : IsClosed L)
    (hrat : ∀ q : ℚ, 0 ≤ q → γ (q : ℝ).toNNReal ∈ L) : range γ ⊆ L := by
  rintro _ ⟨t, rfl⟩
  have hsub : γ '' {s : ℝ≥0 | (∃ q : ℚ, (s : ℝ) = q) ∧ s < t + 1} ⊆ L := by
    rintro _ ⟨s, ⟨⟨q, hq⟩, -⟩, rfl⟩
    have hq0 : (0 : ℝ) ≤ q := hq ▸ s.coe_nonneg
    have hs : s = (q : ℝ).toNNReal := by rw [← NNReal.coe_inj, Real.coe_toNNReal _ hq0, hq]
    rw [hs]
    exact hrat q (by exact_mod_cast hq0)
  exact hL.closure_subset_iff.2 hsub
    (image_closure_subset_closure_image hγ ⟨t, mem_closure_rat_lt (lt_add_one t), rfl⟩)

/-- **The extreme-angle light-cone identity at a root** (Proposition 5.9 with Lemma 5.7's first visit). Let
`L = closure ({z} ∪ S)` ("include the root `z` itself"), where every point of `S` (the post-`σ` portions of the
descendants) is visited strictly before the first visit of `z` (Lemma 5.7's reverse chronological order), and let the
tips `γ(r)` at the rational times `r < T_z` lie in `L` (the alternating construction). Then `L = γ([0, T_z])`. -/
theorem lightCone_eq_image_Icc {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {z : ℂ} (hz : ∃ t, γ t = z) {S L : Set ℂ}
    (hL : L = closure (insert z S)) (hS : ∀ p ∈ S, ∃ v, γ v = p ∧ ∀ w ≤ v, γ w ≠ z)
    (hrat : ∀ q : ℚ, 0 ≤ q → (q : ℝ) < traceFirstVisit γ z → γ (q : ℝ).toNNReal ∈ L) :
    L = γ '' Icc 0 (traceFirstVisit γ z) := by
  have hvis := apply_traceFirstVisit hγ hz
  refine le_antisymm ?_ ?_
  · rw [hL, insert_eq, closure_union, closure_singleton]
    exact union_subset (singleton_subset_iff.2 ⟨_, ⟨zero_le, le_rfl⟩, hvis⟩)
      (closure_subset_image_traceFirstVisit hγ hz hS)
  · refine image_Icc_subset_of_rat hγ (hL ▸ isClosed_closure) ?_ hrat
    rw [hvis, hL]
    exact subset_closure (mem_insert z S)

end Sec5

end InteractingSLE
