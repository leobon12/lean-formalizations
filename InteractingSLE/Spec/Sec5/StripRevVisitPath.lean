/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513WireReverse
import InteractingSLE.Spec.Sec4.Special2Order

/-!
# Lemma 5.7's reverse visits: the pathwise part

Packet PROVE-REVVISIT. Specification §5.2, Lemma 5.7 and its proof (`source/spec/p097-144.md` L889–L893, p. 138):
"By choosing a dense collection of stopping times (e.g., the positive rationals) and using the continuity of `η′` and
`η` we conclude that the range of `η′` contains `η`. Moreover, the proof clearly also implies that the points of `η`
are hit by `η′` in reverse chronological order."

This file contains the deterministic part, for one realization:

* the inverse `T_q⁻¹` of the E-to-Q chart is the Möbius map `z ↦ −(1+q)/(z−1) − (1+q)`, continuous and injective off
  its pole `1` (`targetChart_inv_eq`, `continuousAt_targetChart_inv`, `targetChart_inv_injOn`); hence a continuous
  Q prefix that is injective and stays in `ℍ ∪ {0}` pulls back to a continuous injective E prefix
  (`continuousOn_pullPrefix`, `injOn_pullPrefix`);
* the completed counterflow `stripCounterflowPath q γ` starts at `−1−q`, stays in `ℍ` on `(0, 1)` and ends at `0`
  (`stripCounterflowPath_mem_H`), so it first hits the lower line `∂_L𝒮 = (−1, ∞)` at its exit `0`
  (`isFirstHitPoint_zero`);
* **`reverseVisit_of_firstHit`**: the first-hit property of Lemma 5.7's proof at every positive rational time of a
  prefix gives the reverse-visit assertion of `Prop513Wire.StripReverseVisitLaw` for that prefix (through
  `Sec4.lemma47_pathwise`, the density argument already proved for Lemma 4.7).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.StripRevVisit

open QuantumZipper Sec4 Prop513Schedule Prop513Target Prop513Wire

/-! ### The inverse E-to-Q chart -/

/-- The inverse of the E-to-Q chart is the Möbius map `z ↦ −(1+q)/(z−1) − (1+q)`. -/
theorem targetChart_inv_eq (q : ℝ) (z : ℂ) :
    (targetChart q).2.1 z = -(1 + (q : ℂ)) * (z - 1)⁻¹ - (1 + q) := by
  rw [inv_eq, middle, stripCounterflowChart_inv, show z - 2 + 1 = z - 1 by ring]

/-- The inverse E-to-Q chart is continuous off its pole `1`. -/
theorem continuousAt_targetChart_inv (q : ℝ) {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt (targetChart q).2.1 z := by
  have he : (targetChart q).2.1 = fun w : ℂ => -(1 + (q : ℂ)) * (w - 1)⁻¹ - (1 + q) :=
    funext (targetChart_inv_eq q)
  rw [he]
  exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hz))).sub
    continuousAt_const

/-- The inverse E-to-Q chart is injective off its pole `1`. -/
theorem targetChart_inv_injOn {q : ℝ} (hq : 0 < q) : InjOn (targetChart q).2.1 {z | z ≠ 1} := by
  intro z hz w hw he
  rw [targetChart_inv_eq, targetChart_inv_eq] at he
  have h1 : -(1 + (q : ℂ)) ≠ 0 := neg_ne_zero.2 (one_add_ne_zero_of_pos hq)
  have h2 : (z - 1)⁻¹ = (w - 1)⁻¹ := mul_left_cancel₀ h1 (sub_left_injective he)
  have h3 : z - 1 = w - 1 := inv_injective h2
  linear_combination h3

/-- A point of `ℍ` is not the pole `1`. -/
theorem ne_one_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ 1 := by
  rintro rfl
  exact absurd hz (by simp [H])

/-- **A continuous Q prefix pulls back to a continuous E prefix** on its closed horizon, when it avoids the pole. -/
theorem continuousOn_pullPrefix (q : ℝ) {T : ℝ} {η : ℝ → ℂ} (hc : ContinuousOn η (Icc 0 T))
    (h1 : ∀ t ∈ Icc 0 T, η t ≠ 1) : ContinuousOn (pullPrefix q T η) (Icc 0 T) := by
  have he : EqOn (pullPrefix q T η) ((targetChart q).2.1 ∘ η) (Icc 0 T) := fun t ht =>
    pullPrefix_of_mem q η ht
  refine ContinuousOn.congr (fun t ht => ?_) he
  exact (continuousAt_targetChart_inv q (h1 t ht)).comp_continuousWithinAt (hc t ht)

/-- **An injective Q prefix pulls back to an injective E prefix**, when it avoids the pole. -/
theorem injOn_pullPrefix {q T : ℝ} (hq : 0 < q) {η : ℝ → ℂ} {S : Set ℝ} (hS : S ⊆ Icc 0 T)
    (hinj : InjOn η S) (h1 : ∀ t ∈ S, η t ≠ 1) : InjOn (pullPrefix q T η) S := by
  intro s hs t ht he
  rw [pullPrefix_of_mem q η (hS hs), pullPrefix_of_mem q η (hS ht)] at he
  exact hinj hs ht (targetChart_inv_injOn hq (h1 s hs) (h1 t ht) he)

/-- A Q prefix starting at `0` and in `ℍ` at positive times avoids the pole. -/
theorem ne_one_of_prefix {T : ℝ} {η : ℝ → ℂ} (hη0 : η 0 = 0) (hηH : ∀ t : ℝ, 0 < t → t ≤ T → η t ∈ H) :
    ∀ t ∈ Icc 0 T, η t ≠ 1 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, hη0]
    exact zero_ne_one
  · exact ne_one_of_mem_H (hηH t h ht.2)

/-! ### The completed counterflow -/

/-- The completed counterflow stays in `ℍ` on `(0, 1)`. -/
theorem stripCounterflowPath_mem_H {q : ℝ} (hq : 0 < q) {γ : ℝ≥0 → ℂ} (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : stripCounterflowPath q γ s ∈ H := by
  rw [stripCounterflowPath_of_lt hs1]
  exact stripCounterflowChart_inv_mem_H hq (hγH _ (Real.toNNReal_pos.2 (div_pos hs0 (by linarith))))

/-- A point of `ℍ` is not on the lower line. -/
theorem notMem_lowerLineH_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∉ lowerLineH := by
  rintro ⟨x, -, rfl⟩
  exact absurd hz (by simp [H])

/-- The counterflow's start `E(z₀) = −1 − q` is neither on the lower line nor at `0`. -/
theorem start_notMem {q : ℝ} (hq : 0 < q) : (-1 - (q : ℂ)) ∉ lowerLineH ∪ {0} := by
  rintro (⟨x, hx, he⟩ | he)
  · have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.neg_re, Complex.one_re] at hre
    have : -1 < x := hx
    linarith
  · have hre := congrArg Complex.re (mem_singleton_iff.1 he)
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith

/-- **The completed counterflow first hits `∂_L𝒮` at its exit `0`** (the time-`0` case of Lemma 5.7's first-hit
property: `η([0, 0]) = {0}`). -/
theorem isFirstHitPoint_zero {q : ℝ} (hq : 0 < q) {γ : ℝ≥0 → ℂ} (hγ0 : γ 0 = 0)
    (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H) {η : ℝ → ℂ} (hη0 : η 0 = 0) :
    IsFirstHitPoint (stripCounterflowPath q γ) 1 (lowerLineH ∪ η '' Icc 0 0) (η 0) := by
  rw [Icc_self, image_singleton, hη0]
  refine ⟨1, ⟨zero_le_one, le_rfl⟩, stripCounterflowPath_one γ, Or.inr rfl, fun v hv => ?_⟩
  rcases eq_or_lt_of_le hv.1 with h | h
  · rw [← h, stripCounterflowPath_zero hγ0]
    exact start_notMem hq
  · have hH := stripCounterflowPath_mem_H hq hγH h hv.2
    rintro (h' | h')
    · exact notMem_lowerLineH_of_mem_H hH h'
    · rw [mem_singleton_iff.1 h'] at hH
      exact absurd hH (by simp [H])

/-! ### Reverse visits from first hits at rational times -/

/-- **Lemma 5.7's reverse visits from its first-hit property, one realization** (the density step of the proof). Let
the completed counterflow `stripCounterflowPath q γ` be continuous on `[0, 1]`, with `γ(0) = 0` and `γ` in `ℍ` at
positive times, and let the prefix `η` be continuous on `[0, T]`, injective on `[0, T)` and rooted at `0`. If at every
positive rational time `r < T` the counterflow first hits `∂_L𝒮 ∪ η([0, r])` at `η(r)`, then for all
`0 ≤ s < t ≤ T` the counterflow visits `η(t)` at some time `u ∈ [0, 1]` and does not visit `η(s)` on `[0, u]`. -/
theorem reverseVisit_of_firstHit {q T : ℝ} (hq : 0 < q) (hT : 0 < T) {γ : ℝ≥0 → ℂ}
    (hγc : ContinuousOn (stripCounterflowPath q γ) (Icc 0 1)) (hγ0 : γ 0 = 0)
    (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H) {η : ℝ → ℂ} (hηc : ContinuousOn η (Icc 0 T))
    (hinj : InjOn η (Ico 0 T)) (hη0 : η 0 = 0)
    (hb : ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < T →
      IsFirstHitPoint (stripCounterflowPath q γ) 1 (lowerLineH ∪ η '' Icc 0 r) (η r)) :
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      ∃ u ∈ Icc (0 : ℝ) 1, stripCounterflowPath q γ u = η t ∧
        ∀ r ∈ Icc (0 : ℝ) u, stripCounterflowPath q γ r ≠ η s := by
  refine (lemma47_pathwise hT hγc hηc hinj fun r hr0 hrT => ?_).2.2
  rcases eq_or_lt_of_le hr0 with h | h
  · rw [← h]
    exact isFirstHitPoint_zero hq hγ0 hγH hη0
  · exact hb r h hrT

end InteractingSLE.Sec5.StripRevVisit
