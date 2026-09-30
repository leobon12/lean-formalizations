/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (EXT-D3: hitting times of the driving function)
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# First and last hitting times of a level by a continuous function on a closed interval

If `φ : ℝ → ℝ` is continuous on `Icc a b`, is strictly below a level `L` at the left endpoint `a`
and reaches `L` somewhere on `Icc a b`, then there is a *first* such time (`exists_firstHit`); if
moreover `L < φ b`, there is a *last* such time (`exists_lastHit`). Each lemma gives the full
first/last-time characterisation. Both are proved from scratch by the standard "first entrance
time" argument, with `σ := sInf {t ∈ Icc a b | L ≤ φ t}` and `τ := sSup {t ∈ Icc a b | φ t = L}`.
-/

noncomputable section

open Set Metric

namespace QuantumZipper.JS

/-- **First hitting time of a level by a continuous function on a closed interval.**
Own elementary proof (real analysis; the standard "first entrance time" argument). Let
`S = {t ∈ Icc a b | L ≤ φ t}` be the set of times of the interval at which the level is already
reached; it is nonempty by `h` and bounded below by `a`, so `σ := sInf S` exists and lies in
`Icc a b`. Continuity at `a` together with `φ a < L` gives `a < σ`, and by definition of the
infimum `φ < L` strictly below `σ` on the interval. If `φ σ < L`, continuity at `σ` puts a point of
`S` just above `σ` inside a relative ball on which `φ < L`, a contradiction; if `L < φ σ`,
continuity at `σ` gives `L < φ` on a relative ball around `σ`, but the point `max a (σ - δ/2)` of
the interval lies strictly below `σ` inside that ball, contradicting `φ < L` below `σ`. Hence
`φ σ = L`; the two final claims are then just the definition of `σ` as an infimum of hitting
times. -/
lemma exists_firstHit {φ : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (ha : φ a < L) (h : ∃ t ∈ Icc a b, L ≤ φ t) :
    ∃ σ : ℝ, σ ∈ Icc a b ∧ φ σ = L ∧ (∀ s ∈ Icc a b, s < σ → φ s < L) ∧
      ∀ s ∈ Icc a b, L ≤ φ s → σ ≤ s := by
  -- continuity of `φ` on the interval, as a relative ball on which a strict comparison
  -- with the level `L` persists at a point of the interval
  have hcontLt : ∀ x ∈ Icc a b, φ x < L →
      ∃ δ > 0, ∀ t ∈ Icc a b, dist t x < δ → φ t < L := by
    intro x hx hxL
    have hmem := (hφ.continuousWithinAt hx).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hxL)
    obtain ⟨δ, hδpos, hδ⟩ := mem_nhdsWithin_iff.mp hmem
    exact ⟨δ, hδpos, fun t ht htd => hδ ⟨mem_ball.mpr htd, ht⟩⟩
  have hcontGt : ∀ x ∈ Icc a b, L < φ x →
      ∃ δ > 0, ∀ t ∈ Icc a b, dist t x < δ → L < φ t := by
    intro x hx hxL
    have hmem := (hφ.continuousWithinAt hx).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds hxL)
    obtain ⟨δ, hδpos, hδ⟩ := mem_nhdsWithin_iff.mp hmem
    exact ⟨δ, hδpos, fun t ht htd => hδ ⟨mem_ball.mpr htd, ht⟩⟩
  obtain ⟨t₀, ht₀, ht₀L⟩ := h
  -- `S` is the set of times of the interval at which the level has already been reached
  have hSne : (Icc a b ∩ φ ⁻¹' (Ici L)).Nonempty := ⟨t₀, ht₀, ht₀L⟩
  have hbdd : BddBelow (Icc a b ∩ φ ⁻¹' (Ici L)) := ⟨a, fun y hy => hy.1.1⟩
  have hσmem : sInf (Icc a b ∩ φ ⁻¹' (Ici L)) ∈ Icc a b := by
    obtain ⟨t, ht⟩ := hSne
    exact ⟨le_csInf ⟨t, ht⟩ fun y hy => hy.1.1, le_trans (csInf_le hbdd ht) ht.1.2⟩
  -- the infimum is strictly above `a`
  have ha_lt : a < sInf (Icc a b ∩ φ ⁻¹' (Ici L)) := by
    obtain ⟨δ, hδpos, hδ⟩ := hcontLt a ⟨le_rfl, hab⟩ ha
    have hle : a + δ ≤ sInf (Icc a b ∩ φ ⁻¹' (Ici L)) := by
      refine le_csInf hSne fun y hy => ?_
      by_contra hcon
      have hylt : y < a + δ := not_le.mp hcon
      have hdist : dist y a < δ := by
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith [hy.1.1]
      exact absurd (hδ y hy.1 hdist) (not_lt.mpr hy.2)
    linarith
  -- strictly below the infimum the level is not yet reached, by definition of the infimum
  have hbelow : ∀ s ∈ Icc a b, s < sInf (Icc a b ∩ φ ⁻¹' (Ici L)) → φ s < L := by
    intro s hs hslt
    by_contra hcon
    exact absurd (csInf_le hbdd ⟨hs, not_lt.mp hcon⟩) (not_le.mpr hslt)
  -- `φ` does not exceed the level at the infimum: a point of the interval just below the infimum
  -- has `φ < L`, while `L < φ (sInf S)` would make `L < φ` hold on a relative neighbourhood of
  -- the infimum, which still contains a point of the interval just below it
  have hσLle : φ (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) ≤ L := by
    by_contra hcon
    have hgt : L < φ (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) := not_le.mp hcon
    obtain ⟨δ, hδpos, hδ⟩ := hcontGt _ hσmem hgt
    have htlt : max a (sInf (Icc a b ∩ φ ⁻¹' (Ici L)) - δ / 2) <
        sInf (Icc a b ∩ φ ⁻¹' (Ici L)) := max_lt_iff.mpr ⟨ha_lt, by linarith⟩
    have htmem : max a (sInf (Icc a b ∩ φ ⁻¹' (Ici L)) - δ / 2) ∈ Icc a b :=
      ⟨le_max_left _ _, le_trans htlt.le hσmem.2⟩
    have hdist : dist (max a (sInf (Icc a b ∩ φ ⁻¹' (Ici L)) - δ / 2))
        (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [le_max_right a (sInf (Icc a b ∩ φ ⁻¹' (Ici L)) - δ / 2)]
    exact absurd (hδ _ htmem hdist) (not_lt.mpr (le_of_lt (hbelow _ htmem htlt)))
  -- and the level is reached at the infimum
  have hσLge : L ≤ φ (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) := by
    by_contra hcon
    have hlt : φ (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) < L := not_le.mp hcon
    obtain ⟨δ, hδpos, hδ⟩ := hcontLt _ hσmem hlt
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hSne
      (lt_add_of_pos_right (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) hδpos)
    have hσt : sInf (Icc a b ∩ φ ⁻¹' (Ici L)) ≤ t := csInf_le hbdd ht
    have hdist : dist t (sInf (Icc a b ∩ φ ⁻¹' (Ici L))) < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    exact absurd (hδ t ht.1 hdist) (not_lt.mpr ht.2)
  refine ⟨sInf (Icc a b ∩ φ ⁻¹' (Ici L)), hσmem, le_antisymm hσLle hσLge, ?_, ?_⟩
  · intro s hs hslt
    by_contra hcon
    exact absurd (csInf_le hbdd ⟨hs, not_lt.mp hcon⟩) (not_le.mpr hslt)
  · intro s hs hsL
    exact csInf_le hbdd ⟨hs, hsL⟩

/-- **Last hitting time of a level by a continuous function on a closed interval** (it starts below
`L` and ends above `L`). Own elementary proof. Let `B = {t ∈ Icc a b | φ t = L}` be the set of
times of the interval at which the level is attained. It is nonempty by the intermediate value
theorem applied on `Icc a b` (`L ∈ Icc (φ a) (φ b)`), and bounded above by `b`, so
`τ := sSup B` exists and lies in `Icc a b`. If `φ τ < L`, continuity at `τ` gives `φ < L` on a
relative neighbourhood of `τ`, which contains a point of `B` below `τ`; if `L < φ τ`, continuity
at `τ` gives `L < φ` on a relative neighbourhood of `τ`, so every point of `B` is at distance `≥ δ`
below `τ` and `τ - δ` is an upper bound of `B`, contradicting `τ = sSup B`. Hence `φ τ = L`.
Finally, if `τ < s ∈ Icc a b` and `φ s ≤ L`, then either `φ s = L`, so `s ∈ B` and `s ≤ τ`, or
`φ s < L`, and the intermediate value theorem on `Icc s b` (where `L < φ b`) produces a point of
`B` strictly above `τ < s`, again a contradiction. -/
lemma exists_lastHit {φ : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (ha : φ a < L) (hb : L < φ b) :
    ∃ τ : ℝ, τ ∈ Icc a b ∧ φ τ = L ∧ ∀ s ∈ Icc a b, τ < s → L < φ s := by
  have hcontLt : ∀ x ∈ Icc a b, φ x < L →
      ∃ δ > 0, ∀ t ∈ Icc a b, dist t x < δ → φ t < L := by
    intro x hx hxL
    have hmem := (hφ.continuousWithinAt hx).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hxL)
    obtain ⟨δ, hδpos, hδ⟩ := mem_nhdsWithin_iff.mp hmem
    exact ⟨δ, hδpos, fun t ht htd => hδ ⟨mem_ball.mpr htd, ht⟩⟩
  have hcontGt : ∀ x ∈ Icc a b, L < φ x →
      ∃ δ > 0, ∀ t ∈ Icc a b, dist t x < δ → L < φ t := by
    intro x hx hxL
    have hmem := (hφ.continuousWithinAt hx).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds hxL)
    obtain ⟨δ, hδpos, hδ⟩ := mem_nhdsWithin_iff.mp hmem
    exact ⟨δ, hδpos, fun t ht htd => hδ ⟨mem_ball.mpr htd, ht⟩⟩
  -- the level is attained, by the intermediate value theorem
  obtain ⟨τ₀, hτ₀, hτ₀L⟩ := intermediate_value_Icc hab hφ ⟨le_of_lt ha, le_of_lt hb⟩
  -- `B` is the set of times of the interval at which the level is attained
  have hBne : (Icc a b ∩ φ ⁻¹' {L}).Nonempty := ⟨τ₀, hτ₀, hτ₀L⟩
  have hbddB : BddAbove (Icc a b ∩ φ ⁻¹' {L}) := ⟨b, fun y hy => hy.1.2⟩
  have hτmem : sSup (Icc a b ∩ φ ⁻¹' {L}) ∈ Icc a b := by
    obtain ⟨t, ht⟩ := hBne
    exact ⟨le_trans ht.1.1 (le_csSup hbddB ht), csSup_le ⟨t, ht⟩ fun y hy => hy.1.2⟩
  -- the level is attained at the supremum
  have hτLge : L ≤ φ (sSup (Icc a b ∩ φ ⁻¹' {L})) := by
    by_contra hcon
    have hlt : φ (sSup (Icc a b ∩ φ ⁻¹' {L})) < L := not_le.mp hcon
    obtain ⟨δ, hδpos, hδ⟩ := hcontLt _ hτmem hlt
    obtain ⟨t, ht, htt⟩ := exists_lt_of_lt_csSup hBne
      (sub_lt_self (sSup (Icc a b ∩ φ ⁻¹' {L})) hδpos)
    have hts : t ≤ sSup (Icc a b ∩ φ ⁻¹' {L}) := le_csSup hbddB ht
    have hdist : dist t (sSup (Icc a b ∩ φ ⁻¹' {L})) < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have hφt : φ t = L := ht.2
    linarith [hδ t ht.1 hdist]
  have hτLle : φ (sSup (Icc a b ∩ φ ⁻¹' {L})) ≤ L := by
    by_contra hcon
    have hgt : L < φ (sSup (Icc a b ∩ φ ⁻¹' {L})) := not_le.mp hcon
    obtain ⟨δ, hδpos, hδ⟩ := hcontGt _ hτmem hgt
    have hupper : ∀ t ∈ Icc a b ∩ φ ⁻¹' {L}, t ≤ sSup (Icc a b ∩ φ ⁻¹' {L}) - δ := by
      intro t ht
      by_contra hcon'
      have htt : sSup (Icc a b ∩ φ ⁻¹' {L}) - δ < t := not_le.mp hcon'
      have hts : t ≤ sSup (Icc a b ∩ φ ⁻¹' {L}) := le_csSup hbddB ht
      have hdist : dist t (sSup (Icc a b ∩ φ ⁻¹' {L})) < δ := by
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor <;> linarith
      have hφt : φ t = L := ht.2
      linarith [hδ t ht.1 hdist]
    have hle := csSup_le hBne hupper
    linarith
  refine ⟨sSup (Icc a b ∩ φ ⁻¹' {L}), hτmem, le_antisymm hτLle hτLge, ?_⟩
  intro s hs hτs
  by_contra hcon
  have hle : φ s ≤ L := not_lt.mp hcon
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- `φ s < L`: the intermediate value theorem on `Icc s b` finds a later hit of the level
    obtain ⟨u, hu, huL⟩ := intermediate_value_Icc hs.2
      (hφ.mono fun x hx => ⟨le_trans hs.1 hx.1, hx.2⟩) ⟨le_of_lt hlt, le_of_lt hb⟩
    have huB : u ∈ Icc a b ∩ φ ⁻¹' {L} := ⟨⟨le_trans hs.1 hu.1, hu.2⟩, huL⟩
    linarith [le_csSup hbddB huB, hu.1]
  · have hsB : s ∈ Icc a b ∩ φ ⁻¹' {L} := ⟨hs, heq⟩
    linarith [le_csSup hbddB hsB]

end QuantumZipper.JS
