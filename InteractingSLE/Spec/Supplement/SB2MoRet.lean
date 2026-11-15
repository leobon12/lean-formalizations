/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MoHull
import InteractingSLE.GFF.LocalSets.HittingSigma
import InteractingSLE.Spec.Sec7.SideHeightRange

/-!
# Random retained hulls observed through hitting events

Packet PROVE-SB2-LCMEAN, round 11 (item F2). The canonical relative chart of an actual lower stage is the chart of
the hull of the retained union `A ∪ B_{<ℓ}` (`Mo.hullChart`). Its measurability (`Mo.measurable_indicator_*`) asks
for a random compact set, connected to the real line at every sample, observed through closed dyadic squares. The
retained union is known through a line version `B` (`Lcd.exists_lineVersion`): a random relatively closed subset of
`ℍ`, measurable for the hitting σ-algebra (open subsets of `ℍ`), equal almost surely to the actual stage sets. This
file passes from such a `B` to a random compact set:

* **`measurableSet_dyadicHit_closure`**: for `B` measurable for the hitting σ-algebra with values in `ℍ`, the event
  that a closed dyadic square meets `closure (B ω)` is measurable (thickenings of the square);
* `closure_inter_H_union_lowerHalf`, `fillH_closure_inter_H`: for a closed `X ⊆ ℍ̄`, `closure (X ∩ ℍ)` has the same
  union with the lower half-plane and the same fill as `X`;
* **`retHull`**: `closure (B ω)` on a good event `G`, `∅` elsewhere; **`isDyadicHitMeasurable_retHull`** (for any
  σ-algebra containing `B`'s and `G`), `isCompact_retHull`, `isPreconnected_retHull_union` (from the good event).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mo

/-! ### Dyadic hits of the closure of a hitting-measurable set -/

/-- A compact set meets the closure of `S ⊆ ℍ` iff every thickening of it meets `S` inside `ℍ`. -/
theorem inter_closure_nonempty_iff {Q S : Set ℂ} (hQ : IsCompact Q) (hS : S ⊆ H) :
    (Q ∩ closure S).Nonempty ↔ ∀ n : ℕ, (S ∩ (thickening (1 / ((n : ℝ) + 1)) Q ∩ H)).Nonempty := by
  constructor
  · rintro ⟨p, hpQ, hpS⟩ n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨s, hs, hsS⟩ := mem_closure_iff_nhds.1 hpS _ (ball_mem_nhds p hε)
    exact ⟨s, hsS, mem_thickening_iff.2 ⟨p, hpQ, hs⟩, hS hsS⟩
  · intro h
    choose s hs using h
    have hq : ∀ n, ∃ q ∈ Q, dist (s n) q < 1 / ((n : ℝ) + 1) := fun n => mem_thickening_iff.1 (hs n).2.1
    choose q hqQ hqd using hq
    obtain ⟨p, hpQ, φ, hφ, hlim⟩ := hQ.tendsto_subseq hqQ
    refine ⟨p, hpQ, mem_closure_of_tendsto (f := fun n => s (φ n)) (b := atTop) ?_
      (Eventually.of_forall fun n => (hs (φ n)).1)⟩
    have h0 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (by simpa using h0.add (tendsto_iff_dist_tendsto_zero.1 hlim)))
    calc dist (s (φ n)) p ≤ dist (s (φ n)) (q (φ n)) + dist (q (φ n)) p := dist_triangle _ _ _
      _ ≤ 1 / ((φ n : ℝ) + 1) + dist (q (φ n)) p := by linarith [(hqd (φ n)).le]
      _ = ((φ n : ℝ) + 1)⁻¹ + dist (q (φ n)) p := by rw [one_div]

/-- **Dyadic hits of the closure of a hitting-measurable random subset of `ℍ` are measurable.** -/
theorem measurableSet_dyadicHit_closure {Ω : Type*} {m : MeasurableSpace Ω} {B : Ω → Set ℂ}
    (hB : Measurable[m, hittingSigma] B) (hBH : ∀ ω, B ω ⊆ H) (n : ℕ) (k : ℤ × ℤ) :
    MeasurableSet[m] {ω | (Restart.dyadicSquare n k ∩ closure (B ω)).Nonempty} := by
  have e : {ω | (Restart.dyadicSquare n k ∩ closure (B ω)).Nonempty} =
      ⋂ j : ℕ, B ⁻¹' {S : Set ℂ |
        (S ∩ (thickening (1 / ((j : ℝ) + 1)) (Restart.dyadicSquare n k) ∩ H)).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    exact inter_closure_nonempty_iff (Restart.isCompact_dyadicSquare n k) (hBH ω)
  rw [e]
  exact MeasurableSet.iInter fun j =>
    hB (LocalSets.measurableSet_hitting (isOpen_thickening.inter QuantumZipper.isOpen_H) inter_subset_right)

/-! ### Closures of the parts in `ℍ` -/

/-- For a closed `X ⊆ ℍ̄`, the closure of its part in `ℍ` has the same union with the lower half-plane. -/
theorem closure_inter_H_union_lowerHalf {X : Set ℂ} (hXc : IsClosed X) :
    closure (X ∩ H) ∪ Restart.lowerHalf = X ∪ Restart.lowerHalf := by
  refine Subset.antisymm (union_subset_union_left _ ((closure_mono inter_subset_left).trans hXc.closure_subset)) ?_
  rintro z (hz | hz)
  · by_cases hzH : z ∈ H
    · exact Or.inl (subset_closure ⟨hz, hzH⟩)
    · right
      have h1 : ¬ 0 < z.im := hzH
      show z.im ≤ 0
      exact not_lt.1 h1
  · exact Or.inr hz

/-- The closure of the part in `ℍ` has the same fill. -/
theorem fillH_closure_inter_H (X : Set ℂ) : fillH (closure (X ∩ H)) = fillH X := by
  rw [Sec7.SideHeight.fillH_closure, Sec7.SideHeight.fillH_inter_H]

/-! ### The random retained hull -/

section RetHull

variable {Ω : Type*} (B : Ω → Set ℂ) (G : Set Ω)

open Classical in
/-- **The random retained hull**: `closure (B ω)` on the good event `G`, empty elsewhere. -/
def retHull (ω : Ω) : Set ℂ := if ω ∈ G then closure (B ω) else ∅

variable {B G}

theorem retHull_of_mem {ω : Ω} (hω : ω ∈ G) : retHull B G ω = closure (B ω) := by
  simp only [retHull, hω, ↓reduceIte]

theorem retHull_of_notMem {ω : Ω} (hω : ω ∉ G) : retHull B G ω = ∅ := by
  simp only [retHull, hω, ↓reduceIte]

/-- **The random retained hull is observed through its dyadic hits** for any σ-algebra containing the good event and
the hitting events of `B`. -/
theorem isDyadicHitMeasurable_retHull {m : MeasurableSpace Ω} (hB : Measurable[m, hittingSigma] B)
    (hBH : ∀ ω, B ω ⊆ H) (hG : MeasurableSet[m] G) : @Restart.IsDyadicHitMeasurable Ω m (retHull B G) := by
  intro n k
  have e : {ω | (Restart.dyadicSquare n k ∩ retHull B G ω).Nonempty} =
      G ∩ {ω | (Restart.dyadicSquare n k ∩ closure (B ω)).Nonempty} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, retHull_of_mem hω, mem_inter_iff, hω, true_and]
    · simp only [mem_ofPred_eq, retHull_of_notMem hω, inter_empty, Set.not_nonempty_empty, mem_inter_iff, hω,
        false_and]
  rw [e]
  exact hG.inter (measurableSet_dyadicHit_closure hB hBH n k)

theorem isCompact_retHull (hGb : ∀ ω ∈ G, Bornology.IsBounded (B ω)) (ω : Ω) : IsCompact (retHull B G ω) := by
  by_cases hω : ω ∈ G
  · rw [retHull_of_mem hω]
    exact (hGb ω hω).isCompact_closure
  · rw [retHull_of_notMem hω]
    exact isCompact_empty

/-- **The random retained hull is connected to the real line** when, on the good event, `B ω` is the part in `ℍ`
of a closed set `X ω ⊆ ℍ̄` connected to the real line. -/
theorem isPreconnected_retHull_union {X : Ω → Set ℂ}
    (hGX : ∀ ω ∈ G, B ω = X ω ∩ H ∧ IsClosed (X ω) ∧ (∀ z ∈ X ω, 0 ≤ z.im) ∧
      IsPreconnected (X ω ∪ Restart.lowerHalf)) (ω : Ω) :
    IsPreconnected (retHull B G ω ∪ Restart.lowerHalf) := by
  by_cases hω : ω ∈ G
  · obtain ⟨hBX, hXc, -, hXp⟩ := hGX ω hω
    rw [retHull_of_mem hω, hBX, closure_inter_H_union_lowerHalf hXc]
    exact hXp
  · rw [retHull_of_notMem hω, empty_union]
    exact InteractingSLE.isPreconnected_lowerHalf

theorem fillH_retHull_of_mem {X : Ω → Set ℂ} {ω : Ω} (hω : ω ∈ G) (hBX : B ω = X ω ∩ H) :
    fillH (retHull B G ω) = fillH (X ω) := by
  rw [retHull_of_mem hω, hBX, fillH_closure_inter_H]

end RetHull

end InteractingSLE.Theorem14.SB.Mo
