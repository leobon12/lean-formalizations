/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLeafStep
import InteractingSLE.Spec.Supplement.SB4SwitchWords

/-!
# The relative SB3 instance from SB4's surviving-height classification

Packet PROVE-T14-SBTAIL. In the proof of SB4 (specification pp. 634–635) the hybrid middle word
of the relative pair is not assumed: it is computed from the surviving boundary heights between
the new piece's seed and the relative walk's seed — old upper sides `λ − ψ_jχ`, `−λ − ψ_jχ` of
schedule angles, low groups `H ≤ −Λ`, and the separately retained original bridge. This file
states the relative SB3 instance with that classification (`IsRelSB3WordInstance`) and proves the
instance with the hybrid word from it, by the landed weight algebra `switch_middle_word`. The
distinct-seed bridge `(u, 0)` satisfies the bridge hypothesis by SB4's own premises
(`distinctSeed_bridge`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Leaf

open Sec4

/-- **The relative SB3 instance with SB4's height classification** on the middle interval
`(u', 0)`: the hybrid word of `IsRelSB3Instance` is replaced by the source's classification of
each surviving height (old schedule sides from the list `l`, low groups, or a height of the
retained original bridge word `original`); the new angle is one of the schedule's angles. -/
def IsRelSB3WordInstance (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Ω → DistOn upperHalfPlaneOpens)
    (b' : ℝ → ℝ) (jumps' : Finset ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (l : List (ℝ × ℝ≥0)) (original : Set ℝ) : Prop :=
  IsPiecewiseConstantBoundaryData b' jumps' ∧ IsGFFWithBoundaryData Q hQ b' jumps' ∧
    (IsBoundaryContinuedProgram (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true).2.2 →
      IsStagedHistory κ b' jumps' Q hQ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL ∧
        StagedPiecesRegular κ b' jumps' Q (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL) ∧
    u' ≤ 0 ∧ (∃ q ∈ l, ψ = q.1) ∧
    (∀ x ∈ Ioo u' 0, x ∉ jumps' →
      (∃ p ∈ l, b' x = sleLambda κ - p.1 * chiC κ ∨ b' x = -sleLambda κ - p.1 * chiC κ) ∨
        b' x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨ b' x ∈ original) ∧
    IsFlowLine κ b' jumps' u' ψ Q hQ η ζ ∧ ∀ᵐ ω ∂Q, 0 < ζ ω

/-- **SB4's word paragraph.** Under (SB4.1) (`ψ_j > −π/2`, `|ψ_i − ψ_j| < 2λ/χ`) and the bridge
hypothesis for every schedule angle, the classified relative pair is an SB3 instance. -/
theorem isRelSB3Instance_of_word {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hQ : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {jumps' : Finset ℝ}
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u' ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ}
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hW : IsRelSB3WordInstance κ Q hQ b' jumps' EL u' ψ η ζ l original) :
    IsRelSB3Instance κ Q hQ b' jumps' EL u' ψ η ζ := by
  obtain ⟨hb, hh, hL, hu, ⟨q, hq, rfl⟩, htypes, hη, hζ⟩ := hW
  have hw := switch_middle_word (φ := -(Real.pi / 2)) (ψ := q.1) (u := u') (v := 0)
    (bc := b') (jc := jumps') hκ hκ4 hangles (fun p hp => hgaps q hq p hp)
    (hbridge q hq) htypes
  exact ⟨hb, hh, hL, hu, hangles q hq, hw.1, hw.2, hη, hζ⟩

/-- The distinct-seed bridge word of SB4 (`(u, 0)` with its original heights) satisfies the bridge
hypothesis for every schedule angle, by SB4's own premises on `(u, 0)`. -/
theorem distinctSeed_bridge {κ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {l : List (ℝ × ℝ≥0)}
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) :
    ∀ p ∈ l, ∀ B ∈ b '' {x | x ∈ Ioo u 0 ∧ x ∉ jumps},
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)) := by
  rintro p hp _ ⟨x, ⟨hx, hxj⟩, rfl⟩
  exact ⟨hL x hx hxj, hH p hp x hx hxj⟩

end InteractingSLE.Theorem14.SB.Leaf
