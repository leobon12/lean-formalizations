/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2EraseStep
import InteractingSLE.Spec.Supplement.SBLeafSB3

/-!
# The initial and relative pair comparisons in SB3's induction

Packet PROVE-T14-SBTAIL2. SB1 handles distinct relative seeds and S6 handles a
coincident pair of seeds, with an empty middle interval. Both statements are
explicit named hypotheses here: their finite terminal-endpoint claims remain
unproved. Given them, the relative ordered-completion premise of an erasure
step follows from genuine flow-line laws and the hybrid boundary word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE.Theorem14.SB.Erase

/-- Ordered completions imply S1 for the lower prefix, by the proved Jordan-side
duality. The separately labelled original-real bridge may also be retained. -/
theorem isOneSided_union_bridge_of_ordered {α β : ℝ≥0 → ℂ} {d a : ℝ≥0} {u v : ℝ}
    (hα0 : α 0 = v) (hβ0 : β 0 = u) (huv : u ≤ v)
    (hord : HasOrderedProperCompletions α d β a) :
    IsOneSided (α '' Icc 0 d ∪ ((↑) : ℝ → ℂ) '' Icc u 0) β a := by
  obtain ⟨α', β', hα', hβ', hleft⟩ := hord
  have hα'0 : α' 0 = v := (hα'.2.2.2.2 0 zero_le).trans hα0
  have hβ'0 : β' 0 = u := (hβ'.2.2.2.2 0 zero_le).trans hβ0
  have hright := Supp9B.range_subset_closedRightSide
    (Supp9B.isProperCurve_of_isProperCompletion hα')
    (Supp9B.isProperCurve_of_isProperCompletion hβ')
    (by rw [hα'0]; rfl) (by rw [hβ'0]; rfl)
    (by simpa only [hα'0, hβ'0, Complex.ofReal_re] using huv) hleft
  apply IsOneSided.union_bridge (β := β) (a := a) (u := u) _ hβ0
  refine ⟨β', hβ', ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hright ⟨t, hα'.2.2.2.2 t ht.2⟩

/-- The hybrid comparison also covers coincident seeds: its middle conditions
are then empty, and S6 supplies the finite terminal comparisons. -/
theorem ae_ordered_of_hybrid (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h b jumps)
    {u v ψ : ℝ} (huv : u ≤ v) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {α β : Ω → ℝ≥0 → ℂ} {ζα ζβ : Ω → ℝ≥0∞}
    (hα : IsFlowLine κ b jumps v (-(Real.pi / 2)) Q h α ζα)
    (hβ : IsFlowLine κ b jumps u ψ Q h β ζβ)
    (hζα : ∀ᵐ ω ∂Q, 0 < ζα ω) (hζβ : ∀ᵐ ω ∂Q, 0 < ζβ ω) :
    ∀ᵐ ω ∂Q, ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζα ω → (a : ℝ≥0∞) ≤ ζβ ω →
      HasOrderedProperCompletions (α ω) d (β ω) a := by
  rcases huv.eq_or_lt with heq | hlt
  · subst v
    exact hS6 κ hκ hκ4 b jumps hb u u (-(Real.pi / 2)) ψ le_rfl hψ hL
      (fun x hx _ => False.elim (lt_irrefl u (hx.1.trans hx.2)))
      Q h hh α β ζα ζβ hα hβ hζα hζβ
  · exact hSB1 κ hκ hκ4 b jumps hb Q h hh u v ψ hlt hψ hL hH
      α β ζα ζβ hα hβ hζα hζβ

/-- The source's base ordinary piece, with its original-real bridge, from the
hybrid pair comparison. All available finite stops, including terminal ones,
hold on one event. -/
theorem ae_isOneSided_base_of_hybrid (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h b jumps)
    {u v ψ : ℝ} (huv : u ≤ v) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {α β : Ω → ℝ≥0 → ℂ} {ζα ζβ : Ω → ℝ≥0∞}
    (hα : IsFlowLine κ b jumps v (-(Real.pi / 2)) Q h α ζα)
    (hβ : IsFlowLine κ b jumps u ψ Q h β ζβ)
    (hζα : ∀ᵐ ω ∂Q, 0 < ζα ω) (hζβ : ∀ᵐ ω ∂Q, 0 < ζβ ω) :
    ∀ᵐ ω ∂Q, ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζα ω → (a : ℝ≥0∞) ≤ ζβ ω →
      IsOneSided (α ω '' Icc 0 d ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (β ω) a := by
  filter_upwards [ae_ordered_of_hybrid hSB1 hS6 hκ hκ4 hb hh huv hψ hL hH hα hβ hζα hζβ,
    IsFlowLine.ae_seed_continuousOn hα, IsFlowLine.ae_seed_continuousOn hβ]
    with ω hord hαω hβω d a hd ha
  exact isOneSided_union_bridge_of_ordered hαω.1 hβω.1 huv (hord d a hd ha)

end InteractingSLE.Theorem14.SB.Erase
