/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2EraseClock
import InteractingSLE.Spec.Supplement.SB4SwitchWords

/-!
# SB3's protected-word comparison and physical gluing with separate clocks

Packet PROVE-T14-SBTAIL2. These are conditional helpers, not providers for SB3
or SB4. SB1/S6 are named mathematical inputs. The actual conditional field,
exhaustive surviving-height classification, relative clocks and pullback
identity are still needed to instantiate them at a lower-walk launch.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

universe u

namespace InteractingSLE.Theorem14.SB.Erase

/-- SB3's surviving low sides and retained original bridge give the hybrid
comparison. The low-height arithmetic is reused from `switch_hybrid_low`.
The exhaustive classification is an explicit geometric hypothesis. -/
theorem ae_ordered_of_low_or_original (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h b jumps)
    {w ψ : ℝ} (hw : 0 ≤ w) (hψ : -(Real.pi / 2) < ψ) {original : Set ℝ}
    (hbridge : ∀ B ∈ original,
      -2 < Sec4.cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < Sec4.cumWeightRight κ (B + ψ * chiC κ) ∨
          κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (htypes : ∀ x ∈ Ioo 0 w, x ∉ jumps →
      b x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨ b x ∈ original)
    {α β : Ω → ℝ≥0 → ℂ} {ζα ζβ : Ω → ℝ≥0∞}
    (hα : IsFlowLine κ b jumps w (-(Real.pi / 2)) Q h α ζα)
    (hβ : IsFlowLine κ b jumps 0 ψ Q h β ζβ)
    (hζα : ∀ᵐ ω ∂Q, 0 < ζα ω) (hζβ : ∀ᵐ ω ∂Q, 0 < ζβ ω) :
    ∀ᵐ ω ∂Q, ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζα ω → (a : ℝ≥0∞) ≤ ζβ ω →
      HasOrderedProperCompletions (α ω) d (β ω) a := by
  have hword : ∀ x ∈ Ioo 0 w, x ∉ jumps →
      -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ) ∧
        (-2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
          κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) := by
    intro x hx hj
    rcases htypes x hx hj with hlow | horig
    · exact switch_hybrid_low hκ hκ4 hlow
    · exact hbridge (b x) horig
  exact ae_ordered_of_hybrid hSB1 hS6 hκ hκ4 hb hh hw hψ
    (fun x hx hj => (hword x hx hj).1) (fun x hx hj => (hword x hx hj).2)
    hα hβ hζα hζβ

/-- An almost-everywhere relative pair comparison can be read in independently
chosen physical clocks. No measurability of these pathwise clock choices is
needed: one common event already contains every available pair of stops. -/
theorem ae_ordered_comp_prefixClocks {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    {α β : Ω → ℝ≥0 → ℂ} {ζα ζβ : Ω → ℝ≥0∞}
    {τ σ : Ω → ℝ≥0 → ℝ≥0} {d a : Ω → ℝ≥0}
    (hpair : ∀ᵐ ω ∂Q, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζα ω → (t : ℝ≥0∞) ≤ ζβ ω →
      HasOrderedProperCompletions (α ω) s (β ω) t)
    (hclock : ∀ᵐ ω ∂Q,
      ContinuousOn (τ ω) (Iic (d ω)) ∧ StrictMonoOn (τ ω) (Iic (d ω)) ∧ τ ω 0 = 0 ∧
      ContinuousOn (σ ω) (Iic (a ω)) ∧ StrictMonoOn (σ ω) (Iic (a ω)) ∧ σ ω 0 = 0 ∧
      (τ ω (d ω) : ℝ≥0∞) ≤ ζα ω ∧ (σ ω (a ω) : ℝ≥0∞) ≤ ζβ ω) :
    ∀ᵐ ω ∂Q, HasOrderedProperCompletions (α ω ∘ τ ω) (d ω) (β ω ∘ σ ω) (a ω) := by
  filter_upwards [hpair, hclock] with ω hp hc
  obtain ⟨hτc, hτm, hτ0, hσc, hσm, hσ0, hd, ha⟩ := hc
  exact ordered_comp_prefixClocks hτc hτm hτ0 hσc hσm hσ0 (hp _ _ hd ha)

/-- S5's actual physical gluing step from capacity-parametrized relative
prefixes and their finite clocks. The original upper curve itself keeps its
physical parametrization. -/
theorem erasureStep_of_relative_clocks {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0}
    {c : Chart} {g : ℂ → ℂ} {tL a₁ : ℝ≥0} {αR βR : ℝ≥0 → ℂ}
    {τ σ : ℝ≥0 → ℝ≥0} {w : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite)
    (ht : tL ≤ a) (hL : β tL = realMin (p '' Icc 0 1)) (hbR0 : βR 0 = 0)
    (hrel : ∀ s : ℝ≥0, s ≤ a - tL → g (βR (σ s)) = β (tL + s))
    (hw : 0 ≤ w) (haR0 : αR 0 = w)
    (hτc : ContinuousOn τ (Iic a₁)) (hτm : StrictMonoOn τ (Iic a₁)) (hτ0 : τ 0 = 0)
    (hσc : ContinuousOn σ (Iic (a - tL))) (hσm : StrictMonoOn σ (Iic (a - tL)))
    (hσ0 : σ 0 = 0)
    (hord : HasOrderedProperCompletions αR (τ a₁) βR (σ (a - tL))) :
    ErasureStep β a (p '' Icc 0 1) (p '' Icc 0 1 ∪ g '' ((αR ∘ τ) '' Icc 0 a₁)) := by
  apply ErasureStep.relative hp hp0 hpH hβ0 hc hgc hgi hgf ht hL
    (bR := βR ∘ σ) (w := w)
  · exact (congrArg βR hσ0).trans hbR0
  · exact hrel
  · exact hw
  · exact (congrArg αR hτ0).trans haR0
  · exact ordered_comp_prefixClocks hτc hτm hτ0 hσc hσm hσ0 hord

end InteractingSLE.Theorem14.SB.Erase
