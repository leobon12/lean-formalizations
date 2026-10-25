import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableJointLawSB

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem joint_law_internal_of_smallAnnulusCosts_on_open
    (hStrong : Inputs.DG20LimitStrongSB)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V)
    (U : TopologicalSpace.Opens ℂ) (x y : U) :
    ∃ (F : DistC → ℝ≥0∞), Measurable F ∧
      P.map (fun ω => (h ω, (D (h ω)).internal (U : Set ℂ) (x, y))) =
        P.map (fun ω => (h ω, F (h ω))) := by
  let H : CompactExhaustion U := CompactExhaustion.choice U
  obtain ⟨W, V, hgeo⟩ := exists_countable_nested_buffers U.isOpen H x y
  have hsmall : ∀ᵐ ω ∂P, ∀ n,
      PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω))
        (D (h ω)) (closure (W n)) (V n) := by
    apply ae_all_iff.mpr
    intro n
    exact hAnn (closure (W n)) (V n)
      (hgeo n).2.1 (hgeo n).2.2.2.2.2.2.1
      (hgeo n).2.2.2.2.2.2.2.1 (hgeo n).2.2.2.2.2.2.2.2.2.1
  exact joint_law_internal_countableLocalized_of_smallAnnulusCosts
    hStrong ξ Q hQ m hm ε hε D hD P h hh X hX H x y W V hgeo hsmall

end SupercriticalLQGUniqueness.B2.PfeAxioms
