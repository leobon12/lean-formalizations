import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableJointLawSB
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedLimitSkC

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem joint_law_internal_countableLocalized_of_smallAnnulusCosts_skC
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
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
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U)
    (W V : ℕ → Set ℂ)
    (hgeo : ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n ∧
      IsOpen (V n) ∧ IsCompact (closure (V n)) ∧
      closure (V n) ⊆ U ∧ closure (W n) ⊆ V n ∧
      IsCompact (frontier (V n)) ∧
      (frontier (V n)).Nonempty ∧
      Disjoint (closure (W n)) (frontier (V n)))
    (hsmall : ∀ᵐ ω ∂P, ∀ n,
      PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω))
        (D (h ω)) (closure (W n)) (V n)) :
    ∃ (F : DistC → ℝ≥0∞), Measurable F ∧
      P.map (fun ω => (h ω, (D (h ω)).internal U (x, y))) =
        P.map (fun ω => (h ω, F (h ω))) := by
  have hxV : ∀ n, (x : ℂ) ∈ V n := fun n =>
    (hgeo n).2.2.2.2.2.2.2.2.2.1
      (subset_closure (hgeo n).2.2.2.2.1)
  have hyV : ∀ n, (y : ℂ) ∈ V n := fun n =>
    (hgeo n).2.2.2.2.2.2.2.2.2.1
      (subset_closure (hgeo n).2.2.2.2.2.1)
  let F := countableLocalizedObservable ξ m ε V x y hxV hyV
  refine ⟨F, ?_, ?_⟩
  · exact measurable_countableLocalizedObservable ξ m ε V x y hxV hyV
      (fun n => (hgeo n).2.2.2.2.2.2.1)
      (fun n => (hgeo n).2.2.2.2.2.2.2.1.isBounded.subset subset_closure)
  · apply Measure.map_congr
    filter_upwards [ae_internal_eq_countable_localized_observable_of_smallAnnulusCosts_skC
      hSkSB ξ Q hQ m hm ε hε D hD P h hh X hX H x y W V hgeo hsmall]
      with ω hω
    exact congrArg (fun d : ℝ≥0∞ => (h ω, d)) hω

end SupercriticalLQGUniqueness.B2.PfeAxioms
