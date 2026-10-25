import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableBddLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableOpenFactorSB

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_internal_local_factor_bdd_of_geometry
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hGeom : ∀ᵐ ω ∂P,
      ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hAnn : ∀ K V : Set ℂ,
      IsCompact K → IsOpen V → IsCompact (closure V) → K ⊆ V →
      ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (D (h ω)) K V)
    (U : TopologicalSpace.Opens ℂ) (x y : U) :
    ∃ F : DistC → ℝ≥0∞,
      Measurable F ∧
      (∀ᵐ ω ∂P,
        (D (h ω)).internal (U : Set ℂ) (x, y) = F (h ω)) ∧
      MeasurableSpace.comap (fun ω => F (h ω)) inferInstance ≤
        LQGMetric.Blueprint.fieldSigma h U := by
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
  have hxV : ∀ n, (x : ℂ) ∈ V n := fun n =>
    (hgeo n).2.2.2.2.2.2.2.2.2.1
      (subset_closure (hgeo n).2.2.2.2.1)
  have hyV : ∀ n, (y : ℂ) ∈ V n := fun n =>
    (hgeo n).2.2.2.2.2.2.2.2.2.1
      (subset_closure (hgeo n).2.2.2.2.2.1)
  let F := countableLocalizedObservable ξ m ε V x y hxV hyV
  refine ⟨F, ?_, ?_, ?_⟩
  · exact measurable_countableLocalizedObservable ξ m ε V x y hxV hyV
      (fun n => (hgeo n).2.2.2.2.2.2.1)
      (fun n => (hgeo n).2.2.2.2.2.2.2.1.isBounded.subset subset_closure)
  · exact ae_internal_eq_countable_localized_bdd_of_geometry
      ξ m ε hε D hD P h hh X hX hGeom H x y W V hgeo hsmall
  · exact comap_countableLocalizedObservable_le_fieldSigma
      ξ m ε hε V (x : ℂ) (y : ℂ) hxV hyV
      (fun n => (hgeo n).2.2.2.2.2.2.1)
      (fun n => (hgeo n).2.2.2.2.2.2.2.1.isBounded.subset subset_closure)
      (fun n => (hgeo n).2.2.2.2.2.2.2.1) U
      (fun n => (hgeo n).2.2.2.2.2.2.2.2.1) h

end SupercriticalLQGUniqueness.B2.PfeAxioms
