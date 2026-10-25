import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryTransferC

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem ae_internal_eq_countable_heat_observable_of_smallAnnulusCosts_skC
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
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
    ∀ᵐ ω ∂P,
      (D (h ω)).internal U (x, y) =
        ⨅ n : ℕ, lowerNeighborhoodObservable
          (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
            (m (ε k)) (X (ε k) ω)) (V n)
          ⟨(x : ℂ),
            (hgeo n).2.2.2.2.2.2.2.2.2.1
              (subset_closure (hgeo n).2.2.2.2.1)⟩
          ⟨(y : ℂ),
            (hgeo n).2.2.2.2.2.2.2.2.2.1
              (subset_closure (hgeo n).2.2.2.2.2.1)⟩ := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  letI : BorelSpace LSCFun := ⟨rfl⟩
  have hGeom := B2.DG20Lim.ae_geometry_of_dg20LimitSkC
    hSkSB ξ Q hQ m hm ε hε D hD P h hh
  have hConv := ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX
  filter_upwards [hGeom, hConv, hsmall] with ω hGω hCω hSω
  have hfinite := normalizedLFPPMetric_finite_geometry
    (ξ : ℝ) (fun k => m (ε k)) (fun k => X (ε k) ω)
  have hforget : Continuous (PfeWeyl.euclidForget (D (h ω))) := by
    exact B2.PfeLocal.continuous_euclidForget_of_small_metric
      (D (h ω)) hGω.2.1
  exact internal_eq_iInf_lowerNeighborhoodObservable_of_smallAnnulusCosts
    hCω hfinite.1 hfinite.2.1 hfinite.2.2 hforget
    H x y W V hgeo hSω

end SupercriticalLQGUniqueness.B2.PfeAxioms
