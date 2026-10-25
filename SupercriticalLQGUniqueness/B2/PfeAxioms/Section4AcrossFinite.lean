import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4BufferedFinite
import SupercriticalLQGUniqueness.B2.Strong.Annulus

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_acrossDist_lt_top_of_section4_buffered
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioo (0 : ℝ) 1)
    (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m
      (fun n => ⟨(ε n : ℝ), (ε n).property.1⟩) D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (A : EuclideanAnnulus)
    (V : TopologicalSpace.Opens ℂ) (hVc : IsConnected (V : Set ℂ))
    (hVcompact : IsCompact (closure (V : Set ℂ)))
    (x y : V) (hx : (x : ℂ) ∈ A.innerBoundary)
    (hy : (y : ℂ) ∈ A.outerBoundary) :
    ∀ᵐ ω ∂P, acrossDist (D (h ω)) A < ∞ := by
  have hxy : (x : ℂ) ≠ (y : ℂ) := by
    intro he
    exact Set.disjoint_left.mp (B2.Strong.disjoint_boundaries A) hx (he ▸ hy)
  have hfinite := ae_internal_lt_top_of_section4_buffered hS ξ Q hQ m hm ε D hD
    P h hh X hX V hVc subset_closure hVcompact (subset_univ _)
    x y hxy
  filter_upwards [hfinite] with ω hω
  calc
    acrossDist (D (h ω)) A ≤ D (h ω) ((x : ℂ), (y : ℂ)) :=
      iInf₂_le_of_le _ hx (iInf₂_le _ hy)
    _ ≤ (D (h ω)).internal Set.univ
      (⟨(x : ℂ), Set.mem_univ _⟩, ⟨(y : ℂ), Set.mem_univ _⟩) :=
        B2.PfeLocal.edist_le_internal (D (h ω)) Set.univ
          (⟨(x : ℂ), Set.mem_univ _⟩, ⟨(y : ℂ), Set.mem_univ _⟩)
    _ < ∞ := hω

end SupercriticalLQGUniqueness.B2.PfeAxioms
