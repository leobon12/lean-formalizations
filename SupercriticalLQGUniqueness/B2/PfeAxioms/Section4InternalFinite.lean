import SupercriticalLQGUniqueness.B2.PfeAxioms.ConnectedCompactBuffer

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_internal_lt_top_of_section4
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
    (U : TopologicalSpace.Opens ℂ) (hUc : IsConnected (U : Set ℂ))
    (x y : U) (hxy : (x : ℂ) ≠ (y : ℂ)) :
    ∀ᵐ ω ∂P, (D (h ω)).internal U (x, y) < ∞ := by
  obtain ⟨V, hVc, hVcompact, hVU, hxV, hyV⟩ :=
    exists_connected_compact_buffer U hUc x y
  let xv : V := ⟨(x : ℂ), hxV⟩
  let yv : V := ⟨(y : ℂ), hyV⟩
  have hfin := ae_internal_lt_top_of_section4_buffered hS ξ Q hQ m hm
    ε D hD P h hh X hX V hVc subset_closure hVcompact hVU xv yv hxy
  simpa only [xv, yv, Subtype.coe_eta] using hfin

end SupercriticalLQGUniqueness.B2.PfeAxioms
