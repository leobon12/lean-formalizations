import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TAssembly
import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TCoords

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem r68_subseqLimit_of_normalized_of_inputs
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ)) (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate')
    (hPos : DG20ExponentPositive)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L)
    (hZ : Final.CoupledRatCoords ξ m e V P' hN L)
    (Φ : DistC → LSCMetric) (hΦm : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    (hW3 : FixedFieldWeylAllBounded ξ m e Φ)
    (hgeo : NormalizedLimitGeometry Φ)
    (hweyl : BoundedShiftWeyl ξ Φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ SubseqLimit ξ m (e ∘ ψ) Φ := by
  have hCirc : CoupledAllRationalCircles ξ m e V P' hN L :=
    coupledAllRationalCircles_of_coords hS4 hPerc hPos hB hSA hZ
  obtain ⟨ψ, hψ, hcount⟩ :=
    exists_fixedField_weyl_rationalCircle_countable_of_coupling
      ξ Q m e c V P' h' hN L hB hSA hAT hCirc Φ hΦm hII hweyl
      upperShiftFamily upperShiftBound upperShiftFamily_bound
  have hW3' : FixedFieldWeylAllBounded ξ m (e ∘ ψ) Φ :=
    fixedFieldWeylAllBounded_comp hW3 hψ
  have hcircles : FixedFieldWeylAllCircles ξ m (e ∘ ψ) Φ :=
    ae_weyl_rationalCircle_all_bounded_of_upper_squeeze
      ξ m (e ∘ ψ) Φ hW3' hgeo upperShiftFamily upperShiftBound
      upperShiftFamily_bound upperShiftFamily_countableUpperShifts hcount
  exact ⟨ψ, hψ,
    subseqLimit_of_fixedFieldWeyl_and_circles ξ m (e ∘ ψ) Φ hW3' hcircles hweyl⟩

 
theorem r68_subseqLimit_of_normalized_of_pfeWeak
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ)) (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate')
    (hPos : DG20ExponentPositive)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L)
    (hZ : Final.CoupledRatCoords ξ m e V P' hN L)
    (Φ : DistC → LSCMetric) (hΦm : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    (hW3 : FixedFieldWeylAllBounded ξ m e Φ)
    (hgeo : NormalizedLimitGeometry Φ)
    (hPfe : IsPfeWeakMetric ξ Φ c) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ SubseqLimit ξ m (e ∘ ψ) Φ :=
  r68_subseqLimit_of_normalized_of_inputs ξ Q m e c V P' h' hN L
    hS4 hPerc hPos hB hSA hAT hZ Φ hΦm hII hW3 hgeo
    (r68_boundedShiftWeyl_of_isPfeWeakMetric hPfe)

end SupercriticalLQGUniqueness.B2.PfeWeyl
