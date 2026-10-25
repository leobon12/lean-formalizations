import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicSparseRadiusBounds

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_eventually_good_lattice_rdata_of_coord_good
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Ylim : Ω → (CoordJ → ℝ) × RatCoords) (C : ℝ≥0∞)
    (hRData : ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2)
    (hGood : ∀ᵐ ω ∂P, ∀ M : ℕ, ∀ᶠ K in atTop,
      ∀ v ∈ dyadicLatticeBox M K, ω ∉ coupledSiteBad Ylim C K v) :
    ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      ∀ M : ℕ, ∀ᶠ K in atTop,
        ∀ v ∈ dyadicLatticeBox M K, dyadicGoodAt R C K v := by
  filter_upwards [hRData, hGood] with ω hR hG
  obtain ⟨R, hA, hB⟩ := hR
  refine ⟨R, hA, hB, ?_⟩
  intro M
  filter_upwards [hG M] with K hK v hv
  exact dyadicGoodAt_of_not_coupledSiteBad Ylim ω R C K v hA hB (hK v hv)

end SupercriticalLQGUniqueness.B2.DG20Lim
