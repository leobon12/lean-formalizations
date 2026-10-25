import SupercriticalLQGUniqueness.B2.DG20Lim.R32UnitAnnulusCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.R32UnitGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32ScaledGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32TranslatedGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32UniformGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusAffine
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedRatAnnulusLocality
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.R32GoodAnnulusCoupledLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedMollifierSigma
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusBuffer
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodCostCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodHeatCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventualCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodSequenceTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodFullTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FullHeatGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.R32WiderAnnulusSupport
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodCostsLocal
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventLocal
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventCentered
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodRepresentative
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedLMAnnulus
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodIteration
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodMarginal
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FiniteGoodEvents
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodIterationEventual
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FullGoodIterationEventual
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FullGoodNormalize
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FiniteGoodCoupledLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicLatticeCoupledUnion
import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicLatticeEventual
import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicGoodSurrounds
import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicGoodRData
import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicGoodPoint
import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicSparseRadiusBounds

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_eventually_good_lattice_rdata_of_coord_goodR32
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Ylim : Ω → (CoordJ → ℝ) × RatCoords) (C : ℝ≥0∞)
    (hRData : ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2)
    (hGood : ∀ᵐ ω ∂P, ∀ M : ℕ, ∀ᶠ K in atTop,
      ∀ v ∈ dyadicLatticeBox M K, ω ∉ coupledSiteBadR32 Ylim C K v) :
    ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      ∀ M : ℕ, ∀ᶠ K in atTop,
        ∀ v ∈ dyadicLatticeBox M K, dyadicGoodAtR32 R C K v := by
  filter_upwards [hRData, hGood] with ω hR hG
  obtain ⟨R, hA, hB⟩ := hR
  refine ⟨R, hA, hB, ?_⟩
  intro M
  filter_upwards [hG M] with K hK v hv
  exact dyadicGoodAt_of_not_coupledSiteBadR32 Ylim ω R C K v hA hB (hK v hv)

end SupercriticalLQGUniqueness.B2.DG20Lim
