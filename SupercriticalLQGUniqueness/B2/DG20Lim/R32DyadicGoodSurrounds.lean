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
import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeCover

 



set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem dyadic_mesh_lt_sparse_radiusR32 {K i : ℕ}
    (hi : i ∈ sparseDyadicIndices K) :
    2 / (2 : ℝ) ^ (K + 4) < (ratRad64 1 i : ℝ) := by
  have hscale := (sparseDyadicIndices_scale hi).2
  have hpow : (2 : ℝ) ^ (6 * i) ≤ (2 : ℝ) ^ K := by gcongr; norm_num
  have hden : 2 * (2 : ℝ) ^ K < (2 : ℝ) ^ (K + 4) := by
    rw [pow_add]
    norm_num
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]
  rw [ratRad64_one_eq_dyadic]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  have hp1 : 0 < (2 : ℝ) ^ (K + 4) := by positivity
  have hp2 : 0 < (2 : ℝ) ^ K := by positivity
  have hp3 : 0 < (2 : ℝ) ^ (6 * i) := by positivity
  calc
    2 / (2 : ℝ) ^ (K + 4) < 1 / (2 : ℝ) ^ K := by
      apply (div_lt_div_iff₀ hp1 hp2).mpr
      nlinarith
    _ ≤ 1 / (2 : ℝ) ^ (6 * i) := by
      apply (div_le_div_iff₀ hp2 hp3).mpr
      nlinarith

theorem dyadic_good_inner_surroundsR32 (K i : ℕ) (z : ℂ)
    (hi : i ∈ sparseDyadicIndices K) :
    (centeredRatAnnulusR32
      (dyadicLatticeCenter K (dyadicRoundCenter K z)).1
      (dyadicLatticeCenter K (dyadicRoundCenter K z)).2
      (ratRad64 1 i) (ratRad64_pos (by norm_num) i)).inner.Surrounds z := by
  have hd := dyadicRoundCenter_dist_lt K z
  have hr := dyadic_mesh_lt_sparse_radiusR32 hi
  refine ⟨?_, ?_⟩
  · simp [centeredRatAnnulusR32, centeredInnerCircleR32, ratRad64_pos]
  · change z ∈ ball
      (Complex.mk
        ((dyadicLatticeCenter K (dyadicRoundCenter K z)).1 : ℝ)
        ((dyadicLatticeCenter K (dyadicRoundCenter K z)).2 : ℝ))
      (ratRad64 1 i : ℝ)
    exact mem_ball.mpr (hd.trans hr)

end SupercriticalLQGUniqueness.B2.DG20Lim
