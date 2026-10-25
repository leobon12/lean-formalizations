import SupercriticalLQGUniqueness.Exponent.InwardMap.OpenAnnulusFamily




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

def gradientSup (f : ℂ → ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖fderiv ℝ f z‖) '' gradientBox)

private theorem gradientBox_compact : IsCompact gradientBox :=
  isCompact_Icc.reProdIm isCompact_Icc

private theorem gradientBox_nonempty : gradientBox.Nonempty := by
  refine ⟨0, ?_⟩
  simp [gradientBox, Complex.mem_reProdIm]

theorem gradientSup_bound (f : ℂ → ℝ)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox) :
    ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ gradientSup f := by
  intro z hz
  exact le_csSup (gradientBox_compact.bddAbove_image hfc.norm)
    (Set.mem_image_of_mem _ hz)

theorem gradientSup_nonneg (f : ℂ → ℝ)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox) :
    0 ≤ gradientSup f := by
  obtain ⟨z, hz⟩ := gradientBox_nonempty
  exact (norm_nonneg _).trans (gradientSup_bound f hfc z hz)

theorem mappedFourBandFamily_cost_le_gradientSup (a : ℚ) (ha0 : 0 ≤ a)
    (ha : (a:ℝ) ≤ 1/256) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox)
    (F : Exponent.PolygonalCost.RationalFourBand ξ f) :
    (mappedFourBandFamily a F).cost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*gradientSup f))) * F.cost :=
  mappedFourBandFamily_cost_le a ha0 ha ξ (gradientSup f) hξ
    (gradientSup_nonneg f hfc) f hfd (gradientSup_bound f hfc) F


end SupercriticalLQGUniqueness.Exponent.InwardMap
