import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.StableScale
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.SizeBinScale
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.StableScaleCore




 


set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem fbarV2_of_distance_scale
    {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC)
    (c : ℝ)
    (hDscale : ∀ x y : ℂ,
      D (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D g (x, y))
    (hD'scale : ∀ x y : ℂ,
      D' (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * D' g (x, y))
    (hF : EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z g) :
    EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar
      r b q K₁ K₂ obj Z (LQGMetric.addConst g c) := by
  let k := Real.exp ((ξ : ℝ) * c)
  have hk : 0 < k := Real.exp_pos _
  rcases hF with ⟨hne, hconf, hbr, havg, hbad, hloc, P, T, hgeo, hhit⟩
  refine ⟨hne, hconf, hbr + c,
    isCircleAverage_addConst g b 0 hbr c havg, ?_, ?_,
    P ∘ fun t => t / k, k * T,
    uniqueSetGeodesic_rescale (D g) (D (LQGMetric.addConst g c))
      k hk hDscale K₁ K₂ P T hgeo, ?_⟩
  · rw [setDist_rescale (D' g) (D' (LQGMetric.addConst g c)) k hk hD'scale,
      setDist_rescale (D g) (D (LQGMetric.addConst g c)) k hk hDscale,
      errorTerm_addConst]
    change cPlus * (ENNReal.ofReal k * OptimalConstants.Ratios.setDist (D g) K₁ K₂) -
        ENNReal.ofReal k *
          ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * hbr)) ≤
      ENNReal.ofReal k * OptimalConstants.Ratios.setDist (D' g) K₁ K₂
    calc
      _ = ENNReal.ofReal k *
          (cPlus * OptimalConstants.Ratios.setDist (D g) K₁ K₂ -
            ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
              Real.exp ((ξ : ℝ) * hbr))) := by
                rw [ENNReal.mul_sub (fun _ _ => ENNReal.ofReal_ne_top)]
                ac_rfl
      _ ≤ _ := by gcongr
  · intro i hi
    rcases hloc i hi with ⟨hE, a, ha, hbin⟩
    refine ⟨((obj i).E_constant g c).1 hE, a + c,
      isCircleAverage_addConst g r
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) a c ha,
      localSizeBin_addConst ξ Q r b q a hbr c hbin⟩
  · intro i hi
    obtain ⟨t, ht, hball⟩ := hhit i hi
    refine ⟨k * t, ?_, ?_⟩
    · exact ⟨mul_nonneg hk.le ht.1, mul_le_mul_of_nonneg_left ht.2 hk.le⟩
    · simpa only [Function.comp_def, show (k * t) / k = t by field_simp] using hball

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
