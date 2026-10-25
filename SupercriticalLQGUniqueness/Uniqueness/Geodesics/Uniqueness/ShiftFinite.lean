import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.CorrectedChoicesBridge




 

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC TestC)

theorem setDist_shift_lt_top_of_base_finite
    (D : DistC → LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : DistC) (hreg : EndSaving.Choices.RegularAt D ξ g)
    (φ : TestC) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hfin : OptimalConstants.Ratios.setDist (D g) K₁ K₂ < ⊤) :
    OptimalConstants.Ratios.setDist (D (LQGMetric.addFun g (LQGMetric.testCont φ))) K₁ K₂ < ⊤ := by
  obtain ⟨u, hu, v, hv, hmin⟩ := Geodesics.SetGeodesics.setDist_attained
    (D g) K₁ K₂ hK₁ hK₂ hne₁ hne₂
  have huv : D g (u, v) < ⊤ := hmin ▸ hfin
  obtain ⟨m, hm⟩ := EndSaving.Choices.testCont_bounded_below φ
  obtain ⟨M, hM⟩ := EndSaving.Choices.testCont_bounded_below (-φ)
  have hf : ∀ z : ℂ,
      -m ≤ LQGMetric.testCont φ z ∧ LQGMetric.testCont φ z ≤ M := by
    intro z
    refine ⟨hm z, ?_⟩
    have hz := hM z
    rw [EndSaving.Choices.testCont_neg] at hz
    change -M ≤ -(LQGMetric.testCont φ z) at hz
    linarith
  have hmetric : ∀ p : ℂ × ℂ,
      D (LQGMetric.addFun g (LQGMetric.testCont φ)) p =
        weylScale ξ (LQGMetric.testCont φ) (D g) p :=
    fun p => (congrFun (hreg.weyl (LQGMetric.testCont φ)) p).symm
  have hupper := Toolkit.WeylShift.distance_upper (D g)
    (D (LQGMetric.addFun g (LQGMetric.testCont φ))) ξ hξ
    (LQGMetric.testCont φ) (-m) M hreg.forget hmetric hf hreg.length u v
  have hfin' : D (LQGMetric.addFun g (LQGMetric.testCont φ)) (u, v) < ⊤ :=
    lt_of_le_of_lt hupper (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) huv)
  exact Geodesics.SetGeodesics.setDist_lt_top_of_pair _ K₁ K₂ u v hu hv hfin'

 

theorem ae_uniqueGeodesicEventV2_of_base_finite
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (b : Set.Ioi (0 : ℝ))
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ,
      OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ < ⊤ →
      EndSaving.Choices.UniqueGeodesicEventV2 μ h D D' ξ Q cMid par pbar R family
        b K₁ K₂ ω := by
  have hbridge := ae_uniqueGeodesicEventV2_of_finite_distances hD μ h hh
    cMid par pbar R family b K₁ K₂ hK₁ hK₂ hne₁ hne₂ hK
  filter_upwards [hbridge, EndSaving.Choices.ae_regularAt_self hD μ h hh] with ω hb hreg hfin
  apply hb hfin
  intro r hr W _ _
  have hshift := setDist_shift_lt_top_of_base_finite D (ξ : ℝ) ξ.2.le
    (h ω) hreg
    (-(EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r
      (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) W))
    K₁ K₂ hK₁ hK₂ hne₁ hne₂ hfin
  simpa only [EndSaving.FiniteEvents.subtractBumpsV2, EndSaving.Choices.subTest_eq_addFun] using hshift

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
