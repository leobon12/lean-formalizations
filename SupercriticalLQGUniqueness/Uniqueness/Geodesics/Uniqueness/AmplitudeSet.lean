import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.NoTiePlateau
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2




 






set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC)

 

theorem badSetGeodesic_amplitudes_subsingleton
    (D : DistC → LSCMetric) (ξ : ℝ) (hξ : 0 < ξ)
    (g : DistC) (hreg : EndSaving.Choices.RegularAt D ξ g)
    (f : C(ℂ, ℝ)) (hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1)
    (K₁ K₂ U V : Set ℂ) (hV : IsOpen V)
    (hV₁ : Disjoint V K₁) (hV₂ : Disjoint V K₂)
    (hfU : ∀ z ∉ U, f z = 0) (hfV : ∀ z ∈ V, f z = 1) :
    {a : ℝ | 0 ≤ a ∧
      Geodesics.SetGeodesics.BadSetGeodesic (D (LQGMetric.addFun g (a • f))) K₁ K₂ U V}.Subsingleton := by
  intro a ha b hb
  rcases lt_trichotomy a b with hab | hab | hab
  · have h₁ (p : ℂ × ℂ) :
        D (LQGMetric.addFun g (a • f)) p =
          weylScale ξ (a • f) (D g) p :=
      (congrFun (hreg.weyl (a • f)) p).symm
    have h₂ (p : ℂ × ℂ) :
        D (LQGMetric.addFun g (b • f)) p =
          weylScale ξ (b • f) (D g) p :=
      (congrFun (hreg.weyl (b • f)) p).symm
    exact False.elim (badSetGeodesic_no_later_amplitude
      (D g) (D (LQGMetric.addFun g (a • f)))
      (D (LQGMetric.addFun g (b • f))) ξ a b hξ ha.1 hab f hf
      hreg.forget hreg.length h₁ h₂ K₁ K₂ U V hV hV₁ hV₂ hfU hfV ha.2 hb.2)
  · exact hab
  · have h₁ (p : ℂ × ℂ) :
        D (LQGMetric.addFun g (b • f)) p =
          weylScale ξ (b • f) (D g) p :=
      (congrFun (hreg.weyl (b • f)) p).symm
    have h₂ (p : ℂ × ℂ) :
        D (LQGMetric.addFun g (a • f)) p =
          weylScale ξ (a • f) (D g) p :=
      (congrFun (hreg.weyl (a • f)) p).symm
    exact False.elim (badSetGeodesic_no_later_amplitude
      (D g) (D (LQGMetric.addFun g (b • f)))
      (D (LQGMetric.addFun g (a • f))) ξ b a hξ hb.1 hab f hf
      hreg.forget hreg.length h₁ h₂ K₁ K₂ U V hV hV₁ hV₂ hfU hfV hb.2 ha.2)

 

theorem ae_volume_bad_amplitudes_eq_zero
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (f : C(ℂ, ℝ)) (hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1)
    (K₁ K₂ U V : Set ℂ) (hV : IsOpen V)
    (hV₁ : Disjoint V K₁) (hV₂ : Disjoint V K₂)
    (hfU : ∀ z ∉ U, f z = 0) (hfV : ∀ z ∈ V, f z = 1) :
    ∀ᵐ ω ∂μ,
      volume {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
        Geodesics.SetGeodesics.BadSetGeodesic
          (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V} = 0 := by
  filter_upwards [EndSaving.Choices.ae_regularAt_self hD μ h hh] with ω hreg
  have hsub := badSetGeodesic_amplitudes_subsingleton D (ξ : ℝ) ξ.2
    (h ω) hreg f hf K₁ K₂ U V hV hV₁ hV₂ hfU hfV
  have hsub' : {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
      Geodesics.SetGeodesics.BadSetGeodesic
        (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V}.Subsingleton := by
    intro a ha b hb
    exact hsub ⟨ha.1.1, ha.2⟩ ⟨hb.1.1, hb.2⟩
  exact hsub'.measure_zero volume

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
