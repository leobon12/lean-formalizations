import SupercriticalLQGUniqueness.B2.DG20Lim.RationalAnnulusAffine

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem exists_rational_good_annulus_ratio_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
      ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
        (∀ e, IsHeatSmoothing P h e (X e)) →
      ∀ x y r : ℚ, ∀ hr : 0 < r, ∀ δ : Ioo (0 : ℝ) 1,
        (δ : ℝ) < δ₀ →
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos (Rat.cast_pos.mpr hr) δ.property.1⟩
        let D : Ω → ContMetric :=
          fun ω => normalizedContLFPP (ξ : ℝ) (m e) (X e ω)
        P {ω | ENNReal.ofReal C *
          finiteCircleCoords (D ω)
            (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
          finiteAroundCoords (D ω) (centeredRatAnnulus x y r hr)} ≤
          ENNReal.ofReal η := by
  obtain ⟨C, δ₀, hC, hδ₀, hgood⟩ :=
    exists_uniform_good_annulus_ratio_tail_of_inputs
      hS4 hPerc ξ Q hQ m hm η hη
  refine ⟨C, δ₀, hC, hδ₀, ?_⟩
  intro Ω _ P _ h hh X hX x y r hr δ hδ
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  let rr : Ioi (0 : ℝ) := ⟨(r : ℝ), hrR⟩
  have hb := hgood P h hh X hX (Complex.mk (x : ℝ) (y : ℝ)) rr δ hδ
  dsimp [rr, B2.Polylog.dilateHomeo] at hb
  have hT :
      (⇑(Homeomorph.smulOfNeZero (r : ℝ) hrR.ne') : ℂ → ℂ) =
        fun w => (r : ℝ) • w := rfl
  rw [hT] at hb
  have hInner :
      (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
        ((fun w : ℂ => (r : ℝ) • w) '' unitInnerCircle.toSet) =
        (centeredInnerCircle x y r hr).toSet :=
    centeredInnerCircle_affine x y r hr
  have hOuter :
      (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
        ((fun w : ℂ => (r : ℝ) • w) '' unitOuterCircle.toSet) =
        (centeredOuterCircle x y r hr).toSet :=
    centeredOuterCircle_affine x y r hr
  have hAnn :
      (fun w : ℂ => w + Complex.mk (x : ℝ) (y : ℝ)) ''
        ((fun w : ℂ => (r : ℝ) • w) '' unitRatAnnulus.toSet) =
        (centeredRatAnnulus x y r hr).toSet :=
    centeredRatAnnulus_affine x y r hr
  rw [hInner, hOuter, hAnn] at hb
  have hi : (centeredRatAnnulus x y r hr).inner =
      centeredInnerCircle x y r hr := rfl
  have ho : (centeredRatAnnulus x y r hr).outer =
      centeredOuterCircle x y r hr := rfl
  simpa only [finiteCircleCoords, finiteAroundCoords, hi, ho] using hb

end SupercriticalLQGUniqueness.B2.DG20Lim
