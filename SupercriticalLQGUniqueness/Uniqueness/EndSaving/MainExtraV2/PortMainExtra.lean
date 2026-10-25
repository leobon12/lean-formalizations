import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.MainExtra
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.AssemblyV2




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtraV2
open LQGMetric (DistC)

theorem lemMainExtraV2 :
    ∃ pbar : Set.Ioo (0 : ℝ) 1,
      ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus < cPlus →
      ∀ objs : EndSaving.InterfaceV2.ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar,
      ∀ (κ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
        ∃ ε₀ : Set.Ioo (0 : ℝ) 1, ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ j : ℕ,
          ENNReal.ofReal (κ : ℝ) ≤
            P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (EndSaving.Interfaces.dyadicRadius j) κ
              ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
          ENNReal.ofReal (1 - (η : ℝ)) ≤
            P (EndSaving.InterfaceV2.AuxiliaryGoodV2 h ξ Q objs.radii (fun z r hr => (objs.family z r hr).E)
              (EndSaving.Interfaces.dyadicRadius j) ⟨ε, hε⟩) := by
  obtain ⟨p, hp0, hp1, C, ε₁, hC, hε₁, hε₁1, Hcore⟩ := EndSaving.MainExtra.auxiliaryGood_prob_core
  refine ⟨⟨p, hp0, hp1⟩, ?_⟩
  intro ξ Q D D' hD _ Ω _ P _ h hh cMinus cPlus _ _ _ objs κ η
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  obtain ⟨ε₀', hdens⟩ := objs.density κ
  have hη : (0 : ℝ) < η := η.2.1
  set ε₀ : ℝ := min (min ε₀'.1 ε₁) ((η : ℝ) / C) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (lt_min ε₀'.2.1 hε₁) (div_pos hη hC)
  have hε₀1 : ε₀ < 1 := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt hε₁1)
  refine ⟨⟨ε₀, hε₀pos, hε₀1⟩, fun ε hε hεle j hG => ?_⟩
  have hεle' : ε ≤ ε₀ := hεle
  have h1 : ε ≤ ε₀'.1 := hεle'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε ≤ ε₁ := hεle'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε ≤ (η : ℝ) / C := hεle'.trans (min_le_right _ _)
  obtain ⟨F, hF, hcard⟩ := hdens ε hε h1 j hG
  have hmain := Hcore P h hh ξ Q hQ objs.radii
    (fun z r hr => EndSaving.InterfaceV2.sampleEvent h (objs.family z r hr).E)
    (fun z r hr => (objs.family z r hr).sample_local hh)
    (fun z r hr => (objs.family z r hr).E_probability)
    (EndSaving.Interfaces.dyadicRadius j) ⟨ε, hε⟩ h2 F hF hcard
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have : C * ε ≤ η := by
    have := mul_le_mul_of_nonneg_left h3 hC.le
    rwa [mul_div_cancel₀ _ hC.ne'] at this
  show 1 - (η : ℝ) ≤ 1 - C * ε
  linarith


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtraV2
