import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.Window
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete




 














set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra

open LQGMetric (DistC)
open LQGMetric.Blueprint (fieldSigmaClosed0)

 
theorem ofReal_one_sub_le_of_compl {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} {x : ℝ} (hx : 0 ≤ x)
    (hA : P Aᶜ ≤ ENNReal.ofReal x) : ENNReal.ofReal (1 - x) ≤ P A := by
  have h1 : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono (union_compl_self A).symm.subset).trans (measure_union_le _ _)
  rw [ENNReal.ofReal_sub 1 hx, ENNReal.ofReal_one]
  exact tsub_le_iff_right.2 (h1.trans (add_le_add le_rfl hA))

 


theorem auxiliaryGood_prob_core :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∃ C ε₁ : ℝ, 0 < C ∧ 0 < ε₁ ∧ ε₁ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
        ∀ (R : EndSaving.Interfaces.AdmissibleRadii)
          (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set Ω),
        (∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii), ∃ E₀ : Set Ω,
          MeasurableSet[fieldSigmaClosed0 h
            {x : ℂ | (r : ℝ) ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}] E₀ ∧
          event z r hr =ᵐ[P] E₀) →
        (∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
          ENNReal.ofReal p ≤ P (event z r hr)) →
        ∀ (b ε : Set.Ioi (0 : ℝ)), (ε : ℝ) ≤ ε₁ →
        ∀ F : Finset ℝ, (F : Set ℝ) = R.radii ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) →
        (5 / 8 : ℝ) * (Real.log (ε : ℝ)⁻¹ / Real.log 8) ≤ F.card →
        ENNReal.ofReal (1 - C * ε) ≤ P (EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q R event b ε) := by
  obtain ⟨p, hp0, hp1, Cb, hCb, Hcover⟩ := r51b_cover
  obtain ⟨Ca, ε₁, hCa, hε₁, hε₁1, Hwin⟩ := r51a_window
  refine ⟨p, hp0, hp1, Ca + Cb, ε₁, by positivity, hε₁, hε₁1, ?_⟩
  intro Ω _ P _ h hh ξ Q hQ R event hloc hprob b ε hε F hF hcard
  have hε1 : (ε : ℝ) < 1 := hε.trans_lt hε₁1
  have hεpos : (0 : ℝ) < ε := ε.2
  set Ga : Set Ω := {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → (ε : ℝ) ^ 2 * b ≤ r → (r : ℝ) ≤ ε * b →
      ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)), ∃ hrz : ℝ,
        IsCircleAverage (h ω) r z hrz ∧ |hrz - hbr| ≤ 3 * Real.log (((r : ℝ) / (b : ℝ))⁻¹)}
    with hGa
  set Gb : Set Ω := {ω | ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
    ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
      (ε : ℝ) ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
      LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈ Metric.ball z ((r : ℝ) / 25) ∧
      ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr} with hGb
  have hsub : Ga ∩ Gb ⊆ EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q R event b ε := by
    rintro ω ⟨⟨hbr, hbrc, hwin⟩, hcov⟩
    refine ⟨hbr, hbrc, fun r hrR hlo hhi z hz => ?_, hcov⟩
    obtain ⟨hrz, hrzc, hinc⟩ := hwin r hrR hlo hhi z hz
    exact ⟨hrz, hrzc, EndSaving.CircleRange.sizeWindow_of_circle_increment ξ Q hQ ε b r hε1 hlo hhi hbr hrz hinc⟩
  have hA : P Gaᶜ ≤ ENNReal.ofReal (Ca * ε) := by
    have := Hwin P h hh R b ε hε
    simpa only [hGa, Set.compl_ofPred] using this
  have hB : P Gbᶜ ≤ ENNReal.ofReal (Cb * ε) := by
    have := Hcover P h hh.1 R event hloc hprob b ε hε1 F hF hcard
    simpa only [hGb, Set.compl_ofPred] using this
  have hcompl : P (EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q R event b ε)ᶜ ≤ ENNReal.ofReal ((Ca + Cb) * ε) := by
    have hs : (EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q R event b ε)ᶜ ⊆ Gaᶜ ∪ Gbᶜ := by
      rw [← Set.compl_inter]
      exact Set.compl_subset_compl.2 hsub
    calc P (EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q R event b ε)ᶜ ≤ P (Gaᶜ ∪ Gbᶜ) := measure_mono hs
      _ ≤ P Gaᶜ + P Gbᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Ca * ε) + ENNReal.ofReal (Cb * ε) := add_le_add hA hB
      _ = ENNReal.ofReal ((Ca + Cb) * ε) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hCa.le hεpos.le) (mul_nonneg hCb.le hεpos.le),
            add_mul]
  exact ofReal_one_sub_le_of_compl (mul_nonneg (add_pos hCa hCb).le hεpos.le) hcompl

 





theorem lemMainExtra :
    ∃ pbar : Set.Ioo (0 : ℝ) 1,
      ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus < cPlus →
      ∀ objs : EndSaving.Interfaces.ObjectsExist P h D D' ξ Q cMinus cPlus pbar,
      ∀ (κ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
        ∃ ε₀ : Set.Ioo (0 : ℝ) 1, ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ j : ℕ,
          ENNReal.ofReal (κ : ℝ) ≤
            P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (EndSaving.Interfaces.dyadicRadius j) κ
              ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
          ENNReal.ofReal (1 - (η : ℝ)) ≤
            P (EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q objs.radii (fun z r hr => (objs.family z r hr).E)
              (EndSaving.Interfaces.dyadicRadius j) ⟨ε, hε⟩) := by
  obtain ⟨p, hp0, hp1, C, ε₁, hC, hε₁, hε₁1, Hcore⟩ := auxiliaryGood_prob_core
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
  have hmain := Hcore P h hh ξ Q hQ objs.radii (fun z r hr => (objs.family z r hr).E)
    (fun z r hr => (objs.family z r hr).E_local) (fun z r hr => (objs.family z r hr).E_probability)
    (EndSaving.Interfaces.dyadicRadius j) ⟨ε, hε⟩ h2 F hF hcard
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have : C * ε ≤ η := by
    have := mul_le_mul_of_nonneg_left h3 hC.le
    rwa [mul_div_cancel₀ _ hC.ne'] at this
  show 1 - (η : ℝ) ≤ 1 - C * ε
  linarith

 
theorem lemMainExtra_T58Data :
    ∃ pbar : Set.Ioo (0 : ℝ) 1,
      ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus < cPlus →
      ∀ data : EndSaving.RepairedInterfaces.T58Data P h D D' ξ Q cMinus cPlus pbar,
      ∀ (κ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
        ∃ ε₀ : Set.Ioo (0 : ℝ) 1, ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
          ENNReal.ofReal (κ : ℝ) ≤
            P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κ
              ⟨data.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg data.cMid'_lower⟩} →
          ENNReal.ofReal (1 - (η : ℝ)) ≤
            P (EndSaving.RepairedInterfaces.AuxiliaryGood h ξ Q data.radii (fun z r hr => (data.family z r hr).E)
              b ⟨ε, hε⟩) := by
  obtain ⟨p, hp0, hp1, C, ε₁, hC, hε₁, hε₁1, Hcore⟩ := auxiliaryGood_prob_core
  refine ⟨⟨p, hp0, hp1⟩, ?_⟩
  intro ξ Q D D' hD _ Ω _ P _ h hh cMinus cPlus _ _ _ data κ η
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  obtain ⟨ε₀', hdens⟩ := data.density κ
  have hη : (0 : ℝ) < η := η.2.1
  set ε₀ : ℝ := min (min ε₀'.1 ε₁) ((η : ℝ) / C) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (lt_min ε₀'.2.1 hε₁) (div_pos hη hC)
  have hε₀1 : ε₀ < 1 := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt hε₁1)
  refine ⟨⟨ε₀, hε₀pos, hε₀1⟩, fun ε hε hεle b hG => ?_⟩
  have hεle' : ε ≤ ε₀ := hεle
  have h1 : ε ≤ ε₀'.1 := hεle'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε ≤ ε₁ := hεle'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε ≤ (η : ℝ) / C := hεle'.trans (min_le_right _ _)
  obtain ⟨F, hF, hcard⟩ := hdens ε hε h1 b hG
  have hmain := Hcore P h hh ξ Q hQ data.radii (fun z r hr => (data.family z r hr).E)
    (fun z r hr => (data.family z r hr).E_local) (fun z r hr => (data.family z r hr).E_probability)
    b ⟨ε, hε⟩ h2 F hF hcard
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have : C * ε ≤ η := by
    have := mul_le_mul_of_nonneg_left h3 hC.le
    rwa [mul_div_cancel₀ _ hC.ne'] at this
  show 1 - (η : ℝ) ≤ 1 - C * ε
  linarith

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra
