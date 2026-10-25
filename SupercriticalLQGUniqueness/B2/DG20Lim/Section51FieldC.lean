import SupercriticalLQGUniqueness.B2.DG20Lim.Section51LSCExist
import SupercriticalLQGUniqueness.B2.DG20Lim.FieldCoordFromStationaryLaw

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem exists_section51_skorokhod_with_lsc_and_fieldC_of_inputs
    (hS4 : DG20Section4)
    (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistC),
          (hh : IsNormalizedWholePlaneGFF h P) →
          ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
            (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) →
          ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
            (_ : StandardBorelSpace Ω') (P' : Measure Ω')
            (_ : IsProbabilityMeasure P')
            (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
            (Ylim : Ω' → (CoordJ → ℝ) × RatCoords),
            (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
            (∀ n, P'.map (Y n) = P.map (fun ω =>
              (pairJ ⊤ (h ω), measurableRatCoordsVersion
                (fun ω => normalizedContLFPP (ξ : ℝ)
                  (m (ε (φ n))) (X (ε (φ n)) ω))
                (aemeasurable_normalizedContLFPP_heat_version P h hh
                  (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
                  (X (ε (φ n))) (hX (ε (φ n)))) ω))) ∧
            IsNormalizedWholePlaneGFF
              (fun ω => pairJInv ⊤ (Ylim ω).1) P' ∧
            (∀ n, P'.map (fun ω =>
              (pairJInv ⊤ (Y n ω).1,
                finiteMetricE (circleCoordsInv (Y n ω).2.1))) =
              P.map (fun ω => (h ω,
                rescaledLFPP (ξ : ℝ) (m (ε (φ n)))
                  (X (ε (φ n)) ω)))) ∧
            (∀ n ω, Continuous
              (finiteMetricE (circleCoordsInv (Y n ω).2.1))) ∧
            (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) ∧
            (∀ᵐ ω ∂P', ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
              (∀ i j : Fin (k + 1), i ≠ j →
                Disjoint (O i).toSet (O j).toSet) →
              (∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
                Disconnects (O ⟨j, by omega⟩).toSet
                  (O ⟨j - 1, by omega⟩).toSet
                  (O ⟨j + 1, by omega⟩).toSet) →
              (∑ j : Fin k,
                (Y n ω).2.1 (O ⟨j.val, by omega⟩,
                  O ⟨j.val + 1, by omega⟩)) ≤
                (Y n ω).2.1 (O ⟨0, by omega⟩,
                  O ⟨k, by omega⟩)) ∧
            (∀ᵐ ω ∂P', ∀ n (A : RatAnnulus)
              (O₁ O₁' O₂ O₂' : RatCircle),
              A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
              (Y n ω).2.1 (O₁, O₂) ≤
                (Y n ω).2.1 (O₁, O₁') +
                (Y n ω).2.1 (O₂, O₂') + (Y n ω).2.2 A) ∧
            (∀ᵐ ω ∂P', ∃ R : RData,
              R.across = (fun O Pcircle => (Ylim ω).2.1 (O, Pcircle)) ∧
              R.around = (Ylim ω).2.2 ∧
              LSCTendsto
                (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
                R.toLSCFun.1) ∧
            (∀ᵐ ω ∂P', Tendsto
              (fun n => pairJ ⊤ (pairJInv ⊤ (Y n ω).1)) atTop
              (𝓝 (pairJ ⊤ (pairJInv ⊤ (Ylim ω).1)))) := by
  obtain ⟨φ, hφ, c, hc, hCouple⟩ :=
    exists_section51_skorokhod_with_lsc_of_inputs
      hS4 hPerc ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω mΩ P hP h hh X hX
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont,
    hConv, hChain, hAround, hLSC⟩ :=
    hCouple P h hh X hX
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
      (X (ε (φ n))) (hX (ε (φ n)))
  let V : ℕ → Ω → RatCoords := fun n =>
    measurableRatCoordsVersion (D n) (hD n)
  have hVm : ∀ n, Measurable (V n) := fun n =>
    measurable_measurableRatCoordsVersion (D n) (hD n)
  have hLawV : ∀ n, P'.map (Y n) =
      P.map (fun ω => (pairJ ⊤ (h ω), V n ω)) := by
    intro n
    simpa only [V, D] using hCoordLaw n
  have hField := ae_decoded_field_coords_tendsto_of_stationary_laws
    P P' h hh.1.measurable Y Ylim V hYm hYlimm hVm hLawV hConv
  exact ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont,
    hConv, hChain, hAround, hLSC, hField⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
