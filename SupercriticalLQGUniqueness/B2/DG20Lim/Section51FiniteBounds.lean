import SupercriticalLQGUniqueness.B2.DG20Lim.Section51Chain
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAroundCoupling

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_section51_skorokhod_with_finite_bounds_of_section4
    (hS4 : DG20Section4)
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
                  (Y n ω).2.1 (O₂, O₂') + (Y n ω).2.2 A) := by
  obtain ⟨φ, hφ, c, hc, hCouple⟩ :=
    exists_section51_skorokhod_with_chain_of_section4
      hS4 ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω mΩ P hP h hh X hX
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont, hConv, hChain⟩ :=
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
  have hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength := by
    intro n
    exact Filter.Eventually.of_forall fun ω =>
      isLength_normalizedContLFPP (ξ : ℝ) (m (ε (φ n)))
        (X (ε (φ n)) ω)
  have hAround := ae_all_finiteAround_bounds_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm hCoordLaw
  exact ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont, hConv, hChain, hAround⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
