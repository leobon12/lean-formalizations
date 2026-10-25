import SupercriticalLQGUniqueness.B2.DG20Lim.UniversalCoordLaw

 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_section51_skorokhod_with_coord_law_of_section4
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
            (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) := by
  obtain ⟨φ, hφ, c, hc, ρ, hlim, hmarg⟩ :=
    exists_scale_canonical_coord_limit hS4 ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω mΩ P hP h hh X hX
  exact exists_lfpp_joint_coord_skorokhod_with_coord_law_of_canonical_limit
    (ξ : ℝ) m (fun n => ε (φ n)) ρ
    (by simpa only [canonicalCoordSeq] using hlim) hmarg
    P h hh X hX

end SupercriticalLQGUniqueness.B2.DG20Lim
