import SupercriticalLQGUniqueness.B2.DG20Lim.Section51Positive
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleSymmetryCoupling
import SupercriticalLQGUniqueness.B2.DG20Lim.RDataCoupling

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_rdata_of_section51_coupling
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {Ω : Type} {Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ)
          (m (ε (φ n))) (X (ε (φ n)) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
          (X (ε (φ n))) (hX (ε (φ n)))) ω)))
    (hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (hChain : ∀ᵐ ω ∂P',
      ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
        (∀ i j : Fin (k + 1), i ≠ j →
          Disjoint (O i).toSet (O j).toSet) →
        (∀ j : ℕ, (hj : 0 < j) → (hk : j < k) →
          Disconnects (O ⟨j, by omega⟩).toSet
            (O ⟨j - 1, by omega⟩).toSet
            (O ⟨j + 1, by omega⟩).toSet) →
        (∑ j : Fin k,
          (Y n ω).2.1 (O ⟨j.val, by omega⟩,
            O ⟨j.val + 1, by omega⟩)) ≤
          (Y n ω).2.1 (O ⟨0, by omega⟩, O ⟨k, by omega⟩))
    (hAround : ∀ᵐ ω ∂P',
      ∀ n (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
        A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
        (Y n ω).2.1 (O₁, O₂) ≤ (Y n ω).2.1 (O₁, O₁') +
          (Y n ω).2.1 (O₂, O₂') + (Y n ω).2.2 A) :
    ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Pcircle => (Ylim ω).2.1 (O, Pcircle)) ∧
      R.around = (Ylim ω).2.2 := by
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
      (X (ε (φ n))) (hX (ε (φ n)))
  have hSymm := ae_all_circle_coord_symm_of_joint_laws
    P P' h hh.1.measurable D hD Y hYm hLaw
  have hPos := ae_all_positive_circle_coords_of_section51
    hPerc ξ m hm ε hε φ hφ P P' h hh X hX
    Y Ylim hYm hLaw hConv
  have hRatConv (ω : Ω') :
      Tendsto (fun n => (Y n ω).2) atTop (𝓝 (Ylim ω).2) :=
    (continuous_snd.tendsto (Ylim ω)).comp (hConv ω)
  exact ae_has_rdata_of_coord_bounds P'
    (fun n ω => (Y n ω).2) (fun ω => (Ylim ω).2)
    hRatConv hSymm hChain hAround hPos

end SupercriticalLQGUniqueness.B2.DG20Lim
