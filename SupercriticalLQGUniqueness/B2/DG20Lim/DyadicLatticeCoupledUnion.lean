import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeUnion

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def coupledSiteBad {Ω : Type} (Ylim : Ω → (CoordJ → ℝ) × RatCoords)
    (C : ℝ≥0∞) (K : ℕ) (v : ℤ × ℤ) : Set Ω :=
  {ω | ∀ i ∈ sparseDyadicIndices K,
    C * (Ylim ω).2.1
      ((centeredRatAnnulus (dyadicLatticeCenter K v).1
        (dyadicLatticeCenter K v).2 (ratRad64 1 i)
        (ratRad64_pos (by norm_num) i)).inner,
       (centeredRatAnnulus (dyadicLatticeCenter K v).1
        (dyadicLatticeCenter K v).2 (ratRad64 1 i)
        (ratRad64_pos (by norm_num) i)).outer) <
      (Ylim ω).2.2
        (centeredRatAnnulus (dyadicLatticeCenter K v).1
          (dyadicLatticeCenter K v).2 (ratRad64 1 i)
          (ratRad64_pos (by norm_num) i))}

theorem exists_dyadic_lattice_bad_bound_on_coupled_limit_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))) ω)))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (a : ℝ) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (R K : ℕ), 12 ≤ K →
        P' {ω | ∃ v ∈ dyadicLatticeBox R K,
          ω ∈ coupledSiteBad Ylim
            (ENNReal.ofReal 2 *
              (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) *
              ENNReal.ofReal 2) K v} ≤
          ((dyadicLatticeBox R K).card : ℝ≥0∞) *
            ENNReal.ofReal (c * Real.exp (-a * (sparseDyadicIndices K).card)) := by
  obtain ⟨c, C, hc, hC, hfin⟩ :=
    exists_finite_good_ratio_on_coupled_limit_of_inputs
      hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε hε Y Ylim hYm hLaw hConv a ha
  refine ⟨c, C, hc, hC, ?_⟩
  intro R K hK
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 *
    (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) * ENNReal.ofReal 2
  let E : (ℤ × ℤ) → Set Ω' := fun v => coupledSiteBad Ylim C' K v
  have hsite : ∀ v ∈ dyadicLatticeBox R K,
      P' (E v) ≤ ENNReal.ofReal
        (c * Real.exp (-a * (sparseDyadicIndices K).card)) := by
    intro v hv
    exact hfin (dyadicLatticeCenter K v).1 (dyadicLatticeCenter K v).2
      1 (by norm_num) (sparseDyadicIndices K)
      (sparseDyadicIndices_nonempty hK)
  simpa only [E, C'] using
    measure_exists_site_bad_le P' R K E
      (ENNReal.ofReal (c * Real.exp (-a * (sparseDyadicIndices K).card))) hsite

end SupercriticalLQGUniqueness.B2.DG20Lim
