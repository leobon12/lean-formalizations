import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledInternalUpperTail
import SupercriticalLQGUniqueness.B2.Strong.Annulus

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_across_upper_tail_of_section4_buffered
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (A : EuclideanAnnulus)
    (V : TopologicalSpace.Opens ℂ) (hVc : IsConnected (V : Set ℂ))
    (hVcompact : IsCompact (closure (V : Set ℂ)))
    (x y : V) (hx : (x : ℂ) ∈ A.innerBoundary)
    (hy : (y : ℂ) ∈ A.outerBoundary) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | ENNReal.ofReal (2 * M) <
          acrossDist (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))) A} ≤ ENNReal.ofReal η := by
  have hxy : (x : ℂ) ≠ (y : ℂ) := by
    intro he
    exact Set.disjoint_left.mp (B2.Strong.disjoint_boundaries A) hx (he ▸ hy)
  have hT := scaled_internal_upper_tail_of_section4
    hS ξ Q hQ m hm ε hε D hD P h hh X hX V hVc
    subset_closure hVcompact (subset_univ _) x y hxy
  intro η hη
  obtain ⟨M, hM, hTail⟩ := hT η hη
  refine ⟨M, hM, ?_⟩
  intro r c hc
  let L (ω : Ω) : LSCMetric := B2.LscTop.smulMetric
    ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate r (D (h ω)))
  calc
    P {ω | ENNReal.ofReal (2 * M) < acrossDist (L ω) A}
      ≤ P {ω | ENNReal.ofReal (2 * M) <
          (L ω).internal Set.univ
            (⟨(x : ℂ), Set.mem_univ _⟩,
              ⟨(y : ℂ), Set.mem_univ _⟩)} := by
        apply measure_mono
        intro ω hω
        have hle : acrossDist (L ω) A ≤
            (L ω).internal Set.univ
              (⟨(x : ℂ), Set.mem_univ _⟩,
                ⟨(y : ℂ), Set.mem_univ _⟩) := by
          calc
            acrossDist (L ω) A ≤ L ω ((x : ℂ), (y : ℂ)) :=
              iInf₂_le_of_le _ hx (iInf₂_le _ hy)
            _ ≤ (L ω).internal Set.univ
                (⟨(x : ℂ), Set.mem_univ _⟩,
                  ⟨(y : ℂ), Set.mem_univ _⟩) :=
              B2.PfeLocal.edist_le_internal (L ω) Set.univ
                (⟨(x : ℂ), Set.mem_univ _⟩,
                  ⟨(y : ℂ), Set.mem_univ _⟩)
        exact hω.trans_le hle
    _ ≤ ENNReal.ofReal η := hTail r c hc

end SupercriticalLQGUniqueness.B2.PfeAxioms
