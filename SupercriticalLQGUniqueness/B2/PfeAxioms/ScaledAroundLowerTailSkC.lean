import SupercriticalLQGUniqueness.B2.PfeAxioms.AroundLowerFromAcross
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAcrossLowerTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledEuclideanControl
import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryTransferC

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_around_lower_tail_of_perc_skC
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hPerc : DG20PercEstimate')
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
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (A : EuclideanAnnulus) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | aroundDist (B2.LscTop.smulMetric
          ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (D (h ω)))) A < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
  let I := {p : Ioi (0 : ℝ) × Ioi (0 : ℝ) //
    Tendsto (fun n => (p.1 : ℝ) *
      (m ⟨(ε n : ℝ) / (p.1 : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property p.1.property)⟩ : ℝ) /
      (m (ε n) : ℝ)) atTop (𝓝 (p.2 : ℝ))}
  let E (i : I) (ω : Ω) : LSCMetric := B2.LscTop.smulMetric
    ⟨(i.1.2 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) i.1.1 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate i.1.1 (D (h ω)))
  have hGeom := B2.DG20Lim.limitEuclideanControl0_of_dg20LimitSkC hSkC
    ξ Q hQ m ε D hm hε hD P h hh
  have hcont : ∀ i : I, ∀ᵐ ω ∂P,
      Continuous (B2.PfeWeyl.euclidForget (E i ω)) := by
    intro i
    filter_upwards [hGeom] with ω hω
    exact continuous_euclidForget_smul_dilate_of_control (D (h ω)) hω
      ⟨(i.1.2 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) i.1.1 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.property) (Real.exp_pos _))⟩
      i.1.1
  have hcross : ∀ B : EuclideanAnnulus, ∀ η : ℝ, 0 < η →
      ∃ M : ℝ, 0 < M ∧ ∀ i : I,
        P {ω | acrossDist (E i ω) B < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
    intro B η hη
    obtain ⟨M, hM, htail⟩ := scaled_across_lower_tail_of_perc
      hPerc ξ m hm ε hε D hD P h hh X hX hsmall B η hη
    exact ⟨M, hM, fun i => htail i.1.1 i.1.2 i.property⟩
  have hTail := around_lower_tail_of_across_lower_tail P E A hcont hcross
  intro η hη
  obtain ⟨M, hM, hBound⟩ := hTail η hη
  exact ⟨M, hM, fun r c hc => hBound ⟨(r,c),hc⟩⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
