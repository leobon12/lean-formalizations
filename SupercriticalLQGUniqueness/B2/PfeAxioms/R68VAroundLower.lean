import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VLowerCluster
import SupercriticalLQGUniqueness.B2.PfeAxioms.AroundLowerFromAcross
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledEuclideanControl

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem r68v_scaled_around_lower_tail_cluster_of_coupling
    (hPerc : DG20PercEstimate')
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (A : EuclideanAnnulus) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c' : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ) /
          (m (e (ψ n)) : ℝ)) atTop (𝓝 (c' : ℝ)) →
        P' {ω | aroundDist (B2.LscTop.smulMetric
          ⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (L ω))) A < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
  let I := {p : Ioi (0 : ℝ) × Ioi (0 : ℝ) × (ℕ → ℕ) //
    StrictMono p.2.2 ∧
    Tendsto (fun n => (p.1 : ℝ) *
      (m ⟨(e (p.2.2 n) : ℝ) / (p.1 : ℝ),
        Set.mem_Ioi.mpr (div_pos (e (p.2.2 n)).property p.1.property)⟩ : ℝ) /
      (m (e (p.2.2 n)) : ℝ)) atTop (𝓝 (p.2.1 : ℝ))}
  let E (i : I) (ω : Ω') : LSCMetric := B2.LscTop.smulMetric
    ⟨(i.1.2.1 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) i.1.1 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.1.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate i.1.1 (L ω))
  have hcont : ∀ i : I, ∀ᵐ ω ∂P',
      Continuous (B2.PfeWeyl.euclidForget (E i ω)) := by
    intro i
    filter_upwards [hB.geometry] with ω hω
    exact continuous_euclidForget_smul_dilate_of_control (L ω) hω.2.1
      ⟨(i.1.2.1 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) i.1.1 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.1.property) (Real.exp_pos _))⟩
      i.1.1
  have hcross : ∀ B : EuclideanAnnulus, ∀ η : ℝ, 0 < η →
      ∃ M : ℝ, 0 < M ∧ ∀ i : I,
        P' {ω | acrossDist (E i ω) B < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
    intro B η hη
    obtain ⟨M, hM, htail⟩ := r68v_scaled_across_lower_tail_cluster_of_coupling
      hPerc hB hSA B η hη
    exact ⟨M, hM, fun i => htail i.1.1 i.1.2.1 i.1.2.2 i.property.1 i.property.2⟩
  have hTail := around_lower_tail_of_across_lower_tail P' E A hcont hcross
  intro η hη
  obtain ⟨M, hM, hBound⟩ := hTail η hη
  exact ⟨M, hM, fun r c' ψ hψ hc => hBound ⟨(r, c', ψ), hψ, hc⟩⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
