import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VFinite
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAcrossConvergence
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledRatioLimit

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem r68v_ae_scaled_crossing_tendsto
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (A : EuclideanAnnulus) (r c' : Ioi (0 : ℝ))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hc : Tendsto (fun n => (r : ℝ) *
      (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ) /
      (m (e (ψ n)) : ℝ)) atTop (𝓝 (c' : ℝ)))
    (hCircle : ∀ᵐ ω ∂P', Tendsto (fun n => circleAvg (hN (ψ n) ω) r 0)
      atTop (𝓝 (circleAvg (h' ω) r 0))) :
    ∀ᵐ ω ∂P', Tendsto (fun n =>
      acrossDist (r68vScaledFiniteMetric ξ m (e (ψ n)) r V (hN (ψ n) ω)) A)
      atTop (𝓝 (acrossDist (B2.LscTop.smulMetric
        ⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0),
          Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩
        (B2.LscTop.dilate r (L ω))) A)) := by
  have hCross := ae_coupled_acrossDist_tendsto hB hSA (A.dilate r r.property)
  filter_upwards [hCross, hCircle] with ω hC hAvg
  have hC' := hC.comp hψ.tendsto_atTop
  have hExp : Tendsto
      (fun n => Real.exp (-(ξ : ℝ) * circleAvg (hN (ψ n) ω) r 0))
      atTop (𝓝 (Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0))) :=
    (Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul hAvg)
  have hInv : Tendsto (fun n =>
      ((r : ℝ) * (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ) /
        (m (e (ψ n)) : ℝ))⁻¹) atTop (𝓝 (c' : ℝ)⁻¹) :=
    hc.inv₀ c'.property.ne'
  have hcoef : Tendsto (fun n =>
      ((m (e (ψ n)) : ℝ) /
        ((r : ℝ) * (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ))) *
        Real.exp (-(ξ : ℝ) * circleAvg (hN (ψ n) ω) r 0))
      atTop (𝓝 ((c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0))) := by
    have heq (n : ℕ) :
        ((m (e (ψ n)) : ℝ) /
          ((r : ℝ) * (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ))) =
        ((r : ℝ) * (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ) /
          (m (e (ψ n)) : ℝ))⁻¹ := by
      field_simp [ne_of_gt (Set.mem_Ioi.mp r.property),
        ne_of_gt (Set.mem_Ioi.mp (m (e (ψ n))).property),
        ne_of_gt (Set.mem_Ioi.mp (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩).property)]
    simpa only [heq] using hInv.mul hExp
  have hScaled := tendsto_acrossDist_smul_dilate
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (ψ n)))
      (V (e (ψ n)) (hN (ψ n) ω))) (L ω)
    (fun n => ⟨((m (e (ψ n)) : ℝ) /
        ((r : ℝ) * (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ))) *
          Real.exp (-(ξ : ℝ) * circleAvg (hN (ψ n) ω) r 0),
        Set.mem_Ioi.mpr (mul_pos
          (div_pos (m (e (ψ n))).property
            (mul_pos r.property (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩).property))
          (Real.exp_pos _))⟩)
    ⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩
    r A hcoef hC'
  simpa only [r68vScaledFiniteMetric] using hScaled

end SupercriticalLQGUniqueness.B2.PfeAxioms
