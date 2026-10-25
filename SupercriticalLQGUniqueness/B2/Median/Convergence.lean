import SupercriticalLQGUniqueness.B2.Median.CrossingConvergence
import SupercriticalLQGUniqueness.B2.Median.UpperCurveAE
import SupercriticalLQGUniqueness.B2.Median.SurgeryProof
import SupercriticalLQGUniqueness.B2.Median.Removable
import SupercriticalLQGUniqueness.B2.Median.GoodLoopsAE

 









set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 

theorem ae_tendsto_crossing_of_subseqLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (X (ε n) ω)) atTop (𝓝 (crossingInf (D (h ω)))) := by
  have hbdd : LQGMetric.IsGFFPlusBddCont h P := LQGMetric.DFGPS.T12.isGFFPlusBddCont_of_wp hh.1
  obtain ⟨u₀, hu₀, hR⟩ := exists_ae_sideRemovable ξ D c hweak P h hh
  filter_upwards [ae_crossing_le_liminf_of_subseqLimit P ξ m ε D hsub h hbdd X hX,
    ae_limsup_le_len_of_strip_curve P ξ m ε hε D hsub c hweak h hbdd X hX,
    hR, ae_goodLoops ξ D c hweak P h hh] with ω hA hB hRω hGLω
  have hlim : limsup (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
      lfppCrossingLength (ξ : ℝ) (X (ε n) ω)) atTop ≤ crossingInf (D (h ω)) := by
    by_cases hZ : crossingInf (D (h ω)) = ∞
    · rw [hZ]; exact le_top
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    obtain ⟨G, a, b, hG, hGa, hGb, hGtr, hGlen⟩ :=
      exists_strip_curve_of_surgery (D (h ω)) u₀ hu₀ hRω hGLω hZ η hη
    refine (hB G a b hG hGa hGb hGtr).trans ?_
    simpa only [ENNReal.ofReal_coe_nnreal] using hGlen
  exact tendsto_of_le_liminf_of_limsup_le hA hlim

end SupercriticalLQGUniqueness.B2.Median
