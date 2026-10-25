import SupercriticalLQGUniqueness.B2.Median.Convergence
import SupercriticalLQGUniqueness.B2.Median.Assembly
import SupercriticalLQGUniqueness.B2.Median.NoGapControl
import NV1Evidence

 









set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 

theorem isMedian_crossing_one_of_subseqLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    IsMedian P (fun ω => crossingInf (D (h ω))) 1 :=
  isMedian_crossing_one_of_ae_tendsto P ξ m hm ε D hweak.1 h hh X hX
    (ae_tendsto_crossing_of_subseqLimit P ξ m ε hε D hsub c hweak h hh X hX)

 

theorem iface_medianPassage_of_limitEuclideanControl0
    (hInput : PfeAxioms.Inputs.LimitEuclideanControl0) : B2.Iface.MedianPassage := by
  intro ξ m hm ε ε' hε hε' D D' hD hD' c c' hc hc' C hC hprop
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := SupercriticalLQGUniqueness.exists_normalizedGFF
  letI : MeasurableSpace Ω := mΩ
  haveI : IsProbabilityMeasure P := hP
  have hXex : ∀ δ : Set.Ioi (0 : ℝ), ∃ X : Ω → C(ℂ, ℝ), IsHeatSmoothing P h δ X := by
    intro δ
    obtain ⟨X, -, hX⟩ := SupercriticalLQGUniqueness.exists_heatVersion hh (δ : ℝ) δ.2
    exact ⟨X, hX⟩
  choose X hX using hXex
  have hmedD := isMedian_crossing_one_of_subseqLimit P ξ m hm ε hε D hD c hc h hh X hX
  have hmedD' := isMedian_crossing_one_of_subseqLimit P ξ m hm ε' hε' D' hD' c' hc' h hh X hX
  have hcont : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_normalized
      (Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)
  have hng := noGap_crossingInf_finite_of_limitEuclideanControl0 hInput ξ m hm ε hε D hD c hc
    P h hh
  exact eq_one_of_proportional_crossing_medians P (fun ω => D (h ω)) (fun ω => D' (h ω))
    C hC (hprop P h hcont) hmedD hmedD' hng

end SupercriticalLQGUniqueness.B2.Median
