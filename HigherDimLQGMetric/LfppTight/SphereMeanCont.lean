import HigherDimLQGMetric.LfppTight.MedianBridge
import HigherDimLQGMetric.ConvField.JointMain

/-! Joint continuity gives cutoff continuity of the convolved sphere mean. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_sphereMean_continuousOn_of_joint {d : ℕ}
    (κ : Rd d → ℝ) (h : DistRd d)
    (hc : ContinuousOn (fun p : ℝ × Rd d => convMollify κ p.1 h p.2)
      (Ioi (0 : ℝ) ×ˢ univ)) :
    ContinuousOn (fun ε => l6a_convSphereMean κ ε h) (Ioi (0 : ℝ)) := by
  letI : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  have hs : ∀ᵐ u ∂(unitSphereProb d), u ∈ Metric.closedBall (0 : Rd d) 1 := by
    filter_upwards [ae_unitSphereProb_norm_le d] with u hu
    simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  have hre : (unitSphereProb d).restrict (Metric.closedBall (0 : Rd d) 1) =
      unitSphereProb d := Measure.restrict_eq_self_of_ae_mem hs
  have hfunc : Continuous (fun p : Ioi (0 : ℝ) × Rd d =>
      convMollify κ p.1.1 h p.2) := by
    have hm : Continuous (fun p : Ioi (0 : ℝ) × Rd d =>
        ((p.1.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hcc := hc.comp_continuous hm (fun p => ⟨p.1.2, trivial⟩)
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hcc
  have hcont := continuous_parametric_integral_of_continuous
    (μ := unitSphereProb d)
    (f := fun ε : Ioi (0 : ℝ) => fun u : Rd d => convMollify κ ε.1 h u)
    hfunc (isCompact_closedBall (0 : Rd d) 1)
  rw [hre] at hcont
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun ε : Ioi (0 : ℝ) =>
    ∫ u, convMollify κ ε.1 h u ∂(unitSphereProb d))
  exact hcont

theorem l6a_ae_sphereMean_continuousOn {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ContinuousOn (fun ε => l6a_convSphereMean κ ε (h ω))
      (Ioi (0 : ℝ)) := by
  filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh]
    with ω hc
  exact l6a_sphereMean_continuousOn_of_joint κ (h ω) hc

end HigherDimLQGMetric
