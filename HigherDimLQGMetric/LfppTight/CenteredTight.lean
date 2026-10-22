import HigherDimLQGMetric.LfppTight.MetricIdent
import HigherDimLQGMetric.ConvField.CenteredGaussian
import HigherDimLFPP.Field.Exists

/-! Tightness after centering the convolution field by its unit-sphere mean. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_aemeasurable_centered_metric {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ a : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    AEMeasurable (fun ω => l6a_metricOfFieldC ξ a
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))) P := by
  let H : Rd d → Ω → ℝ := fun z ω => convMollifyNorm κ ε (h ω) z
  have hm (z : Rd d) : AEMeasurable (H z) P := by
    have hmeas := l2b_measurable_pairCenteredKernel d hd κ hκ h
      hh.1.measurable hε z
    have heq : H z =ᵐ[P] fun ω => l2b_pairCenteredKernel hd hκ hε z (h ω) := by
      filter_upwards [l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh]
        with ω heqω
      exact (heqω ε hε z).symm
    exact hmeas.aemeasurable.congr heq.symm
  have hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω := by
    filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh]
      with ω hcont
    have hbase : Continuous fun z : Rd d => convMollify κ ε (h ω) z := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hp : (ε, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) := ⟨hε, trivial⟩
      have hOpen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d))) :=
        isOpen_Ioi.prod isOpen_univ
      exact (hcont.continuousAt (hOpen.mem_nhds hp)).comp
        (continuousAt_const.prodMk continuousAt_id)
    exact hbase.sub continuous_const
  have hmet := l6a_aemeasurable_lfppMetricLaw P ξ a H hm hc
  have heq : (fun ω => l6a_metricOfFieldC ξ a
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))) =ᵐ[P]
      (fun ω => toCMapRd (a • fun p : Rd d × Rd d =>
        HigherDimLFPP.lfppDistOn ξ (H · ω) univ p.1 p.2)) := by
    filter_upwards [hc] with ω hω
    apply ContinuousMap.ext
    intro p
    rw [l6a_metricOfFieldC, show l6a_toFieldCMap (fun z => H z ω) =
      (⟨fun z => H z ω, hω⟩ : C(Rd d, ℝ)) from dite_eq_left hω]
    apply congrArg (fun f : Rd d × Rd d → ℝ => toCMapRd f p)
    funext q
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun t : ℝ => a * t)
      (fieldLfpp_eq_lfppDistOn hω q)
  exact (aemeasurable_congr heq.symm).1 hmet

/-- The centred convolution metric, normalized by the finite-band median,
is tight on the whole interval of real cutoffs. -/
theorem l6a_centered_tight (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : HigherDimLFPP.WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε)) :
    IsTightMeasureSet {μ : Measure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map (fun ω => l6a_metricOfFieldC ξ
          (DGZ.aHat P' G ξ ε)⁻¹
          (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))))} := by
  obtain ⟨Ψ, hΨc, hΨm, hlaw⟩ :=
    l6a_coupled_metric_law hL1e hDGZ.dim hDGZ.kernel P h hh
      P' W hW G hG
  have hT := l6a_coupled_tight hDGZ hAdapter P' W hW G hG Ψ hΨc hΨm
  apply hT.subset
  rintro μ ⟨ε, hε, rfl⟩
  refine ⟨ε, hε, ?_⟩
  let X : Ω → C(Rd d × Rd d, ℝ) := fun ω => l6a_metricOfFieldC ξ
    (DGZ.aHat P' G ξ ε)⁻¹
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))
  let Y : Ω' → C(Rd d × Rd d, ℝ) := fun ω => DGZ.normMetricC ξ
    (l6a_coupledPhi κ W G Ψ ε · ω) (DGZ.aHat P' G ξ ε)
  have hXm : AEMeasurable X P :=
    l6a_aemeasurable_centered_metric hDGZ.dim κ hDGZ.kernel ξ
      (DGZ.aHat P' G ξ ε)⁻¹ hε.1 P h hh
  have hΦc (ω : Ω') : Continuous fun z => l6a_coupledPhi κ W G Ψ ε z ω :=
    ((hG ε hε).continuous ω).sub continuous_const |>.add (hΨc ω)
  have hΦm (z : Rd d) : Measurable fun ω => l6a_coupledPhi κ W G Ψ ε z ω :=
    ((hG ε hε).measurable z).sub (hW.measurable _) |>.add (hΨm z)
  have hYm : Measurable Y := DGZ.measurable_normMetricC hΦc hΦm ξ _
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply_of_aemeasurable hXm hS, Measure.map_apply hYm hS]
  calc
    P (X ⁻¹' S) = P' {ω | l6a_metricOfFieldC ξ
        (DGZ.aHat P' G ξ ε)⁻¹
        (l6a_toFieldCMap (l6a_coupledPhi κ W G Ψ ε · ω)) ∈ S} := by
      exact hlaw ε hε ξ _ S hS
    _ = P' (Y ⁻¹' S) := by
      apply measure_congr
      apply Filter.Eventually.of_forall
      intro ω
      have heq : l6a_toFieldCMap
          (fun z => l6a_coupledPhi κ W G Ψ ε z ω) =
          (⟨fun z => l6a_coupledPhi κ W G Ψ ε z ω, hΦc ω⟩ : C(Rd d, ℝ)) :=
        dite_eq_left (hΦc ω)
      exact congrArg (· ∈ S) (by
        simp only [Y, heq, l6a_metricOfFieldC_eq_normMetricC]
        rfl)

end HigherDimLQGMetric
