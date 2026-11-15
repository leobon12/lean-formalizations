/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6ReadDGauge
import InteractingSLE.Spec.Supplement.Q3ChainMeas

/-!
# The retained chart decoded from GB6's actual record

Endpoint driver comparison transports inverse landing from the existing
frozen retained chart to the record driver. All other chart fields are
already supplied by the deterministic relative-chart API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Supp8.GB6.GaugeE

open Exist.StagedLaw Q3Rel

/-- Endpoint agreement of continuous zero-start drivers gives agreement of
relative inverse maps throughout the half-plane. -/
theorem relInv_eqOn_of_prefix {U V : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    (hV : Continuous V) (hV0 : V 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (heq : EqOn V U (Icc 0 s)) : EqOn (relInv V s) (relInv U s) H := by
  intro z hz
  unfold relInv
  rw [LP.fwdMapInv_eq_of_eqOn_Icc hV hU hV0 hU0 hs heq (neg_inv_mem_H hz)]

/-- The retained chart landing property depends only on the driver through
the retained endpoint. No global trace of the replacement driver is needed. -/
theorem retainedChart_of_prefix {U V : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    (hV : Continuous V) (hV0 : V 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (heq : EqOn V U (Icc 0 s))
    (hΨ : IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)) :
    IsRetainedChartOff (invHull V s) (relMap V s) (relInv V s) (relLog V s) (relBad V s) := by
  have hD := isDomainChart_rel hV hV0 hs
  refine ⟨hD.isOpen, hD.isConformalBijection, fun v hv => hD.inv_mem hv,
    fun v hv => hD.fwd_inv hv, hD.isConformal.1, isDerivLog_relLog hV hs, ?_,
    fun y hy => tendsto_relMap hV hV0 hs hy, fun y hy0 hy => tendsto_im_relLog hV hV0 hs hy0 hy⟩
  intro y hy
  have hbad := Q3Chain.relBad_eq_of_eqOn hU hs heq
  obtain ⟨p, hp⟩ := hΨ.inv_lands y (hbad ▸ hy)
  refine ⟨p, hp.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)⟩
  exact (relInv_eqOn_of_prefix hU hU0 hV hV0 hs heq hz).symm

/-- Almost surely on the source interior-tip event, the actual retained
record has the retained-chart landing property and the correct inverse tip. -/
theorem ae_retainedChart_record {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsRetainedChartOff (invHull (rdrv (gb6Rec s Wα ζα ω)) s)
        (relMap (rdrv (gb6Rec s Wα ζα ω)) s) (relInv (rdrv (gb6Rec s Wα ζα ω)) s)
        (relLog (rdrv (gb6Rec s Wα ζα ω)) s) (relBad (rdrv (gb6Rec s Wα ζα ω)) s) ∧
      Tendsto (fwdMapInv (rdrv (gb6Rec s Wα ζα ω)) s) (𝓝[H] 0) (𝓝 (α ω s)) := by
  filter_upwards [Q3Kernel.ae_exists_frozen_retainedChartOff hκ hκ4 hF hα s,
    ae_driver_zero_continuousOn hF, hα] with ω hchart hreg htrace hs hsH
  obtain ⟨U, αr, t₂, hst₂, _, hU, hU0, _, hUeq, _, hΨ⟩ := hchart hs hsH
  let V := rdrv (gb6Rec s Wα ζα ω)
  have hV : Continuous V := continuous_rdrv _
  have hV0 : V 0 = 0 := rdrv_zero _
  have heq : EqOn V U (Icc 0 (s : ℝ)) := by
    intro x hx
    have hrec : V x = Wα x.toNNReal ω := rdrv_recOf_cfE s hreg.1 hreg.2 hs hx.2
    exact hrec.trans (hUeq x ⟨hx.1, hx.2.trans hst₂.le⟩).symm
  refine ⟨retainedChart_of_prefix hU hU0 hV hV0 s.coe_nonneg heq hΨ, ?_⟩
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip htrace hreg.2 hreg.1 hs
  have hInv : fwdMapInv U s = fwdMapInv (Ito.rpath (Wα · ω)) s :=
    fwdMapInv_eq_of_eqOn s.coe_nonneg hst₂ hUeq
  change Tendsto (fwdMapInv (Ito.rpath (Wα · ω)) s) (𝓝[H] 0) (𝓝 (α ω s)) at htip
  rw [← hInv] at htip
  exact htip.congr' (eventually_nhdsWithin_of_forall fun z hz =>
    (LP.fwdMapInv_eq_of_eqOn_Icc hV hU hV0 hU0 s.coe_nonneg heq hz).symm)

end InteractingSLE.Supp8.GB6.GaugeE
