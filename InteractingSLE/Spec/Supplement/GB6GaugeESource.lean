/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEClock

/-!
# Causal physical read-back at the source coordinates

The deterministic inverse readout applies to the actual retained record and
to every relative driver satisfying the proved source coordinate predicate.
Clock continuity upgrades cofinal coverage to exact coverage of every live
relative capacity time. All identifications are on the source interior event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.GB6.GaugeE

open Exist.StagedLaw ReadD RelDrv

/-- The decoded record and source relative coordinates reconstruct the
physical trace at every clock value and every live relative capacity time. -/
theorem ae_physicalReadback {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs0 : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      gb6Clock s W Wα ω 0 = 0 ∧
      StrictMonoOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      ContinuousOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        physicalTrace s (gb6Clock s W Wα ω t).toNNReal (gb6Rec s Wα ζα ω, (fun u => D u ω)) = γ ω t) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ gb6Clock s W Wα ω t = u ∧
        physicalTrace s u (gb6Rec s Wα ζα ω, (fun u => D u ω)) = γ ω t := by
  filter_upwards [ae_retainedChart_record hκ hκ4 hF hα s, ae_driver_zero_continuousOn hF,
    hα, hW, hC.relative] with ω hchart hreg hflow hcounter hcoords hs hsH
  obtain ⟨hΨ, htip⟩ := hchart hs hsH
  obtain ⟨hw, hw0, hγ⟩ := hcounter
  obtain ⟨hrange, hhulls⟩ := hcoords hs hsH
  let U := rdrv (gb6Rec s Wα ζα ω)
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hmap : relMap U s = relMap (Ito.rpath (Wα · ω)) s := record_relMap_eq s hreg.1 hreg.2 hs
  have hclock : relClock U s (Ito.rpath (W · ω)) = relClock (Ito.rpath (Wα · ω)) s (Ito.rpath (W · ω)) :=
    record_relClock_eq s hreg.1 hreg.2 hs _
  have hKrec : fwdHull U s = fwdHull (Ito.rpath (Wα · ω)) s := record_hull_eq s hreg.1 hreg.2 hs
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < gb6Tc s γ α ω → Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath (W · ω)) T)) := by
    intro T hT
    rw [hKrec]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hflow hreg.2 hreg.1 hγ hw.continuousOn hw0
      hs ENNReal.coe_lt_top hT
  have hTc : 0 < gb6Tc s γ α ω := by
    obtain ⟨t, ht, _⟩ := hrange 0 (hC.life_pos ω)
    exact lt_of_le_of_lt bot_le ht
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  obtain ⟨ha0, ham, hac⟩ := relative_clock_regular hU hU0 hsR htip hw hw0 hγ hTc hd
  have hclockN : (fun t : ℝ≥0 => relClock U s (Ito.rpath (W · ω)) t) = gb6Clock s W Wα ω := by
    funext t
    rw [hclock]
    rfl
  have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      physicalTrace s (relClock U s (Ito.rpath (W · ω)) t).toNNReal
        (gb6Rec s Wα ζα ω, (fun u => D u ω)) = γ ω t := by
    intro t ht
    obtain ⟨S, htS, hS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    obtain ⟨T, hST, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS
    have hST' : S < T := ENNReal.coe_lt_coe.1 hST
    have htS' : t < S := ENNReal.coe_lt_coe.1 htS
    have hS0 : 0 < S := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) htS'
    have hT0 : 0 < T := hS0.trans hST'
    have hlife : ENNReal.ofReal (relClock U s (Ito.rpath (W · ω)) S) < L ω := by
      rw [hclock]
      exact (hhulls S hS).2.1
    have hD : ∀ q ∈ Icc (0 : ℝ) S,
        fwdHull (Ito.rpath (D · ω)) (relClock U s (Ito.rpath (W · ω)) q) =
          relMap U s '' fwdHull (Ito.rpath (W · ω)) q := by
      intro q hq
      rw [hclock, hmap]
      have hqS : q.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hq.2
      have hqTc : (q.toNNReal : ℝ≥0∞) < gb6Tc s γ α ω :=
        (ENNReal.coe_le_coe.2 hqS).trans_lt hS
      have he := (hhulls q.toNNReal hqTc).2.2
      rw [← Real.coe_toNNReal q hq.1]
      exact he
    exact physicalTrace_of_relHulls s hs0 hΨ htip hw hw0 hγ hT0 hS0 hST' (hd T hT)
      (hC.continuous ω) (hC.zero ω) hlife hD htS'.le
  rw [← hclockN]
  refine ⟨ha0, ham, hac, hread, ?_⟩
  intro u hu
  obtain ⟨T, hT, huT⟩ := hrange u hu
  have huT' : (u : ℝ) ≤ relClock U s (Ito.rpath (W · ω)) T := by
    rw [hclock]
    exact huT.le
  obtain ⟨t, ht, hat⟩ := exists_clock_eq (hac.mono fun q hq =>
    (ENNReal.coe_le_coe.2 hq.2).trans_lt hT) ha0 huT'
  have htTc : (t : ℝ≥0∞) < gb6Tc s γ α ω := (ENNReal.coe_le_coe.2 ht.2).trans_lt hT
  refine ⟨t, htTc, hat, ?_⟩
  have hr := hread t htTc
  rw [hat, Real.toNNReal_coe] at hr
  exact hr

end InteractingSLE.Supp8.GB6.GaugeE
