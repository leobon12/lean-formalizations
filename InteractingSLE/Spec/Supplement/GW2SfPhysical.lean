/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfVersion

/-!
# Almost-sure physical collision exclusion for GW2

Packet PROVE-GW2-SAFE. The simultaneous version caps give a physical horizon
before both the flow lifetime and contact. On that horizon the extended
curve is the original flow, which avoids its own closed bad-boundary set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
  Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2Rd GW2TipSystem

/-- A relative clock value strictly before the physical end belongs to a
separated local prefix whose horizon is still before the flow lifetime. -/
theorem exists_live_local_horizon {Ω : Type*} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, RelSafe.PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω)
    {ω : Ω} (hωG : ω ∈ GT)
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω)
    (htraceeq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζα ω → extTr s Wα ζα α ω t = α ω t)
    {t u : ℝ≥0} (ht : (t : ℝ≥0∞) < gw2End s ζα γ α ω) (hut : (u : ℝ) < gw2Clock s W Wα ω t) :
    ∃ T : ℝ≥0, (T : ℝ≥0∞) < ζα ω ∧ ω ∈ RelSafe.locEv s (regW s Wα ζα) W ζ GT T ∧
      (u : ℝ≥0∞) < capLife (RelSafe.gb6Curve s (regW s Wα ζα) W ζ T ω) := by
  obtain ⟨T, htT, hTend⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htT' : t < T := ENNReal.coe_lt_coe.1 htT
  have hTpos : 0 < T := (zero_le : (0 : ℝ≥0) ≤ t).trans_lt htT'
  have hTζ : (T : ℝ≥0∞) < ζα ω := hTend.trans_le (min_le_left _ _)
  have hTc : (T : ℝ≥0∞) < firstContactTime (fun r => (α ω r : OnePoint ℂ))
      ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) := hTend.trans_le (min_le_right _ _)
  have hTrel : (T : ℝ≥0∞) < gb6Tc s (extTr s Wα ζα α) γ ω :=
    (hull_clock_contact_of_ext (w := fun t => W t ω) heq htraceeq hTζ hTc).2.2
  have hmem : ω ∈ RelSafe.locEv s (regW s Wα ζα) W ζ GT T :=
    (RelSafe.mem_locEv_iff hGT hωG).2 ⟨hTpos, hTrel⟩
  refine ⟨T, hTζ, hmem, ?_⟩
  have hclk : gb6Clock s (regW s Wα ζα) W ω t = gw2Clock s W Wα ω t :=
    (hull_clock_contact_of_ext (w := fun v => W v ω) heq htraceeq
      (ht.trans_le (min_le_left _ _)) (ht.trans_le (min_le_right _ _))).2.1
  rw [RelSafe.capLife_gb6Curve_eq hGT hmem]
  refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun (v : ℝ≥0) (_ : v < T) =>
    ENNReal.ofReal (gb6Clock s (regW s Wα ζα) W ω v)) t htT')
  rw [← ENNReal.ofReal_coe_nnreal]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.coe_nonneg).2
  rw [hclk]
  exact hut

/-- Physical collision exclusion on any supplied full good event. The good
event is the one already constructed for GW2's (S)/(L) clauses. -/
theorem ae_no_threshold_gw2_of_goodSet
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGW2RelVersion s P W Wα ζ ζα γ α R V)
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, RelSafe.PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω)
    (hGTae : ∀ᵐ ω ∂P, γ ω s ∈ H → ω ∈ GT) :
    ∀ᵐ ω ∂P, γ ω s ∈ H → ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
      ¬ ForceWord.ThresholdCondition
        (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 0)
        (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 0)
        (R u ω)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -R v.toNNReal ω)
          (-flowLineXL (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 i) u)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => R v.toNNReal ω)
          (flowLineXR (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 j) u) := by
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (by positivity : 0 < 16 / κ) hb' hcf
  have hdata := fun x hxJ hx0 hxJ' => data_eq_returnData_gw2 hκ hb hG hb' hG' hT c' hc'J hc'b
    (x := x) hxJ hx0 hxJ'
  have hcofinal := ae_cofinal_gw2End_of_version hκ hfl hα hζ s hver
  obtain ⟨⟨⟨⟨-, hRc, hR0, -, -, -, hlive⟩, -⟩, -⟩, -⟩ := hver
  filter_upwards [hGTae, hcofinal, ae_extTr_spec hκ hfl hα s,
    ae_trace_notMem_hitSet hκ hκ4 hb hG hfl hα, hlive]
    with ω hGω hc hext havoid hv hsH u huV
  have hωG := hGω hsH
  have hg := hGT ω hωG
  obtain ⟨t, ht, hut⟩ := hc hsH u huV
  obtain ⟨-, -, heq, -, htraceeq⟩ := hext ((zero_le : (0 : ℝ≥0∞) ≤ t).trans_lt (ht.trans_le (min_le_left _ _)))
  obtain ⟨T, hTζ, hmem, huL⟩ := exists_live_local_horizon hGT hωG heq htraceeq ht hut
  have hvAt : RelSafe.VersionAt s (regW s Wα ζα) W (extTr s Wα ζα α) γ R V ω :=
    ⟨hRc ω, hR0 ω, (hv hg.2.2.1 hsH).2.2⟩
  exact not_threshold_gw2_version_of_localGood hGT hmem hvAt hκ hb c' hdata hTζ htraceeq havoid huL huV.le

end InteractingSLE.Theorem14.GW2Sf
