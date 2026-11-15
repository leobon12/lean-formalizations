/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmThr
import InteractingSLE.Spec.Supplement.GW2RdSafeGood

/-!
# GW2's collision exclusion at one relative time, with the good-sample facts proved

Packet PROVE-GW2-NOTHR (round 3, SAFE's per-sample facts `hpt` of D38's export). PROVE-GW2-SAFE's
`GW2Stm.ae_no_threshold_gw2_random` asks, almost surely on `{γ(S) ∈ ℍ}`, for three facts at the random retained time
`S`: the good sample (`RelSafe.PhysGood`), a relative version `(R, V)` (`RelSafe.VersionAt`) and its cofinality.

* **`physGood_of_sample`**, **`ae_physGood_all`**: the good-sample facts hold at **every** retained time `S` with
  `γ(S) ∈ ℍ`, on one almost-sure event: the flow driver's extension (`GW2Stm.ae_extTr_spec_all`), the counterflow's
  regularity, and per-sample record facts (`gb6_rec_spec`, the record tip).
* **`not_threshold_gw2_at`** (deterministic, one sample) and **`ae_no_threshold_gw2_at`**: SAFE's conclusion at one
  relative time `u`, for any continuous driver `Rr` from `0` that generates the relative hulls at the relative times
  `≤ u` and with `u` before the relative clock of a time before the physical end. No global version `(R, V)` is needed;
  in particular `Rr` need not be continuous at the relative contact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMapInv)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Nu

open Restart Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2Rd GW2TipSystem GW2Sf
  GW2JointKernel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ θ : ℝ} {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
  {Wα W : ℝ≥0 → Ω → ℝ} {ζα ζ : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}

omit [MeasurableSpace Ω] in
/-- **The record of a complete counterflow, one sample**: at every own time `S` with an interior tip, the record is
good and its retained inverse map has the tip `γ(S)`. -/
theorem recGood_tip_of_sample {ω : Ω} (hW0 : W 0 ω = 0) (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hζ : ζ ω = ⊤) (hγ : IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (S : ℝ≥0) :
    GB6RecGood S W ζ γ ω ∧ Tendsto (fwdMapInv (rdrv (gb6Rec S W ζ ω)) S) (𝓝[H] 0) (𝓝 (γ ω S)) := by
  have hs : (S : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  refine ⟨⟨gb6_rec_spec S hW0 hWc hγ hs, recOf_cfE_eq S hW0 hWc hs, rtime_recOf_cfE S hs⟩, ?_⟩
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hWc hW0 hs
  have hWc' : Continuous fun r : ℝ => W r.toNNReal ω := by
    have h1 : ContinuousOn (fun t => W t ω) univ := by
      have e : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = univ := by
        ext t; simp only [hζ, mem_ofPred_eq, ENNReal.coe_lt_top, mem_univ]
      rw [← e]; exact hWc
    exact (continuousOn_univ.1 h1).comp continuous_real_toNNReal
  refine htip.congr' (eventually_nhdsWithin_of_forall fun z hz' => ?_)
  refine LP.fwdMapInv_eq_of_eqOn_Icc hWc' (continuous_rdrv _) (by simp [hW0]) (rdrv_zero _) S.coe_nonneg
    (fun x hx => ?_) hz'
  exact (rdrv_recOf_cfE S hW0 hWc hs hx.2).symm

omit [MeasurableSpace Ω] in
/-- **The good-sample facts at a retained time, one sample**: from the extension of the flow driver at `S`, the
counterflow's regularity (complete, with its trace) and an interior tip `γ(S) ∈ ℍ`. -/
theorem physGood_of_sample {ω : Ω} {S : ℝ≥0}
    (hext : Continuous (fun t => regW S Wα ζα t ω) ∧ regW S Wα ζα 0 ω = 0 ∧
      IsGeneratingTrace (fun t => regW S Wα ζα t ω) ⊤ (extTr S Wα ζα α ω))
    (hW0 : W 0 ω = 0) (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hζ : ζ ω = ⊤)
    (hγ : IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (hSH : γ ω S ∈ H) :
    RelSafe.PhysGood S (regW S Wα ζα) W ζ (extTr S Wα ζα α) γ ω := by
  obtain ⟨hg, htip⟩ := recGood_tip_of_sample hW0 hWc hζ hγ S
  exact ⟨hext, ⟨hW0, hWc, hγ⟩, by rw [hζ]; exact ENNReal.coe_lt_top, hSH, hg, htip⟩

/-- **The good-sample facts at every retained time, on one almost-sure event** (the flow line of `h` at angle `θ`
alive at the start, the complete counterflow of `h'`). -/
theorem ae_physGood_all [IsProbabilityMeasure P] (hκ : 0 < κ) (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, 0 < ζα ω → ∀ S : ℝ≥0, γ ω S ∈ H →
      RelSafe.PhysGood S (regW S Wα ζα) W ζ (extTr S Wα ζα α) γ ω := by
  filter_upwards [GW2Stm.ae_extTr_spec_all hκ hfl hα, ae_driver_zero_continuousOn hcf, hγ]
    with ω hext hd hγω hpos S hSH
  obtain ⟨h1, h2, -, h4, -⟩ := hext hpos S
  exact physGood_of_sample ⟨h1, h2, h4⟩ hd.1 hd.2 hγω.1 (by rw [hγω.1]; exact hγω.2) hSH

omit [MeasurableSpace Ω] in
/-- **SAFE's collision exclusion at one relative time, one sample** (deterministic). At a good sample of the retained
time `S`, for a continuous driver `Rr` from `0` generating the relative hulls at every relative time `≤ u` before the
relative contact, and `u` below the relative clock of a time before the physical end: the joint word of the record at
`S` has no continuation threshold along `Rr` at `u`. -/
theorem not_threshold_gw2_at {ω : Ω} {S : ℝ≥0}
    (hg : RelSafe.PhysGood S (regW S Wα ζα) W ζ (extTr S Wα ζα α) γ ω) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) (c' : BoundaryWord)
    (hdata : ∀ x : ℝ, x ∉ J → x ≠ 0 → -x⁻¹ ∉ c'.jumps →
      b x = Sec7.StripSysField.returnData (Real.pi * chiC (16 / κ)) (chiC (16 / κ)) c'.fn x)
    (hext : 0 < ζα ω → ∀ s : ℝ≥0, Continuous (fun t => regW s Wα ζα t ω) ∧ regW s Wα ζα 0 ω = 0 ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω) ∧
      IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ (extTr s Wα ζα α ω) ∧
      ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ζα ω → extTr s Wα ζα α ω v = α ω v)
    (havoid : ∀ v : ℝ≥0, (v : ℝ≥0∞) < ζα ω → α ω v ∉ hitSet κ b J θ)
    {Rr : ℝ≥0 → ℝ} (hRc : Continuous Rr) (hR0 : Rr 0 = 0) {u : ℝ≥0}
    (hcof : ∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End S ζα γ α ω ∧ (u : ℝ) < gw2Clock S W Wα ω t)
    (hhull : ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc S (extTr S Wα ζα α) γ ω →
      ENNReal.ofReal (gb6Clock S (regW S Wα ζα) W ω t) ≤ u →
      fwdHull (fun r : ℝ => Rr r.toNNReal) (gb6Clock S (regW S Wα ζα) W ω t) =
        relMap (fun r : ℝ => W r.toNNReal ω) S '' fwdHull (fun r : ℝ => regW S Wα ζα r.toNNReal ω) t) :
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
      (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
      (Rr u)
      (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -Rr v.toNNReal)
        (-flowLineXL (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 i) u)
      (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => Rr v.toNNReal)
        (flowLineXR (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 j) u) := by
  set GT : Set Ω := {ω' | RelSafe.PhysGood S (regW S Wα ζα) W ζ (extTr S Wα ζα α) γ ω'} with hGTdef
  have hGT : ∀ ω' ∈ GT, RelSafe.PhysGood S (regW S Wα ζα) W ζ (extTr S Wα ζα α) γ ω' := fun _ h => h
  have hωG : ω ∈ GT := hg
  obtain ⟨t, ht, hut⟩ := hcof
  obtain ⟨-, -, heq, -, htraceeq⟩ :=
    hext ((zero_le : (0 : ℝ≥0∞) ≤ t).trans_lt (ht.trans_le (min_le_left _ _))) S
  obtain ⟨T, hTζ, hmem, huL⟩ := exists_live_local_horizon hGT hωG heq htraceeq ht hut
  have hvAt : RelSafe.VersionAt S (regW S Wα ζα) W (extTr S Wα ζα α) γ (fun t _ => Rr t)
      (fun _ => (u : ℝ≥0∞)) ω := ⟨hRc, hR0, hhull⟩
  exact not_threshold_gw2_version_of_localGood (R := fun t _ => Rr t) (V := fun _ => (u : ℝ≥0∞)) hGT hmem hvAt
    hκ hb c' hdata hTζ htraceeq havoid huL le_rfl

/-- **SAFE's collision exclusion at every retained time and relative time, on one almost-sure event**, with the
good-sample facts proved: almost surely, at every own time `S` of the counterflow with an interior tip, every
continuous driver `Rr` from `0` generating the relative hulls up to the relative time `u`, with `u` below the relative
clock of a time before the physical end, sees no continuation threshold of the joint word at `u`. -/
theorem ae_no_threshold_gw2_at [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y) :
    ∀ᵐ ω ∂P, ∀ S : ℝ≥0, γ ω S ∈ H → ∀ Rr : ℝ≥0 → ℝ, Continuous Rr → Rr 0 = 0 → ∀ u : ℝ≥0,
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End S ζα γ α ω ∧ (u : ℝ) < gw2Clock S W Wα ω t) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc S (extTr S Wα ζα α) γ ω →
        ENNReal.ofReal (gb6Clock S (regW S Wα ζα) W ω t) ≤ u →
        fwdHull (fun r : ℝ => Rr r.toNNReal) (gb6Clock S (regW S Wα ζα) W ω t) =
          relMap (fun r : ℝ => W r.toNNReal ω) S '' fwdHull (fun r : ℝ => regW S Wα ζα r.toNNReal ω) t) →
      ¬ ForceWord.ThresholdCondition
        (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
        (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
        (Rr u)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -Rr v.toNNReal)
          (-flowLineXL (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 i) u)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => Rr v.toNNReal)
          (flowLineXR (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 j) u) := by
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (by positivity : 0 < 16 / κ) hb' hcf
  have hdata := fun x hxJ hx0 hxJ' => data_eq_returnData_gw2 hκ hb hG hb' hG' hT c' hc'J hc'b
    (x := x) hxJ hx0 hxJ'
  filter_upwards [ae_physGood_all hκ hfl hα hcf hγ, GW2Stm.ae_extTr_spec_all hκ hfl hα,
    ae_trace_notMem_hitSet hκ hκ4 hb hG hfl hα] with ω hpg hext havoid S hSH Rr hRc hR0 u hcof hhull
  have hpos : 0 < ζα ω := by
    obtain ⟨t, ht, -⟩ := hcof
    exact (zero_le : (0 : ℝ≥0∞) ≤ t).trans_lt (ht.trans_le (min_le_left _ _))
  exact not_threshold_gw2_at (hpg hpos S hSH) hκ hb c' hdata hext havoid hRc hR0 hcof hhull

end InteractingSLE.Theorem14.GW2Nu
