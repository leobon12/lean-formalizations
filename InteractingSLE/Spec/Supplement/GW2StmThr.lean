/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfPhysical

/-!
# GW2's stage step, part 3: the threshold step at a random retained time

Packet PROVE-GW2-STAGEMEAN (ruling R106). PROVE-GW2-SAFE's physical collision exclusion
(`GW2Sf.ae_no_threshold_gw2_of_goodSet`) reads the counterflow at a deterministic own time `s` and takes the version
`(R, V)` of the relative driver at that time. Its mathematical core is per sample
(`GW2Sf.exists_live_local_horizon`, `GW2Sf.not_threshold_gw2_version_of_localGood`), and its two almost-sure physical
inputs do not depend on `s`: the flow trace avoids the hitting set (`GW2Rd.ae_trace_notMem_hitSet`), and the flow
driver and trace extend continuously past the lifetime **for every `s` at once** (`ae_extTr_spec_all` below; the
landed `GW2Rd.ae_extTr_spec` states it for one `s`). So at stage `k + 1`, where the retained counterflow is read up to
a random own time `S ω` (the stopping time `σ_k`), the threshold step needs exactly the version facts at `S ω`:

* **`ae_extTr_spec_all`**: the extension clauses of `GW2Rd.ae_extTr_spec`, simultaneously for every retained time;
* **`ae_no_threshold_gw2_random`**: for any retained time `S : Ω → ℝ≥0` and any relative driver `R` with stop `V`, if
  almost surely on `{γ(S) ∈ ℍ}` the sample is physically good at `S`, `R` is the relative driver there before `V`
  (`RelSafe.VersionAt`), and every relative time `u < V` is reached by the relative clock before the physical end
  (cofinality), then almost surely on `{γ(S) ∈ ℍ}` the relative word of the record at `S` has no continuation
  threshold at any `u < V`.

The three per-sample premises are the version facts of the relative driver at the random time (PROVE-GW2-RELDET's
`IsGW2RelVersion` and good set, read at `S ω`); at a deterministic `S = s` they are exactly what SAFE's proof extracts
from `IsGW2RelVersion s` and the good set. Conditional helper with a distinct name; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Stm

open Restart Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
  Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2Rd GW2TipSystem GW2Sf

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ θ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
  {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}

/-- **The extended flow driver and trace, almost surely on `{ζα > 0}`, for every retained time at once**
(`GW2Rd.ae_extTr_spec` reads one deterministic `s`; its null set does not depend on `s`). -/
theorem ae_extTr_spec_all [IsProbabilityMeasure P] (hκ : 0 < κ) (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) :
    ∀ᵐ ω ∂P, 0 < ζα ω → ∀ s : ℝ≥0, Continuous (fun t => regW s Wα ζα t ω) ∧ regW s Wα ζα 0 ω = 0 ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω) ∧
      IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ (extTr s Wα ζα α ω) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ζα ω → extTr s Wα ζα α ω u = α ω u := by
  filter_upwards [ae_driver_zero_continuousOn hfl, hα, ae_tendsto_driver_at_lifetime hκ hfl] with ω hd hαω hlim
    hpos s
  obtain ⟨h1, h2, h3, hex⟩ := regW_extension s hd.1 hd.2 hαω hpos fun T hT => hlim T hT (by
    rw [← ENNReal.coe_lt_coe, hT]; simpa using hpos)
  exact ⟨h1, h2, h3, Classical.epsilon_spec hex⟩

/-- **Physical collision exclusion with the counterflow read at a random time** (the threshold step of GW2's stage
identity). The per-sample premises are the good-sample, version and cofinality facts at the retained time `S ω`. -/
theorem ae_no_threshold_gw2_random [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    {h' : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {J' : Finset ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {γ : Ω → ℝ≥0 → ℂ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    (S : Ω → ℝ≥0) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hpt : ∀ᵐ ω ∂P, γ ω (S ω) ∈ H →
      RelSafe.PhysGood (S ω) (regW (S ω) Wα ζα) W ζ (extTr (S ω) Wα ζα α) γ ω ∧
      RelSafe.VersionAt (S ω) (regW (S ω) Wα ζα) W (extTr (S ω) Wα ζα α) γ R V ω ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
        ∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End (S ω) ζα γ α ω ∧ (u : ℝ) < gw2Clock (S ω) W Wα ω t) :
    ∀ᵐ ω ∂P, γ ω (S ω) ∈ H → ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
      ¬ ForceWord.ThresholdCondition
        (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).fn (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).jumps 0 0)
        (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).fn (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).jumps 0 0)
        (R u ω)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -R v.toNNReal ω)
          (-flowLineXL (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).fn (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).jumps 0 i) u)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => R v.toNNReal ω)
          (flowLineXR (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).fn
            (gw2Word κ θ c' (gb6Rec (S ω) W ζ ω)).jumps 0 j) u) := by
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (by positivity : 0 < 16 / κ) hb' hcf
  have hdata := fun x hxJ hx0 hxJ' => data_eq_returnData_gw2 hκ hb hG hb' hG' hT c' hc'J hc'b
    (x := x) hxJ hx0 hxJ'
  filter_upwards [hpt, ae_extTr_spec_all hκ hfl hα, ae_trace_notMem_hitSet hκ hκ4 hb hG hfl hα]
    with ω hω hext havoid hsH u huV
  obtain ⟨hg, hvAt, hc⟩ := hω hsH
  -- the good set of the single retained time `S ω`
  set GT : Set Ω := {ω' | RelSafe.PhysGood (S ω) (regW (S ω) Wα ζα) W ζ (extTr (S ω) Wα ζα α) γ ω'} with hGTdef
  have hGT : ∀ ω' ∈ GT, RelSafe.PhysGood (S ω) (regW (S ω) Wα ζα) W ζ (extTr (S ω) Wα ζα α) γ ω' :=
    fun _ h => h
  have hωG : ω ∈ GT := hg
  obtain ⟨t, ht, hut⟩ := hc u huV
  obtain ⟨-, -, heq, -, htraceeq⟩ :=
    hext ((zero_le : (0 : ℝ≥0∞) ≤ t).trans_lt (ht.trans_le (min_le_left _ _))) (S ω)
  obtain ⟨T, hTζ, hmem, huL⟩ := exists_live_local_horizon hGT hωG heq htraceeq ht hut
  exact not_threshold_gw2_version_of_localGood hGT hmem hvAt hκ hb c' hdata hTζ htraceeq havoid huL huV.le

end InteractingSLE.Theorem14.GW2Stm
