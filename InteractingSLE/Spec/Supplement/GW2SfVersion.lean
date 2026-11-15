/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfCollision

/-!
# GW2's version has no bad collision on a separated live physical prefix

Packet PROVE-GW2-SAFE. This joins the deterministic collision exclusion to
the existing version/local-driver identification. The physical bad-set
avoidance input is precisely `GW2Rd.ae_trace_notMem_hitSet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
  Supp8 Supp8.GB6 Supp8.GB6.CoordB Q3Rel GW2Rd GW2TipSystem

/-- The collision exclusion is invariant under the index identifications
in `IsFlowType`. -/
theorem not_threshold_images_of_isFlowType {κ : ℝ} {c : BoundaryWord} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (htype : FCDet.IsFlowType κ 0 c xL xR ρL ρR) {D : ℝ → ℝ} {u : ℝ≥0}
    (hn : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0)
      (D u) (fun i => -MartChar.RealFlow.rightImg (fun v => -D v) (-flowLineXL c.fn c.jumps 0 i) u)
      (fun j => MartChar.RealFlow.rightImg D (flowLineXR c.fn c.jumps 0 j) u)) :
    ¬ ForceWord.ThresholdCondition ρL ρR (D u)
      (fun i => -MartChar.RealFlow.rightImg (fun v => -D v) (-xL i) u)
      (fun j => MartChar.RealFlow.rightImg D (xR j) u) := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  subst nL nR
  change xL = flowLineXL c.fn c.jumps 0 at hxL
  change xR = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 0 at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 0 at hρR
  rwa [hxL, hxR, hρL, hρR]

/-- On a good separated prefix before the physical flow lifetime, GW2's
version has no geometric threshold before its announced stop. -/
theorem not_threshold_gw2_version_of_localGood {Ω : Type*} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, RelSafe.PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω}
    (hω : ω ∈ RelSafe.locEv s (regW s Wα ζα) W ζ GT T)
    (hver : RelSafe.VersionAt s (regW s Wα ζα) W (extTr s Wα ζα α) γ R V ω)
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (c' : BoundaryWord)
    (hdata : ∀ x : ℝ, x ∉ J → x ≠ 0 → -x⁻¹ ∉ c'.jumps →
      b x = Sec7.StripSysField.returnData (Real.pi * chiC (16 / κ)) (chiC (16 / κ)) c'.fn x)
    (hTζ : (T : ℝ≥0∞) < ζα ω)
    (hext : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ζα ω → extTr s Wα ζα α ω v = α ω v)
    (havoid : ∀ v : ℝ≥0, (v : ℝ≥0∞) < ζα ω → α ω v ∉ hitSet κ b J θ)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < capLife (RelSafe.gb6Curve s (regW s Wα ζα) W ζ T ω))
    (huV : (u : ℝ≥0∞) ≤ V ω) :
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 0)
      (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 0)
      (R u ω)
      (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -R v.toNNReal ω)
        (-flowLineXL (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 i) u)
      (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => R v.toNNReal ω)
        (flowLineXR (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 j) u) := by
  have hg := hGT ω hω.1.2
  have hs0 := RelSafe.pos_of_physGood hg
  have hrtime : rtime (gb6Rec s W ζ ω) = s := hg.2.2.2.2.1.2.2
  have hcurve : RelSafe.gb6Curve s (regW s Wα ζα) W ζ T ω =
      localCurve (rdrv (gb6Rec s W ζ ω)) (rtime (gb6Rec s W ζ ω)) (extTr s Wα ζα α ω) T := by
    rw [RelSafe.gb6Curve, RelSafe.phTr_eq hg, hrtime]
  have hTc := RelSafe.lt_gb6Tc_of_mem_locEv hGT hω
  have hd : Disjoint (closure (fwdHull (rdrv (gb6Rec s W ζ ω)) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath (regW s Wα ζα · ω)) T)) := by
    rw [GaugeE.record_hull_eq s hg.2.1.1 hg.2.1.2.1 hg.2.2.1]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hg.2.1.2.2 hg.2.1.2.1 hg.2.1.1
      hg.1.2.2 hg.1.1.continuousOn hg.1.2.1 hg.2.2.1 ENNReal.coe_lt_top hTc
  have hbad : capTrace (RelSafe.gb6Curve s (regW s Wα ζα) W ζ T ω) u ∉
      hitSet κ (gw2Word κ θ c' (gb6Rec s W ζ ω)).fn (gw2Word κ θ c' (gb6Rec s W ζ ω)).jumps 0 := by
    rw [hcurve, gw2Word, GW2Fb.jointWordOfRec_specOffset hκ]
    apply notMem_hitSet_capTrace_localCurve_of_returnData hκ (by positivity) hb c' _ hdata
      (by rw [hrtime]; exact hs0) (by rw [hrtime]; exact hg.2.2.2.2.2)
      hg.1.1 hg.1.2.1 hg.1.2.2 hω.1.1 (by rwa [hrtime]) ?_ (hcurve ▸ hu)
    intro v hv
    have hvζ := (ENNReal.coe_lt_coe.2 hv).trans hTζ
    rw [hext v hvζ.le]
    exact havoid v hvζ
  exact not_threshold_version_of_local_avoidance hGT hω hver _ hu huV hbad

end InteractingSLE.Theorem14.GW2Sf
