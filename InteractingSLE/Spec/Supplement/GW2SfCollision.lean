/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfHit
import InteractingSLE.Spec.Supplement.GW2SfTransport
import InteractingSLE.Spec.Supplement.RelSafeGB6Drv

/-!
# Geometric collision exclusion for the mapped local curve

Packet PROVE-GW2-SAFE. A version driver agrees with the capacity driver on
each live local prefix. A nonadmissible geometric collision there would put
the mapped trace in its bad-boundary set, contrary to physical avoidance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
  Supp8 Supp8.GB6 Supp8.GB6.CoordB Q3Rel GW2Rd MartChar.RealFlow

/-- A continuous driver agreeing with a live capacity driver has no bad
geometric collision when its current trace avoids the bad-boundary set. -/
theorem not_threshold_of_capTrace_notMem_hitSet {κ : ℝ} (c : BoundaryWord)
    {Γ : ℝ → ℂ} (hΓ : IsDrivenCurve Γ) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < capLife Γ)
    {D : ℝ → ℝ} (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ v : ℝ≥0, v < u → D v = segDriver Γ v)
    (havoid : capTrace Γ u ∉ hitSet κ c.fn c.jumps 0) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0)
      (D u) (fun i => -rightImg (fun s => -D s) (-flowLineXL c.fn c.jumps 0 i) u)
      (fun j => rightImg D (flowLineXR c.fn c.jumps 0 j) u) := by
  intro hth
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ u from zero_le) with h0u | hu0
  · subst h0u
    have hL (i) : -rightImg (fun s => -D s) (-flowLineXL c.fn c.jumps 0 i) 0 =
        flowLineXL c.fn c.jumps 0 i := by
      rw [rightImg_zero (w := fun s => -D s) hD.neg (by simp [hD0])
        (neg_nonneg.2 ((Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.1 i)), neg_neg]
    have hR (i) : rightImg D (flowLineXR c.fn c.jumps 0 i) 0 = flowLineXR c.fn c.jumps 0 i :=
      rightImg_zero hD hD0 ((Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.2.2 i)
    have hbad := mem_hitSet_of_threshold_zero (by
      simpa only [NNReal.coe_zero, hD0, hL, hR] using hth)
    rw [capTrace, NNReal.coe_zero, hΓ.capInv_of_nonpos le_rfl, hΓ.zero] at havoid
    exact havoid hbad
  · exact havoid (mem_hitSet_of_threshold_images (hΓ.isGeneratingTrace hu) hu0 le_rfl hD hD0 hDw hth)

/-- Every live point of the separated local curve avoids the relative bad
set if the physical curve avoids its original bad set before the horizon. -/
theorem notMem_hitSet_capTrace_localCurve_of_returnData {κ k θ : ℝ} (hκ : 0 < κ) (hk : 0 < k)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (c : BoundaryWord) (r : RecData)
    (hdata : ∀ x : ℝ, x ∉ J → x ≠ 0 → -x⁻¹ ∉ c.jumps →
      b x = Sec7.StripSysField.returnData (Real.pi * chiC k) (chiC k) c.fn x)
    (hs : 0 < rtime r) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv (rdrv r) (rtime r)) (𝓝[H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hd : Disjoint (closure (fwdHull (rdrv r) (rtime r)))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))
    (havoid : ∀ t : ℝ≥0, t < T → γ t ∉ hitSet κ b J θ)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < capLife (localCurve (rdrv r) (rtime r) γ T)) :
    capTrace (localCurve (rdrv r) (rtime r) γ T) u ∉
      hitSet κ (upW (θ * chiC κ) (gb6WordOfRec k 0 c r)).fn
        (upW (θ * chiC κ) (gb6WordOfRec k 0 c r)).jumps 0 := by
  have hΓ := isDrivenCurve_localCurve (continuous_rdrv r) (rdrv_zero r) hs htip hw hw0 hγ hT hd
  have hu' : ENNReal.ofReal (u : ℝ) < capLife (localCurve (rdrv r) (rtime r) γ T) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  have hv := (hΓ.capInv_spec u.coe_nonneg hu').1
  have ht0 := clockOf_nonneg (by exact_mod_cast hT) hv
  have htT := clockOf_lt (by exact_mod_cast hT) hv
  have htT' : (clockOf T (capInv (localCurve (rdrv r) (rtime r) γ T) u)).toNNReal < T :=
    (Real.toNNReal_lt_iff_lt_coe ht0).2 htT
  have hsafe := trace_mem_relSafe (continuous_rdrv r) hs.le hw hw0 hγ
    (disjoint_closure_invHull (continuous_rdrv r) hs.le hd) htT'.le
  change relBdry (rdrv r) (rtime r)
    (γ (clockOf T (capInv (localCurve (rdrv r) (rtime r) γ T) u)).toNNReal) ∉ _
  exact notMem_hitSet_relBdry_of_returnData hκ hk hb c r hdata hsafe (havoid _ htT')

/-- The version/local-driver identification supplies the driver agreement
needed by the collision exclusion, only before the announced stop. -/
theorem not_threshold_version_of_local_avoidance {Ω : Type*} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, Supp8.RelSafe.PhysGood s W Wα ζα γ α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω}
    (hω : ω ∈ Supp8.RelSafe.locEv s W Wα ζα GT T)
    (hver : Supp8.RelSafe.VersionAt s W Wα γ α R V ω)
    {κ : ℝ} (c : BoundaryWord) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < capLife (Supp8.RelSafe.gb6Curve s W Wα ζα T ω))
    (huV : (u : ℝ≥0∞) ≤ V ω)
    (havoid : capTrace (Supp8.RelSafe.gb6Curve s W Wα ζα T ω) u ∉ hitSet κ c.fn c.jumps 0) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0)
      (R u ω) (fun i => -rightImg (fun v : ℝ => -R v.toNNReal ω) (-flowLineXL c.fn c.jumps 0 i) u)
      (fun j => rightImg (fun v : ℝ => R v.toNNReal ω) (flowLineXR c.fn c.jumps 0 j) u) := by
  have hΓ := Supp8.RelSafe.isDrivenCurve_of_mem_locEv hGT hω
  have hDw : ∀ v : ℝ≥0, v < u → R v ω = segDriver (Supp8.RelSafe.gb6Curve s W Wα ζα T ω) v := by
    intro v hv
    have hvL := (ENNReal.coe_lt_coe.2 hv).trans hu
    have he := Supp8.RelSafe.eq_localDrv_of_version hGT hω hver hvL
      ((ENNReal.coe_le_coe.2 hv.le).trans huV)
    exact he.trans (drivenDriver_eq hvL)
  have hn := not_threshold_of_capTrace_notMem_hitSet c hΓ hu (D := fun v : ℝ => R v.toNNReal ω)
    (hver.1.comp continuous_real_toNNReal) (by simpa only [Real.toNNReal_zero] using hver.2.1)
    (by simpa only [Real.toNNReal_coe] using hDw) havoid
  simpa only [Real.toNNReal_coe] using hn

end InteractingSLE.Theorem14.GW2Sf
