/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuLaunch
import InteractingSLE.Spec.Supplement.GW2NuBad
import InteractingSLE.Spec.Supplement.GW2NuSafe
import InteractingSLE.Spec.Supplement.GW2BnLaw

/-!
# The converse of SAFE's collision exclusion at the candidate's death (one sample)

Packet PROVE-GW2-NOTHR (round 3, D35 (D-a)). At a good sample of the counterflow's own time `S`, if the candidate
dies at `T` before the relative contact, at a bad point of its launch word, with its zero mark colliding at `T` on
the tip's side (Theorem 1.3, `GW2Nu.launch_zero_collision`), then every continuous driver `Rr` from `0` that generates
the relative hulls up to `T` has a continuation threshold of the joint word at the relative clock of `T`.

The steps:
* earlier real bounces lie strictly inside the tip: weakly by `prior_le_of_zero_collision`, strictly because the
  tip is bad and the trace avoids the bad set before `T`;
* hence the relative trace has no earlier real visit at or beyond the joint tip (`relTrace_off_of_prior`);
* the joint tip carries the forward image of the bad weight (`sumR_le_of_boundary_chart` with SAFE's data identity);
* hence the joint threshold (`rightSum_le_of_real_bad_tip_off`), and the mirror forms on the left.

* **`zero_mem_hitSet_of_isBadPoint`**: a bad start puts `0` in the hitting set (so the tip at a positive death is
  not `0`);
* **`threshold_gw2_at_death`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Nu

open Restart Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.CoordB Supp8.Q3Rel
  GW2Rd GW2TipSystem GW2Sf GW2JointKernel MartChar.RealFlow GW2Bh

section Zero

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **A bad start lies in the hitting set**: if `0` is a bad point of the flow-line word, then small positive
(negative) reals are right (left) bad points, so `0` is in the closure. -/
theorem zero_mem_hitSet_of_isBadPoint
    (h : SB.Vq.IsBadPoint (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      0) : (0 : ℂ) ∈ hitSet κ b J θ := by
  unfold hitSet
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases h.2 with ⟨-, hR⟩ | ⟨-, hL⟩
  · obtain ⟨δ, hδ, hδJ⟩ := exists_gap_above J 0
    set y := min δ ε / 2 with hydef
    have hy : 0 < y := by positivity
    have hyδ : y < δ := by have := min_le_left δ ε; linarith
    have hyε : y < ε := by have := min_le_right δ ε; linarith
    refine ⟨(y : ℂ), ⟨y, Or.inl ⟨hy, ?_⟩, rfl⟩, ?_⟩
    · have heq : univ.filter (fun i => flowLineXR b J 0 i ≤ y) = univ.filter (fun i => flowLineXR b J 0 i ≤ 0) := by
        refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => hi.trans hy.le⟩
        by_contra hgt
        rcases flowLineXR_eq_zero_or_mem b J i with h0 | hJ
        · rw [h0] at hgt; exact hgt le_rfl
        · have := hδJ _ hJ (not_le.1 hgt); linarith
      rw [heq]
      exact hR
    · rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
      exact hyε
  · obtain ⟨δ, hδ, hδJ⟩ := exists_gap_below J 0
    set y := min δ ε / 2 with hydef
    have hy : 0 < y := by positivity
    have hyδ : y < δ := by have := min_le_left δ ε; linarith
    have hyε : y < ε := by have := min_le_right δ ε; linarith
    refine ⟨((-y : ℝ) : ℂ), ⟨-y, Or.inr ⟨by linarith, ?_⟩, rfl⟩, ?_⟩
    · have heq : univ.filter (fun i => -y ≤ flowLineXL b J 0 i) = univ.filter (fun i => 0 ≤ flowLineXL b J 0 i) := by
        refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => le_trans (by linarith) hi⟩
        by_contra hlt
        rcases flowLineXL_eq_zero_or_mem b J i with h0 | hJ
        · rw [h0] at hlt; exact hlt le_rfl
        · have := hδJ _ hJ (not_le.1 hlt); linarith
      rw [heq]
      exact hL
    · rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith

end Zero

variable {Ω : Type*} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {Wα W : ℝ≥0 → Ω → ℝ} {ζα ζ : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}

/-- **SAFE's converse at the candidate's death, one sample.** -/
theorem threshold_gw2_at_death {ω : Ω} {S T : ℝ≥0}
    (hg : RelSafe.PhysGood S (regW S Wα ζα) W ζ (extTr S Wα ζα α) γ ω) (hζ : ζ ω = ⊤) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) (c' : BoundaryWord)
    (hdata : ∀ x : ℝ, x ∉ J → x ≠ 0 → -x⁻¹ ∉ c'.jumps →
      b x = Sec7.StripSysField.returnData (Real.pi * chiC (16 / κ)) (chiC (16 / κ)) c'.fn x)
    (hT0 : 0 < T) (hζT : ζα ω = T)
    (htr : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ζα ω → extTr S Wα ζα α ω v = α ω v)
    (havoid : ∀ v : ℝ≥0, (v : ℝ≥0∞) < ζα ω → α ω v ∉ hitSet κ b J θ)
    (hbad : SB.Vq.IsBadPoint (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) (α ω T))
    (hzR : 0 < (α ω T).re → rightImg (fun r : ℝ => regW S Wα ζα r.toNNReal ω) 0 T = regW S Wα ζα T ω)
    (hzL : (α ω T).re < 0 → rightImg (fun r : ℝ => -regW S Wα ζα r.toNNReal ω) 0 T = -regW S Wα ζα T ω)
    (hTc : (T : ℝ≥0∞) < gb6Tc S (extTr S Wα ζα α) γ ω)
    {Rr : ℝ≥0 → ℝ} (hRc : Continuous Rr) (hR0 : Rr 0 = 0)
    (hhull : ∀ t : ℝ≥0, t ≤ T →
      fwdHull (fun r : ℝ => Rr r.toNNReal) (gb6Clock S (regW S Wα ζα) W ω t) =
        relMap (fun r : ℝ => W r.toNNReal ω) S '' fwdHull (fun r : ℝ => regW S Wα ζα r.toNNReal ω) t) :
    ForceWord.ThresholdCondition
      (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
      (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
      (Rr (gb6Clock S (regW S Wα ζα) W ω T).toNNReal)
      (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -Rr v.toNNReal)
        (-flowLineXL (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 i)
        (gb6Clock S (regW S Wα ζα) W ω T).toNNReal)
      (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => Rr v.toNNReal)
        (flowLineXR (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 j)
        (gb6Clock S (regW S Wα ζα) W ω T).toNNReal) := by
  classical
  have hs : (0 : ℝ) < S := RelSafe.pos_of_physGood hg
  have hγc : Continuous (extTr S Wα ζα α ω) := RelSafe.continuous_γ hg
  obtain ⟨⟨hwc, hw0, hwtr⟩, ⟨hW0, hWc, hWtr⟩, hSζ, hSH, hgood, htip⟩ := hg
  have hrtime : rtime (gb6Rec S W ζ ω) = S := hgood.2.2
  set rec := gb6Rec S W ζ ω with hrecdef
  set U : ℝ → ℝ := rdrv rec with hUdef
  have hU : Continuous U := continuous_rdrv rec
  have hU0 : U 0 = 0 := rdrv_zero rec
  set w : ℝ≥0 → ℝ := fun t => regW S Wα ζα t ω with hwdef
  set γ' : ℝ≥0 → ℂ := extTr S Wα ζα α ω with hγ'def
  have hWcont : Continuous fun t => W t ω := by
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = univ := by
      ext t; simp only [hζ, mem_ofPred_eq, ENNReal.coe_lt_top, mem_univ]
    rw [e] at hWc
    exact continuousOn_univ.1 hWc
  have hWtr' : IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by rw [← hζ]; exact hWtr
  -- the relative chart of the record, the clock and the hulls
  have hd : Disjoint (closure (fwdHull U S)) (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)) := by
    rw [hUdef, hrecdef, GaugeE.record_hull_eq S hW0 hWc hSζ]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hWtr hWc hW0 hwtr hwc.continuousOn hw0 hSζ
      ENNReal.coe_lt_top hTc
  have hsafe : MapsTo γ' (Iic T) (relSafe U S) := mapsTo_relSafe (hU := hU) (hs := hs) (hw := hwc) (hw0 := hw0)
    (hγ := hwtr) (hd := hd)
  have hclk : ∀ t, gb6Clock S (regW S Wα ζα) W ω t = relClock U S (Ito.rpath w) t := fun t => by
    show relClock (fun r : ℝ => W r.toNNReal ω) S (fun r : ℝ => regW S Wα ζα r.toNNReal ω) t = _
    rw [hUdef, hrecdef, GaugeE.record_relClock_eq S hW0 hWc hSζ]
    rfl
  have ha : IsClockOn (fun t : ℝ≥0 => relClock U S (Ito.rpath w) t) (T : ℝ≥0∞) := by
    have h := isClockOn_relClk hWcont hW0 hWtr' hSH hwc hw0 hwtr (τ := T) hTc
    have e : relClk (fun t => W t ω) w S = fun t : ℝ≥0 => relClock U S (Ito.rpath w) t := by
      funext t
      rw [hUdef, hrecdef, GaugeE.record_relClock_eq S hW0 hWc hSζ]
      rfl
    rwa [e] at h
  have hK : ∀ t : ℝ≥0, t ≤ T → fwdHull (Ito.rpath Rr) (relClock U S (Ito.rpath w) t) =
      fillH (relBdry U S '' (γ' '' Icc 0 t)) := by
    refine relBdry_hull_of_relMap hU hU0 hs htip hwc hw0 hwtr hd fun t ht => ?_
    have h := hhull t ht
    rw [hclk t] at h
    rw [hUdef, hrecdef, GaugeE.record_relMap_eq S hW0 hWc hSζ]
    exact h
  have hσ : 0 < relClock U S (Ito.rpath w) T := by
    have h := ha.strictMonoOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ T by simp) (show ((T : ℝ≥0) : ℝ≥0∞) ≤ T from le_rfl) hT0
    rwa [ha.zero] at h
  have hRc' : Continuous (Ito.rpath Rr) := hRc.comp continuous_real_toNNReal
  have hR0' : Ito.rpath Rr 0 = 0 := by simp [Ito.rpath, hR0]
  have hγ'0 : γ' 0 = 0 := hwtr.1
  have hTζ : (T : ℝ≥0∞) ≤ ζα ω := hζT.ge
  have htipT : γ' T = α ω T := htr T hTζ
  have him : (γ' T).im = 0 := by rw [htipT]; exact hbad.1
  -- the tip is not `0`
  have hne0 : (α ω T).re ≠ 0 := by
    intro h0
    have hz : α ω T = 0 := Complex.ext (by simp [h0]) (by simpa using hbad.1)
    have h0bad := zero_mem_hitSet_of_isBadPoint (hz ▸ hbad)
    have hα0 : α ω 0 = 0 := by rw [← htr 0 (by simp)]; exact hγ'0
    exact havoid 0 (by rw [hζT]; exact_mod_cast hT0) (hα0 ▸ h0bad)
  -- the clock read at the conclusion
  have hd0 : (0 : ℝ) ≤ relClock U S (Ito.rpath w) T := hσ.le
  have hcoe : (((gb6Clock S (regW S Wα ζα) W ω T).toNNReal : ℝ≥0) : ℝ) = relClock U S (Ito.rpath w) T := by
    rw [hclk T, Real.coe_toNNReal _ hd0]
  -- the joint word through the record chart
  set K := gw2Word κ θ c' rec with hKdef
  have hKeq : K = upW (θ * chiC κ) (gb6WordOfRec (16 / κ) 0 c' rec) := by
    rw [hKdef, gw2Word, GW2Fb.jointWordOfRec_specOffset hκ]
  have hKpc : IsPiecewiseConstantBoundaryData K.fn K.jumps := K.isPiecewiseConstantBoundaryData
  set E : Set ℝ := ({0} ∪ (J : Set ℝ)) ∪ (fun y : ℝ => -y⁻¹) '' (c'.jumps : Set ℝ) with hEdef
  have hE : E.Finite := ((finite_singleton 0).union J.finite_toSet).union (c'.jumps.finite_toSet.image _)
  have hEJ : (J : Set ℝ) ⊆ E := fun _ hy => Or.inl (Or.inr hy)
  have hEInv {u : ℝ} (hu : u ∉ E) : -u⁻¹ ∉ c'.jumps := fun h => hu (Or.inr ⟨-u⁻¹, h, neg_inv_neg_inv_real u⟩)
  have hheight : ∀ u : ℝ, (u : ℂ) ∉ closure (invHull U S) → u ∉ E → (relBdry U S u).re ∉ K.jumps →
      K.fn (relBdry U S u).re = b u + θ * chiC κ := by
    intro u huA huE huJR
    have hu0 : u ≠ 0 := fun h => huE (Or.inl (Or.inl h))
    rw [hKeq, upW_fn]
    rw [hKeq, upW_jumps] at huJR
    have h := gb6WordOfRec_fn_relBdry (by positivity : (0 : ℝ) < 16 / κ) c' rec hu0
      (by rw [hrtime]; exact huA) (hEInv huE) (by rw [hrtime]; exact huJR)
    rw [hrtime] at h
    show (gb6WordOfRec (16 / κ) 0 c' rec).fn (relBdry U S u).re + θ * chiC κ = _
    rw [h, ← hdata u (fun h => huE (hEJ h)) hu0 (hEInv huE)]
  -- the real tip and a ball of real points off the retained hull around it
  set p := (α ω T).re with hpdef
  have hpe : γ' T = (p : ℂ) := by rw [htipT]; exact Complex.ext (by simp [hpdef]) (by simpa using hbad.1)
  have hpA : (p : ℂ) ∉ closure (invHull U S) := hpe ▸ (hsafe (le_refl T)).2
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hpA
  have hpbad : (p : ℂ) ∈ hitSet κ b J θ → ∀ t : ℝ≥0, t < T → (γ' t).im = 0 → (γ' t).re ≠ p := by
    intro hpH t htT himt hre
    have hte : γ' t = (p : ℂ) := Complex.ext (by simp [hre]) (by simpa using himt)
    have hlt : (t : ℝ≥0∞) < ζα ω := by rw [hζT]; exact_mod_cast htT
    rw [htr t hlt.le] at hte
    exact havoid t hlt (hte ▸ hpH)
  rcases lt_or_gt_of_ne hne0 with hneg | hpos
  · -- a left threshold
    have hwL : SB.Vq.wL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) p ≤ -2 := by
      rcases hbad.2 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (not_le.2 hneg)
      · exact h2
    have hpH : (p : ℂ) ∈ hitSet κ b J θ := ofReal_mem_hitSet (Or.inr ⟨hneg, hwL⟩)
    have hprior : ∀ t < T, (γ' t).im = 0 → (γ' T).re < (γ' t).re := by
      intro t htT himt
      have hz := hzL hneg
      have hle := prior_ge_of_zero_collision hwc hw0 hγc hwtr hT0 hz (by rw [hpe]; simpa using hneg) htT himt
      rw [hpe, Complex.ofReal_re] at hle ⊢
      exact lt_of_le_of_ne hle (Ne.symm (hpbad hpH t htT himt))
    have hoff := relTrace_off_of_prior_neg hU hU0 hs.le ha hsafe him (by rw [hpe]; simpa using hneg) hprior
    set r := min r₀ (-p) with hrdef
    have hr : 0 < r := lt_min hr₀ (by linarith)
    have hball : ball (p : ℂ) r ⊆ (closure (invHull U S))ᶜ := (ball_subset_ball (min_le_left _ _)).trans hball₀
    have hφ := isRealBoundaryConformal_relBdry hU hU0 hs.le hball
    have hreal : ∀ u ∈ Ioo (p - r) (p + r), (u : ℂ) ∉ closure (invHull U S) ∧ u < 0 := fun u hu =>
      ⟨hball (Sec7.Aux37Side.ofReal_mem_ball_iff.2 hu), by linarith [hu.2, min_le_right r₀ (-p)]⟩
    have hφx : (relBdry U S p).re < 0 := ((relBdry_real_sign hU hU0 hs.le hneg.ne hpA).2).1 hneg
    have hbadJ := sumL_le_of_boundary_chart (θ := θ) hκ hb hKpc hr hφ hneg hφx
      (fun u hu hxu => by
        rcases hxu.eq_or_lt with rfl | hlt
        · exact le_rfl
        · exact (re_relBdry_lt_of_neg hU hU0 hs.le (hreal u hu).2 hlt hpA (hreal u hu).1).le)
      hE hEJ (fun u hu huE huJR => hheight u (hreal u hu).1 huE huJR) hwL
    have hsum := leftSum_le_of_real_bad_tip_off hU hU0 hs.le ha hγc.continuousOn hγ'0 hsafe hRc' hR0' hK hσ him
      (by rw [hpe]; exact hφx) hoff (flowLineXL K.fn K.jumps 0) (flowLineRhoL κ K.fn K.jumps 0 0)
      (by rw [hpe]; exact hbadJ)
    left
    rw [hcoe]
    refine le_trans (le_of_eq ?_) hsum
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    simp only [Ito.rpath]
    rw [show (Rr ((gb6Clock S (regW S Wα ζα) W ω T).toNNReal)) = Rr (relClock U S (Ito.rpath w) T).toNNReal by
      rw [hclk T]]
  · -- a right threshold
    have hwR : SB.Vq.wR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) p ≤ -2 := by
      rcases hbad.2 with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact h1
      · exact absurd h2 (not_le.2 hpos)
    have hpH : (p : ℂ) ∈ hitSet κ b J θ := ofReal_mem_hitSet (Or.inl ⟨hpos, hwR⟩)
    have hprior : ∀ t < T, (γ' t).im = 0 → (γ' t).re < (γ' T).re := by
      intro t htT himt
      have hz := hzR hpos
      have hle := prior_le_of_zero_collision hwc hw0 hγc hwtr hT0 hz (by rw [hpe]; simpa using hpos) htT himt
      rw [hpe, Complex.ofReal_re] at hle ⊢
      exact lt_of_le_of_ne hle (hpbad hpH t htT himt)
    have hoff := relTrace_off_of_prior hU hU0 hs.le ha hsafe him (by rw [hpe]; simpa using hpos) hprior
    set r := min r₀ p with hrdef
    have hr : 0 < r := lt_min hr₀ hpos
    have hball : ball (p : ℂ) r ⊆ (closure (invHull U S))ᶜ := (ball_subset_ball (min_le_left _ _)).trans hball₀
    have hφ := isRealBoundaryConformal_relBdry hU hU0 hs.le hball
    have hreal : ∀ u ∈ Ioo (p - r) (p + r), (u : ℂ) ∉ closure (invHull U S) ∧ 0 < u := fun u hu =>
      ⟨hball (Sec7.Aux37Side.ofReal_mem_ball_iff.2 hu), by linarith [hu.1, min_le_right r₀ p]⟩
    have hφx : 0 < (relBdry U S p).re := ((relBdry_real_sign hU hU0 hs.le hpos.ne' hpA).1).1 hpos
    have hbadJ := sumR_le_of_boundary_chart (θ := θ) hκ hb hKpc hr hφ hpos hφx
      (fun u hu hux => by
        rcases hux.eq_or_lt with rfl | hlt
        · exact le_rfl
        · exact (re_relBdry_lt_of_pos hU hU0 hs.le (hreal u hu).2 hlt (hreal u hu).1 hpA).le)
      hE hEJ (fun u hu huE huJR => hheight u (hreal u hu).1 huE huJR) hwR
    have hsum := rightSum_le_of_real_bad_tip_off hU hU0 hs.le ha hγc.continuousOn hγ'0 hsafe hRc' hR0' hK hσ him
      (by rw [hpe]; exact hφx) hoff (flowLineXR K.fn K.jumps 0) (flowLineRhoR κ K.fn K.jumps 0 0)
      (by rw [hpe]; exact hbadJ)
    right
    rw [hcoe]
    refine le_trans (le_of_eq ?_) hsum
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
    simp only [Ito.rpath]
    rw [show (Rr ((gb6Clock S (regW S Wα ζα) W ω T).toNNReal)) = Rr (relClock U S (Ito.rpath w) T).toNNReal by
      rw [hclk T]]
    exact Iff.rfl

/-- **SAFE's converse at the candidate's death, almost surely** (SAFE's configuration under any probability
measure): almost surely, at every own time `S` of the counterflow with an interior tip, if the candidate dies at a
finite positive time `T` before the relative contact, every continuous driver `Rr` from `0` generating the relative
hulls up to `T` has a continuation threshold of the joint word at the relative clock of `T`. -/
theorem ae_threshold_gw2_at_death {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ}
    {J' : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y) :
    ∀ᵐ ω ∂P, ∀ S : ℝ≥0, γ ω S ∈ H → ∀ T : ℝ≥0, 0 < T → ζα ω = T →
      (T : ℝ≥0∞) < gb6Tc S (extTr S Wα ζα α) γ ω → ∀ Rr : ℝ≥0 → ℝ, Continuous Rr → Rr 0 = 0 →
      (∀ t : ℝ≥0, t ≤ T →
        fwdHull (fun r : ℝ => Rr r.toNNReal) (gb6Clock S (regW S Wα ζα) W ω t) =
          relMap (fun r : ℝ => W r.toNNReal ω) S '' fwdHull (fun r : ℝ => regW S Wα ζα r.toNNReal ω) t) →
      ForceWord.ThresholdCondition
        (flowLineRhoL κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
        (flowLineRhoR κ (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 0)
        (Rr (gb6Clock S (regW S Wα ζα) W ω T).toNNReal)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -Rr v.toNNReal)
          (-flowLineXL (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 i)
          (gb6Clock S (regW S Wα ζα) W ω T).toNNReal)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => Rr v.toNNReal)
          (flowLineXR (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (gw2Word κ θ c' (gb6Rec S W ζ ω)).jumps 0 j)
          (gb6Clock S (regW S Wα ζα) W ω T).toNNReal) := by
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (by positivity : 0 < 16 / κ) hb' hcf
  have hdata := fun x hxJ hx0 hxJ' => data_eq_returnData_gw2 hκ hb hG hb' hG' hT c' hc'J hc'b
    (x := x) hxJ hx0 hxJ'
  have hη := isFlowLine_of_driver hfl hα
  have hfl' := hfl
  obtain ⟨h₁, 𝓕, VL, VR, B, -, hcpl⟩ := hfl'
  filter_upwards [ae_physGood_all hκ hfl hα hcf hγ, GW2Stm.ae_extTr_spec_all hκ hfl hα,
    ae_trace_notMem_hitSet hκ hκ4 hb hG hfl hα, SB.Vr.ae_tip_bad_of_isFlowLine hη, hcpl.1.2.2.2.2,
    hcpl.1.1.1.cont, hα, hγ] with ω hpg hext havoid htipbad hp hBc hαω hγω S hSH T hT0 hζT hTc Rr hRc hR0 hhull
  have hpos : 0 < ζα ω := by rw [hζT]; exact_mod_cast hT0
  obtain ⟨hwc, -, hreg, -, htr⟩ := hext hpos S
  have hbad := htipbad hpos (by rw [hζT]; exact ENNReal.coe_ne_top)
  rw [hζT, ENNReal.toNNReal_coe] at hbad
  simp only [Complex.ofReal_zero, sub_zero] at hbad
  rw [hζT] at hp hαω
  have hz := launch_zero_collision hT0 hp hαω hBc.continuousAt (U := fun t => regW S Wα ζα t ω) hwc
    fun t ht => hreg t (by rw [hζT]; exact_mod_cast ht)
  exact threshold_gw2_at_death (hpg hpos S hSH) hγω.1 hκ hb c' hdata hT0 hζT htr havoid hbad hz.1 hz.2 hTc hRc hR0
    hhull

end InteractingSLE.Theorem14.GW2Nu
