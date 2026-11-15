/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KbRoot
import InteractingSLE.Spec.Supplement.GW2OmxDrv
import InteractingSLE.Spec.Supplement.GW2OmxDil5
import InteractingSLE.Spec.Supplement.BW1LMeanRet
import InteractingSLE.Spec.Supplement.Q3ChainMeas
import InteractingSLE.Spec.Exist.StagedLaw2Flow
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide

/-!
# Claim(k)'s base (GEOM2 round 12): the root piece's union form read in the stage chart

Packet PROVE-GW2-GEOM2, round 12 (deterministic, one sample). At the end `T` of the root piece, GW2's union form
`UnionFormAt` (counterflow retained at `s`, root piece at `T`) together with the stage shape of the root piece's unions
at every time `u ≤ T` (the version's hull clause: `ℍ ∖ (invHull ∪ K_u) = relChart⁻¹(ℍ ∖ K^R_{A u})`, `A 0 = 0`) is
the explicit stage mean at clock `0` of the stage chart `cs = stgChart (relChart rec) R (A T)`:

* **`root_stage_read`**: `w = G ∘ cs.1 − u₀ − (specOffset κ + θ χ) − χ · cs.lift` off the union, `G` a bounded harmonic
  extension of the joint word's angle-`θ` data flowed by the version's driver `R` to `A T`. The relative chain of the
  union form is the version's driver (`GW2Omx.sample_driver_scale` with the identity launch chart, `λ = 1`), the
  stage chart's lift is the relative chart's lift `Im relLog − 2π` plus the Loewner term
  (`BW1LMean.relChart_lift_eq`), and `uθ − u₀ = θχ` (`bhe_angle_sub`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)

namespace InteractingSLE.Theorem14.GW2Kb

open GW2Omx GW2TipSystem Exist Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6LMean GW2JointKernel Restart
open Supp8.Q3Rel (invHull relLog)
open Supp8.Q3Chain (flowedData flowedJumps)

/-- The joint word of the counterflow record at `s` (the word of GW2's union mean). -/
abbrev jw {Ω : Type*} (κ : ℝ) (c' : BoundaryWord) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    BoundaryWord :=
  jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)

/-- `Chart.id.recenter 0` has domain `ℍ`. -/
theorem coe_dom_recenter_id_zero : ((Chart.id.recenter 0).dom : Set ℂ) = H := by
  rw [(Chart.isConformal_id.recenter 0).coe_dom]
  ext z
  simp [Chart.recenter, Chart.id]

/-- **The root piece's union form read in the stage chart** (one sample). -/
theorem root_stage_read {Ω : Type*} {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {u₀ uθ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uθ)
    {c' : BoundaryWord} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {Wα : ℝ≥0 → Ω → ℝ} {ω : Ω} {s T : ℝ≥0}
    (hW0 : W 0 ω = 0) (hWc : Continuous fun t => W t ω) (hsζ : (s : ℝ≥0∞) < ζ ω)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} (hA0 : A 0 = 0)
    (hAc : ContinuousOn A (Icc 0 T))
    (hshape : ∀ u ≤ T, H \ (invHull (fun q : ℝ => W q.toNNReal ω) s ∪ fwdHull (fun q : ℝ => Wα q.toNNReal ω) u) =
      (RelSafeS.relChart (gb6Rec s W ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    (hdisj : ∀ u : ℝ≥0, u ≤ T →
      fwdHull (fun q : ℝ => Wα q.toNNReal ω) u ⊆ H \ invHull (fun q : ℝ => W q.toNNReal ω) s)
    {w : ℂ → ℝ} (hform : UnionFormAt κ θ b J c' W ζ Wα uθ ω s T w
      (H \ (invHull (fun q : ℝ => W q.toNNReal ω) s ∪ fwdHull (fun q : ℝ => Wα q.toNNReal ω) T))) :
    ∃ G : ℂ → ℝ, IsBoundedHarmonicExtension
        (flowedData κ (flowLineRhoL κ (jw κ c' s W ζ ω).fn (jw κ c' s W ζ ω).jumps 0 θ)
          (flowLineRhoR κ (jw κ c' s W ζ ω).fn (jw κ c' s W ζ ω).jumps 0 θ)
          (flowLineXL (jw κ c' s W ζ ω).fn (jw κ c' s W ζ ω).jumps 0)
          (flowLineXR (jw κ c' s W ζ ω).fn (jw κ c' s W ζ ω).jumps 0) (Ito.rpath R) (A T))
        (flowedJumps (flowLineXL (jw κ c' s W ζ ω).fn (jw κ c' s W ζ ω).jumps 0)
          (flowLineXR (jw κ c' s W ζ ω).fn (jw κ c' s W ζ ω).jumps 0) (Ito.rpath R) (A T)) G ∧
      ∀ z ∈ H \ (invHull (fun q : ℝ => W q.toNNReal ω) s ∪ fwdHull (fun q : ℝ => Wα q.toNNReal ω) T),
        w z = G ((GW2Rd.stgChart (RelSafeS.relChart (gb6Rec s W ζ ω)) R (A T)).1 z) - u₀ z -
          (specOffset κ + θ * chiC κ) -
            chiC κ * (GW2Rd.stgChart (RelSafeS.relChart (gb6Rec s W ζ ω)) R (A T)).2.2 z := by
  obtain ⟨p, G, hp, hG, hEq⟩ := hform
  obtain ⟨-, -, -, ⟨t₂, hTt₂, hp1eq⟩, hRkc, hRk0, -, -, -, hhulls, -⟩ := hp
  set U : ℝ → ℝ := fun r => W r.toNNReal ω with hUdef
  set Wc : ℝ → ℝ := fun r => p.1 r.toNNReal with hWcdef
  set rec := gb6Rec s W ζ ω with hrec
  set c₀ := RelSafeS.relChart rec with hc₀def
  have hUc : Continuous U := hWc.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp [hUdef, hW0]
  -- the relative chain's piece is the root piece up to `T`
  have hWcEq : ∀ u : ℝ≥0, u ≤ T → fwdHull Wc u = fwdHull (fun q : ℝ => Wα q.toNNReal ω) u := by
    intro u hu
    refine _root_.InteractingSLE.fwdHull_eq_of_eqOn u.coe_nonneg
      (lt_of_le_of_lt (by exact_mod_cast hu) (by exact_mod_cast hTt₂ : (T : ℝ) < t₂)) fun q hq => ?_
    exact hp1eq q.toNNReal (Real.toNNReal_le_iff_le_coe.2 hq.2)
  -- the driver relation (`λ = 1`, identity launch chart)
  have hdil : ∀ x ∈ ((GW2Rd.stgChart c₀ R 0).dom : Set ℂ),
      relMap U s ((Chart.id.recenter 0).1 x) = ((1 : ℝ) : ℂ) * (GW2Rd.stgChart c₀ R 0).1 x := by
    intro x _
    have e1 : (Chart.id.recenter 0).1 x = x := by simp [Chart.recenter, Chart.id]
    have e2 : (GW2Rd.stgChart c₀ R 0).1 x = c₀.1 x := Exist.StagedLaw.fwdMap_zero_time (by simp [Ito.rpath, hR0]) _
    rw [e1, e2, relChart_gb6Rec_fst hW0 hWc.continuousOn hsζ x, Complex.ofReal_one, one_mul]
  set B : ℝ≥0 → Set ℂ := fun u => invHull U s ∪ fwdHull (fun q : ℝ => Wα q.toNNReal ω) u with hBdef
  have hBH : ∀ u, B u ⊆ H := fun u => union_subset (GW2Shr.invHull_subset_H hUc s.coe_nonneg)
    (Exist.fwdHull_subset_H u.coe_nonneg)
  have hunion : ∀ u : ℝ≥0, u ≤ T → (Chart.id.recenter 0).1 '' (B u ∩ ((Chart.id.recenter 0).dom : Set ℂ)) =
      invHull U s ∪ fwdHull Wc u := by
    intro u hu
    rw [coe_dom_recenter_id_zero, inter_eq_left.2 (hBH u), hWcEq u hu]
    have e : (Chart.id.recenter 0).1 = id := funext fun z => by simp [Chart.recenter, Chart.id]
    rw [e, image_id]
  obtain ⟨hdrv, hclk⟩ := sample_driver_scale (Chart.isConformal_id.recenter 0) (RelSafeS.isConformal_relChart rec)
    hR hR0 hUc hU0 one_pos hdil hA0 (fun u => zero_le) hAc hshape (KT := ∅)
    (by rw [coe_dom_recenter_id_zero, sdiff_empty]) (fun u _ => empty_subset _) hRkc hRk0 hhulls
    (fun u hu => by rw [hWcEq u hu]; exact hdisj u hu) hunion
  -- the relative chain is the version's driver on `[0, A T]`, and its clock is `A T`
  have hq : relClock U s Wc T = (A T : ℝ) := by simpa using hclk
  have hRkEq : EqOn p.2.2.1 (Ito.rpath R) (Icc 0 (A T : ℝ)) := by
    intro x hx
    have h := hdrv (show x ∈ Icc 0 ((A T : ℝ) - 0) by rwa [sub_zero])
    simp only [one_pow, one_mul, div_one] at h
    rw [← h]
    simp [Ito.rpath, GW2Rd.stgDrv, hR0]
  have hAT : (0 : ℝ) ≤ A T := (A T).coe_nonneg
  -- the bounded harmonic extension of the flowed word, read along `R`
  refine ⟨G, ?_, fun z hz => ?_⟩
  · have e1 : ∀ x, markPos p.2.2.1 (A T : ℝ) x = markPos (Ito.rpath R) (A T : ℝ) x :=
      Sec7.StripSideHeightProb.markPos_congr hRkEq
    have e2 : ∀ x, markPosL p.2.2.1 (A T : ℝ) x = markPosL (Ito.rpath R) (A T : ℝ) x :=
      Sec7.StripSideHeightProb.markPosL_congr hRkEq
    have hG' := hG
    change IsBoundedHarmonicExtension (flowedData κ _ _ _ _ p.2.2.1 (relClock U s Wc T))
      (flowedJumps _ _ p.2.2.1 (relClock U s Wc T)) G at hG'
    rw [hq] at hG'
    simpa only [flowedData, flowedJumps, e1, e2] using hG'
  · have hzH : z ∈ H := hz.1
    have hzI : z ∉ invHull U s := fun h => hz.2 (Or.inl h)
    have hEz := hEq hz
    change w z + uθ z = G (fwdMap p.2.2.1 (relClock U s Wc T) (relMap U s z)) -
      chiC κ * ((logDerivFwd p.2.2.1 (relClock U s Wc T) (relMap U s z)).im + (relLog U s z).im) at hEz
    rw [hq] at hEz
    have hfm : fwdMap p.2.2.1 (A T : ℝ) (relMap U s z) = fwdMap (Ito.rpath R) (A T : ℝ) (relMap U s z) :=
      _root_.InteractingSLE.fwdMap_eq_of_eqOn hAT fun x hx => hRkEq hx
    have hld : logDerivFwd p.2.2.1 (A T : ℝ) (relMap U s z) = logDerivFwd (Ito.rpath R) (A T : ℝ) (relMap U s z) :=
      Ito.logDerivFwd_congr_of_eqOn hRkEq hAT le_rfl
    rw [hfm, hld] at hEz
    -- the stage chart at `A T`
    have hrs : BW1Ver.recS rec = s := NNReal.coe_injective (by
      rw [← BW1Ver.rtime_eq_recS]
      exact Supp8.GB6.rtime_recOf_cfE s hsζ)
    have hrd : ∀ x ∈ Icc (0 : ℝ) (BW1Ver.recS rec), rdrv rec x = U x := by
      intro x hx
      rw [hrec, gb6Rec]
      exact Supp8.GB6.rdrv_recOf_cfE s hW0 hWc.continuousOn hsζ (by rw [hrs] at hx; exact hx.2)
    have hzD : z ∈ (c₀.dom : Set ℂ) := by
      rw [BW1LMean.coe_dom_relChart, show BW1Ver.recS rec = s from hrs,
        show invHull (rdrv rec) (s : ℝ) = invHull U s from
          Supp8.RelSafeS.invHull_record_eq hW0 hWc.continuousOn hsζ]
      exact ⟨hzH, hzI⟩
    have hlift : c₀.2.2 z = (relLog U s z).im - 2 * Real.pi := by
      rw [BW1LMean.relChart_lift_eq rec hzD, Supp8.Q3Chain.relLog_eq_of_eqOn (BW1Ver.recS rec).coe_nonneg hrd, hrs]
    have hc1 : c₀.1 z = relMap U s z := relChart_gb6Rec_fst hW0 hWc.continuousOn hsζ z
    have hcs1 : (GW2Rd.stgChart c₀ R (A T)).1 z = fwdMap (Ito.rpath R) (A T : ℝ) (relMap U s z) := by
      change fwdMap (Ito.rpath R) (A T : ℝ) (c₀.1 z) = _
      rw [hc1]
    have hcs2 : (GW2Rd.stgChart c₀ R (A T)).2.2 z =
        (logDerivFwd (Ito.rpath R) (A T : ℝ) (relMap U s z)).im + ((relLog U s z).im - 2 * Real.pi) := by
      change (logDerivFwd (Ito.rpath R) (A T : ℝ) (c₀.1 z)).im + c₀.2.2 z = _
      rw [hc1, hlift]
    have hθ := bhe_angle_sub hκ hb hu₀ huθ z hzH
    rw [hcs1, hcs2]
    unfold specOffset
    linarith

end InteractingSLE.Theorem14.GW2Kb
