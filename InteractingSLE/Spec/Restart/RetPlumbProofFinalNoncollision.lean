/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalSeed

/-!
# Discharging the retained pre-lifetime nonthreshold input

Packet PROVE-RETPLUMB. The source's boundary-stopped trace is interior at every
positive time before its lifetime. At zero its own two slit heights give an
admissible seed. These two facts discharge `RetPrelifeNonThreshold`.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7.PocketTraversal

/-- An admissible word has no time-zero threshold in any fixed-type reading. -/
theorem not_threshold_of_isFlowType_admissible {κ θ : ℝ} (hκ : 0 < κ)
    {c : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (ht : FCDet.IsFlowType κ θ c xL xR ρL ρR)
    (ha : ExplState.IsAdmissibleSeed κ
      (PiecewiseConstantBoundaryData.leftLim c.fn 0)
      (PiecewiseConstantBoundaryData.rightLim c.fn 0) θ) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := ht
  subst nL nR
  change xL = flowLineXL c.fn c.jumps 0 at hxL
  change xR = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 θ at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 θ at hρR
  rw [hxL, hxR, hρL, hρR]
  exact fun h => ((Theorem14.GW1.thresholdCondition_flowLine_zero_iff hκ c.fn c.jumps θ).1 h) ha

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The actual retained geometric driver satisfies the nonthreshold input on
every initial type event. No force noncollision or seed hypothesis remains. -/
theorem retPrelifeNonThreshold_of_retWordAt {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {x₁ x₂ κ θ₁ θ₂ : ℝ} {c₀ : BoundaryWord} {F : Set Ω}
    (hκ : 0 < κ) (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hG : F ⊆ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hx : x₂ < x₁)
    (hpair : ∀ ω ∈ F, Sec7.Lemma76Exit.IsDisjointPair
      (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (ht : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂
      (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => W t ω)
    (h0 : ∀ ω, W 0 ω = 0)
    (hg : ∀ ω ∈ F, IsGeneratingTrace (fun t => W t ω)
      (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω)) :
    RetPrelifeNonThreshold (P := P) ρL ρR W xL xR
      (F.indicator (retLife G η₁' η₂' ζ₂ u r)) F := by
  classical
  refine Eventually.of_forall fun ω hω t htl => ?_
  have htV : (t : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω := by
    simpa only [indicator_of_mem hω] using htl
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from zero_le) with he | hpos
  · subst t
    obtain ⟨hL, hR⟩ := retWordAt_incident_heights hd (hG hω) (hp₁ ω hω)
      (hp₂ ω hω) hx (hpair ω hω) hc₀
    have ha : ExplState.IsAdmissibleSeed κ
        (PiecewiseConstantBoundaryData.leftLim
          (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω).fn 0)
        (PiecewiseConstantBoundaryData.rightLim
          (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω).fn 0) θ₂ := by
      rw [hL, hR]
      have hΛ := Sec4.sleLambda_pos hκ
      constructor <;> linarith
    have hs := isFlowType_signs (ht ω hω)
    simpa only [geomLW_zero hc h0 (hs.1 _), geomRW_zero hc h0 (hs.2 _), h0 ω] using
      not_threshold_of_isFlowType_admissible hκ (ht ω hω) ha
  · obtain ⟨hL, hR⟩ := geom_images_ne_of_tip_mem_H xL xR (hc ω) (h0 ω) (hg ω hω)
      hpos htV.le (retPath_mem_H_before_life hd (hG hω) (hp₂ ω hω) (hpair ω hω) hpos htV)
    exact not_threshold_of_images_ne hL hR

end InteractingSLE.Restart.RetAux79
