/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimCover
import InteractingSLE.Spec.Sec7.PocketStopSideFinalPieces

/-!
# Reference pieces before selecting the common phase

PROVE-STRIPSYS38. All geometric and limit adapters from the committed incident
cover are reused. The numerical alignment is the phase word rather than the
zero-phase word. Its common phase is a scalar, not a separately chosen branch
on each reference piece. The physical collar and reference-height producers
remain explicit; this file does not prove them for the strip construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling Aux119Heights PhaseSel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The physical pieces and inherited reference lifts produce the phase cover
without requiring its common phase to vanish. -/
theorem pocketStopPhaseBoundaryCover_of_incident_pieces {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart}
    {C Fnow : Ω → Set ℂ} {Fold : ℚ≥0 → Ω → Set ℂ} {q : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = C ω ∩ (H \ Fnow ω))
    {faces : CoverRef → Ω → Set ℝ}
    (hpieces : IncidentReferenceCover P A γ c C Fnow Fold q (fun ω => forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)) faces)
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {liftB : CoverRef → Ω → ℂ → ℝ} {height : CoverRef → Ω → ℝ → ℝ}
    (hheight : ReferenceHeightLimits (chiC κ) P A γ c C Fold q u faces gB liftB height)
    {branch : CoverRef → Ω → ℝ → ℤ}
    (hlift : ReferenceLiftLimits P A γ c q faces liftB branch) {n : Ω → ℤ} {a : ℝ} {δ : Ω → ℝ}
    (hword : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ i ξ, ξ ∈ faces i ω → height i ω ξ + chiC κ *
        (2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω) = phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (δ ω) ξ - a) :
    PocketStopPhaseBoundaryCover κ ρL ρR P A γ xL xR (fun ω => shiftChart (c ω) (n ω)) a u
      (activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q) δ q
      (referenceSet C Fold) gB liftB := by
  unfold PocketStopPhaseBoundaryCover
  unfold IncidentReferenceCover at hpieces
  unfold ReferenceHeightLimits at hheight
  unfold ReferenceLiftLimits at hlift
  filter_upwards [hpieces, hheight, hlift, hword] with ω hωp hωh hωl hωw hω hq ξ hξ
  obtain ⟨i, p, r, hr, hface, hp, hland, hsub, haway⟩ := hωp hω hq ξ hξ
  have hK : activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q ω =
      extHullSet (C ω) (Fnow ω) := by
    rw [activeCompl_shift, activeCompl_eq_liveExt hact, liveExt_of_live ⟨hω, hq⟩]
  have heq : activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q ω ∩ ball p r =
      referenceSet C Fold i ω ∩ ball p r := by
    rw [hK]
    exact extHullSet_inter_ball_eq_of_pocket hsub haway
  have hpK : p ∈ activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q ω ∪
      {z : ℂ | z.im = 0} := by rwa [hK]
  have hpB : p ∈ referenceSet C Fold i ω ∪ {z : ℂ | z.im = 0} := by
    rcases hpK with hpK | hpR
    · exact Or.inl ((heq ▸ (show p ∈ activeCompl A γ
        (fun ω => shiftChart (c ω) (n ω)) q ω ∩ ball p r from ⟨hpK, mem_ball_self hr⟩) :
          p ∈ referenceSet C Fold i ω ∩ ball p r)).1
    · exact Or.inr hpR
  obtain ⟨hBK, hKB⟩ := local_agreement_of_inter_ball_eq hr heq
  have hland' : Tendsto (relChart (fun ω => shiftChart (c ω) (n ω)) γ q ω).2.1
      (𝓝[H] (ξ : ℂ)) (𝓝 p) := by rwa [relChart_shift_inv]
  have hconf : (shiftChart (c ω) (n ω)).IsConformal := hc ω hω
  have hmap : ∀ y ∈ H, (relChart (fun ω => shiftChart (c ω) (n ω)) γ q ω).2.1 y ∈
      H \ activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q ω :=
    fun y hy => relChart_inv_mem_active hω hq (hγ ω hω) hconf hy
  refine ⟨i, p, height i ω ξ, 2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω,
    hpK, hpB, hBK, hKB, tendsto_common_compl hland' hmap hr heq, ?_, ?_, hωw hω hq i ξ hface⟩
  · rw [relChart_shift_inv]
    exact hωh hω hq i ξ hface
  · rw [relChart_shift_inv]
    have h := (hωl hω hq i ξ hface).sub_const (2 * Real.pi * n ω)
    exact h.congr fun z => by
      rw [relChart_shift_lift]
      ring


end InteractingSLE.Sec7.PocketStopSide
