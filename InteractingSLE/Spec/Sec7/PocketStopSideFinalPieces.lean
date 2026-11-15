/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideFinalGeometry
import InteractingSLE.Spec.Sec7.PocketStopSideCoverPieces

/-!
# Incident reference pieces with separation only inside the pocket

PROVE-STRIPSYS38. The common exterior is filled into both comparison sets. Hence
separation of the additional hull is needed only inside C. This is the precise
weaker geometric input useful with R67; the earlier full-plane separation premise
is not required. Choosing the exposed rational old reference still requires BP1's
filled-domain argument and is explicitly retained as `hold` below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling Aux119Heights

section Inputs

variable {Ω : Type*}

/-- The physical boundary selection: the chosen reference is an incoming side or an
old rational hull, and the additional filled hull inside the pocket stays away from the landing point.
The exterior-filled comparison only requires this pocket-side separation. -/
def IncidentReferenceCover [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (C Fnow : Ω → Set ℂ)
    (Fold : ℚ≥0 → Ω → Set ℂ) (q : ℝ≥0) (J : Ω → Set ℝ)
    (faces : CoverRef → Ω → Set ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
    ∀ ξ : ℝ, ξ ∉ J ω → ∃ (i : CoverRef) (p : ℂ) (r : ℝ),
      0 < r ∧ ξ ∈ faces i ω ∧ p ∈ extHullSet (C ω) (Fnow ω) ∪ {z : ℂ | z.im = 0} ∧
      Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) ∧
      referenceHull Fold i ω ⊆ Fnow ω ∧
      Disjoint (C ω ∩ (Fnow ω \ referenceHull Fold i ω)) (ball p r)

end Inputs

section Physical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The physical cover reduces to finite interior landings, identifying which
incoming side faces a landing, and rational old-hull witnesses at exposed hull points.
The wall-or-hull classification and the incoming-side separation are proved here.
`hold` is the precise filled-set separation still needed from the stopped geometry. -/
theorem incidentReferenceCover_of_landings {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {C Fnow : Ω → Set ℂ} {Fold : ℚ≥0 → Ω → Set ℂ}
    {q : ℝ≥0} {J : Ω → Set ℝ} {faces : CoverRef → Ω → Set ℝ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c q ω = C ω ∩ (H \ Fnow ω))
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    (hland : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ J ω → ∃ p ∈ H,
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p))
    (hwall : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ (ξ : ℝ), ξ ∉ J ω → ∀ p ∈ frontier (C ω), p ∉ Fnow ω →
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ j : Fin 2, ξ ∈ faces (Sum.inl j) ω)
    (hold : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ (ξ : ℝ), ξ ∉ J ω → ∀ p ∈ Fnow ω,
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ faces (Sum.inr s) ω ∧
            Fold s ω ⊆ Fnow ω ∧ Disjoint (C ω ∩ (Fnow ω \ Fold s ω)) (ball p r)) :
    IncidentReferenceCover P A γ c C Fnow Fold q J faces := by
  unfold IncidentReferenceCover
  filter_upwards [hland, hwall, hold] with ω hωland hωwall hωold hω hq ξ hξ
  obtain ⟨p, hpH, hp⟩ := hωland hω hq ξ hξ
  have hclass := active_landing_on_wall_or_hull hω hq (hγ ω hω) (hc ω hω)
    (hact ω hω hq) (hFo ω hω hq) hpH hp
  by_cases hpF : p ∈ Fnow ω
  · obtain ⟨s, r, hr, hface, hsub, haway⟩ := hωold hω hq ξ hξ p hpF hp
    exact ⟨Sum.inr s, p, r, hr, hface, Or.inl ⟨hpH, Or.inr hpF⟩, hp, hsub, haway⟩
  · have hpfr : p ∈ frontier (C ω) := hclass.resolve_right hpF
    obtain ⟨j, hface⟩ := hωwall hω hq ξ hξ p hpfr hpF hp
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ((hFo ω hω hq).mem_nhds ⟨hpH, hpF⟩)
    have hpC : p ∉ C ω := by
      rw [(hCo ω hω).frontier_eq] at hpfr
      exact hpfr.2
    refine ⟨Sum.inl j, p, r, hr, hface, Or.inl ⟨hpH, Or.inl hpC⟩, hp,
      empty_subset _, ?_⟩
    change Disjoint (C ω ∩ (Fnow ω \ ∅)) (ball p r)
    rw [sdiff_empty, disjoint_left]
    exact fun z hzF hzr => (hball hzr).2 hzF.2

end Physical

section Cover

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Construct the original boundary-cover predicate with all local-agreement and
inverse-approach obligations discharged. The remaining named inputs are the physical
selection, reference heights, transition arguments, and exact phase/word identity. -/
theorem pocketStopBoundaryCover_of_incident_pieces {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {c : Ω → Chart}
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
    (hlift : ReferenceLiftLimits P A γ c q faces liftB branch) {n : Ω → ℤ} {a : ℝ}
    (hword : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ i ξ, ξ ∈ faces i ω → height i ω ξ + chiC κ *
        (2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω) = forceBoundaryData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a) :
    PocketStopBoundaryCover κ ρL ρR P A γ xL xR (fun ω => shiftChart (c ω) (n ω)) a u
      (activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q) q
      (referenceSet C Fold) gB liftB := by
  unfold PocketStopBoundaryCover
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

end Cover

end InteractingSLE.Sec7.PocketStopSide
