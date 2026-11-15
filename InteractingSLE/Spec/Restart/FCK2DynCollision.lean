/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2DynSeed
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCollision
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj

/-!
# First-contact collision checks: interior points and retained-pair obstruction

Interior positive-time tips have no geometric force collision. Thus the
pre-lifetime check reduces to boundary visits and the initial seed. Ordinary
retained-pair R1 cannot be applied directly to a shifted first-contact line:
its fixed tip is already in the other retained prefix.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb
open RetAux79 Sec7.PocketTraversal

/-- A common point at the second cutoff excludes an ordinary retained pair
at every extension of the first prefix. -/
theorem not_ordinary_of_retained_contact {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {a c s : ℝ≥0} (he : α a = β c) (has : a ≤ s) :
    ¬ Supp7.IsOrdinaryRetainedPair α ζ₁ s β ζ₂ c := by
  intro ho
  exact ho.2.2.2.2.1 ⟨a, ⟨zero_le, has⟩, he⟩

/-- None of the later first-contact lines is an ordinary retained pair.
This obstruction holds even when the moving tip is interior and live. -/
theorem not_ordinary_firstContact_line {Ω : Type*} [MeasurableSpace Ω]
    {d : PairData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (t : ℝ≥0) :
    ¬ Supp7.IsOrdinaryRetainedPair (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω + t)
      (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) :=
  not_ordinary_of_retained_contact (hd.isFirstContact hE).2.2.1 (le_add_of_nonneg_right zero_le)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
  {U : Ω → ℝ≥0∞} {M : Set Ω} {γ : Ω → ℝ≥0 → ℂ}

/-- Only positive-time noninterior tips require a force-weight check. The
interior case follows from the landed inverse-map terminal theorem, and the
time-zero case from the supplied seed condition. -/
theorem prelifeNonThreshold_of_boundary_checks
    (hc : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0)
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j)
    (hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (U ω) (γ ω))
    (hseed : ∀ᵐ ω ∂P, ω ∈ M →
      ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hboundary : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U ω →
      γ ω t ∉ QuantumZipper.H →
      ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
        (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω)) :
    RetPrelifeNonThreshold (P := P) ρL ρR W xL xR U M := by
  filter_upwards [hg, hseed, hboundary] with ω hgω hs hb hω t ht
  by_cases ht0 : t = 0
  · subst t
    have hL : (fun i => geomLW W xL i 0 ω) = xL ω :=
      funext fun i => geomLW_zero hc h0 (hxL ω i)
    have hR : (fun j => geomRW W xR j 0 ω) = xR ω :=
      funext fun j => geomRW_zero hc h0 (hxR ω j)
    rw [hL, hR, h0]
    exact hs hω
  · by_cases hH : γ ω t ∈ QuantumZipper.H
    · obtain ⟨hL, hR⟩ := geom_images_ne_of_tip_mem_H xL xR (hc ω) (h0 ω)
        (hgω hω) (pos_iff_ne_zero.2 ht0) ht.le hH
      exact not_threshold_of_images_ne hL hR
    · exact hb hω t (pos_iff_ne_zero.2 ht0) ht hH

/-- The collision lifetime identity now needs boundary checks only before
death; all interior pre-lifetime collision checks have been discharged. -/
theorem ae_life_eq_thr_of_boundary_checks
    (hc : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0)
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j)
    (hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (U ω) (γ ω))
    (hseed : ∀ᵐ ω ∂P, ω ∈ M →
      ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hboundary : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U ω →
      γ ω t ∉ QuantumZipper.H →
      ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
        (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω))
    (hterminal : ∀ᵐ ω ∂P, ω ∈ M → ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω →
      ForceWord.ThresholdCondition ρL ρR (W T ω)
        (fun i => geomLW W xL i T ω) (fun j => geomRW W xR j T ω)) :
    ∀ᵐ ω ∂P, ω ∈ M → U ω = FCDet.thr ρL ρR W xL xR ω :=
  ae_life_eq_thr_of_preterminal hc
    (prelifeNonThreshold_of_boundary_checks hc h0 hxL hxR hg hseed hboundary) hterminal

end InteractingSLE.Restart.FCPlumb
