/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimR6
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# Canonical side limits from an inner zero-phase pocket

PROVE-STRIPSYS38. This implements R7POCKET's suggested R.6 reduction. Both
pockets use the same ambient field, parameter and constant offset. The inner
pocket supplies its canonical side limit. The exact remaining geometric and
local-germ comparison input is `hNestedGerm` below; it does not assert equality
of the complete conditional means. This is a conditional reduction, not a
construction of the nested pockets or an unconditional strip side limit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PhaseSel Aux119Heights

/-- R.6 removes the phase at one visit, using an actual inner canonical side
limit and a comparison of the local ambient germs. The full type of the
unconstructed nested-chart comparison is retained in `hNestedGerm`. -/
theorem ae_phase_eq_zero_of_inner_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 4 < κ)
    {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ}
    {A B : Set Ω} {γ η : Ω → ℝ → ℂ} {c cU : Ω → Chart}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {yL : Ω → Fin (mL + 1) → ℝ} {yR : Ω → Fin (mR + 1) → ℝ}
    {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K KU : Ω → Set ℂ} {δ : Ω → ℝ} {q qU : ℝ≥0}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h₀ P)
    (hKUm : Measurable[mΩ, hittingSigma] KU) (hKUloc : IsLocalSet KU h₀ P)
    (hPhase : PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K δ q)
    (hInner : PocketStopSideLimit κ σL σR P B η yL yR cU a h₀ u KU qU)
    (hNestedGerm : ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
      ∀ gU : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean KU h₀ P gU →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        let lC := fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q
        let rC := fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q
        let lU := fun i => geomLW (fun t ω => segDriver (η ω) t) yL i qU ω - segDriver (η ω) qU
        let rU := fun j => geomRW (fun t ω => segDriver (η ω) t) yR j qU ω - segDriver (η ω) qU
        ∃ (ξ ζ y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU : ℝ),
          ω ∈ B ∧ (qU : ℝ≥0∞) < capLife (η ω) ∧
          ξ ∉ forceJumpSet lC rC ∧ ζ ∉ forceJumpSet lU rU ∧ ξ ∈ Ioo (lC 0) (rC 0) ∧
          forceBoundaryData κ ρL ρR lC rC ξ = forceBoundaryData κ σL σR lU rU ζ ∧
          IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
          (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
          ContinuousOn (fun y : ℝ => L y) J ∧
          (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
          bC = bU ∧ bU = bC + chiC κ * (L y₀).im ∧
          ContinuousWithinAt L Hbar (ξ : ℂ) ∧
          Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (ζ : ℂ)) ∧
          Tendsto (fun z =>
            sideMean κ (relChart cU η qU ω) u (harmRep (gU ω) (H \ KU ω)) (φ z) -
              sideMean κ (relChart c γ q ω) u (harmRep (g ω) (H \ K ω)) z - chiC κ * (L z).im)
            (𝓝[H] (ξ : ℂ)) (𝓝 0)) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → δ ω = 0 := by
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh₀ hKm hKloc
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hh₀ hKUm hKUloc
  have hχ : chiC κ ≠ 0 := by
    intro h
    apply phaseStep_ne_zero hκ
    rw [phaseStep, h, neg_zero, mul_zero]
  filter_upwards [hPhase.2 g hg, hInner gU hgU, hg.2.1, hgU.2.1, hNestedGerm g hg gU hgU]
    with ω hCside hUside hgω hgUω hnested hω hq
  obtain ⟨ξ, ζ, y₀, J, φ, L, bC, bU, hωB, hqU, hξJ, hζJ, hξexposed, hmatch,
    hJ, hξ, hy₀, hloc, hLc, hexp, hsame, htransform, hLξ, hφ, hcompare⟩ := hnested hω hq
  obtain ⟨hv, hvr⟩ := harmRep_spec hgω
  obtain ⟨hvU, hvrU⟩ := harmRep_spec hgUω
  have hC := hCside hω hq _ hv hvr ξ hξJ
  have hU := hUside hωB hqU _ hvU hvrU ζ hζJ
  rw [phaseData, indicator_of_mem hξexposed, Pi.one_apply, mul_one] at hC
  have he : ∀ b d : ℝ, b + d - a = (b - a) + d := fun _ _ => by ring
  rw [he] at hC
  rw [← hmatch] at hU
  exact phase_eq_zero_of_inner_germ hχ hJ hloc hLc hexp hy₀ hsame htransform hξ hLξ hφ hC hU hcompare

/-- The unchanged canonical predicate follows from the R.6 phase anchor, for
all versions of the stopped mean. -/
theorem pocketStopSideLimit_of_phase_and_inner_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 4 < κ)
    {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ}
    {A B : Set Ω} {γ η : Ω → ℝ → ℂ} {c cU : Ω → Chart}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {yL : Ω → Fin (mL + 1) → ℝ} {yR : Ω → Fin (mR + 1) → ℝ}
    {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K KU : Ω → Set ℂ} {δ : Ω → ℝ} {q qU : ℝ≥0}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h₀ P)
    (hKUm : Measurable[mΩ, hittingSigma] KU) (hKUloc : IsLocalSet KU h₀ P)
    (hPhase : PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K δ q)
    (hInner : PocketStopSideLimit κ σL σR P B η yL yR cU a h₀ u KU qU)
    (hNestedGerm : ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
      ∀ gU : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean KU h₀ P gU →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        let lC := fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q
        let rC := fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q
        let lU := fun i => geomLW (fun t ω => segDriver (η ω) t) yL i qU ω - segDriver (η ω) qU
        let rU := fun j => geomRW (fun t ω => segDriver (η ω) t) yR j qU ω - segDriver (η ω) qU
        ∃ (ξ ζ y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU : ℝ),
          ω ∈ B ∧ (qU : ℝ≥0∞) < capLife (η ω) ∧
          ξ ∉ forceJumpSet lC rC ∧ ζ ∉ forceJumpSet lU rU ∧ ξ ∈ Ioo (lC 0) (rC 0) ∧
          forceBoundaryData κ ρL ρR lC rC ξ = forceBoundaryData κ σL σR lU rU ζ ∧
          IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
          (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
          ContinuousOn (fun y : ℝ => L y) J ∧
          (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
          bC = bU ∧ bU = bC + chiC κ * (L y₀).im ∧
          ContinuousWithinAt L Hbar (ξ : ℂ) ∧
          Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (ζ : ℂ)) ∧
          Tendsto (fun z =>
            sideMean κ (relChart cU η qU ω) u (harmRep (gU ω) (H \ KU ω)) (φ z) -
              sideMean κ (relChart c γ q ω) u (harmRep (g ω) (H \ K ω)) z - chiC κ * (L z).im)
            (𝓝[H] (ξ : ℂ)) (𝓝 0)) :
    PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K q := by
  exact pocketStopSideLimit_of_phase_eq_zero hPhase
    (ae_phase_eq_zero_of_inner_zero hκ hh₀ hKm hKloc hKUm hKUloc hPhase hInner hNestedGerm)

end InteractingSLE.Sec7.PocketStopSide
