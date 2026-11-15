/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseConst
import InteractingSLE.Spec.Sec7.OuterPhSide

/-!
# Outer-pocket selection from a named shared-side visit hypothesis

PROVE-R7-OUTERPHASE continuation. The unfinished R.6 witness construction is
stated explicitly as `TwoSeedSharedVisitsInput` and its infinity counterpart.
Their conclusions concern a countable family of joint zero-phase visits, not
conditional laws at a future-dependent selected time. The selection theorem
retains the phase word, branch, offset and continuous phase of its input.
These conditional helpers do not prove the actual shared-side hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.OuterPhNext

open PocketTraversal Lemma71C PocketStop PocketWordAssembly PocketSeedOpen
  PocketCoupling PocketJordan Hsd PhaseClause PocketStopField

section Inputs

variable {Ω : Type*}

/-- Named, unproved R.6 step for a bounded outer pocket: for each coherent
phase word, construct countably many joint zero-phase comparisons whose
positive live visits cover the test. This is required only outside Aux. 122's
bounded sector in the R.7 assembly. -/
def TwoSeedSharedVisitsInput (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAll R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∃ (s : ℕ → Ω → ℝ≥0) (E : ℕ → Set Ω),
        (∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0) ∧
        ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
          ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i

/-- The same named R.6 witness construction for a pocket opening at the flow
seed. It has the same phase and probability quantifiers as the bounded case. -/
def TwoSeedSharedVisitsInputInf (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAllInf R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∃ (s : ℕ → Ω → ℝ≥0) (E : ℕ → Set Ω),
        (∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0) ∧
        ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
          ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i

end Inputs

section Select

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
  {P : Measure Ω} {k rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}

/-- R.5, continuity, and the exact named R.6 visits give the original
three-part side input, with the same branch, offset and phase. -/
theorem twoSeedPhaseSideInput_of_cont_shared
    (hcont : TwoSeedPhaseContInput k rL rR 𝓦 P R L r η G h₀ u)
    (hshared : TwoSeedSharedVisitsInput k rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseSideInput k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, a, δ, hphase, hc⟩ := hcont A hA hAG hPA ψ hJ hPt
  obtain ⟨s, E, hzero, hvisit⟩ := hshared A hA hAG hPA ψ hJ hPt n hn a δ hphase hc
  exact ⟨n, hn, a, δ, hphase, hc,
    PocketStopSide.ae_phase_anchor_of_countable_visits hzero hvisit⟩

/-- The shared-side selection at the flow seed, preserving the original
phase version rather than evaluating a fixed-time a.e. statement randomly. -/
theorem twoSeedPhaseSideInputInf_of_cont_shared
    (hcont : TwoSeedPhaseContInputInf k rL rR 𝓦 P R L r η G h₀ u)
    (hshared : TwoSeedSharedVisitsInputInf k rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseSideInputInf k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, a, δ, hphase, hc⟩ := hcont A hA hAG hPA ψ hJ hPt
  obtain ⟨s, E, hzero, hvisit⟩ := hshared A hA hAG hPA ψ hJ hPt n hn a δ hphase hc
  exact ⟨n, hn, a, δ, hphase, hc,
    PocketStopSide.ae_phase_anchor_of_countable_visits hzero hvisit⟩

end Select

end InteractingSLE.Sec7.OuterPhNext
