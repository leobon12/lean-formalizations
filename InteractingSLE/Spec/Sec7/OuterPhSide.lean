/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterPhConst
import InteractingSLE.Spec.Sec7.OuterInSide

/-!
# Outer-pocket side phases: bounded-sector selection and shared-side anchors

PROVE-R7-OUTERPHASE. Aux. 122 selects the phase for outer pockets when both
weights lie in `(-2, k - 6)`, just as for contained pockets. For arbitrary
weights the retained phase means give continuity; a shared-side anchor is
still needed. These are local conditional helpers, not a proof of
`OuterIn.R7OuterPhaseSideRemaining` or a producer of its phase word.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.OuterPh

open PocketTraversal Lemma71C PocketStop PhaseSide Hsd
open PocketWordAssembly PocketSeedOpen PocketCoupling PocketJordan HOuter

section Test

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {k rL rR : ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ} {δ : ℝ≥0 → Ω → ℝ}
  {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}

/-- For arbitrary seed weights, a shared-side zero visit and the retained
phase means supply the three parts of the unchanged two-seed side input. -/
theorem twoSeedPhaseSideAt_of_means_anchor (hk : 4 < k) (hA : MeasurableSet A)
    (hPA : P A ≠ 0)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hPhase : ∀ q, PocketStopSide.PocketStopPhaseSideLimit k
      (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
      (activeCompl A γ c q) (δ q) q)
    (hM : TwoSeedPhaseMeans k rL rR P A γ δ)
    (hAnchor : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0) :
    TwoSeedPhaseSideAt k rL rR P A γ c h₀ u :=
  ⟨a, δ, hPhase,
    Eventually.of_forall (continuousOn_of_twoSeedPhaseMeans hk hA hPA hγ hM), hAnchor⟩

/-- Countable shared-side comparisons are intersected before choosing the
realized original-time visit; their relative times may be random. -/
theorem twoSeedPhaseSideAt_of_means_countable_anchors {ι : Type*} [Countable ι]
    (hk : 4 < k) (hA : MeasurableSet A) (hPA : P A ≠ 0)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hPhase : ∀ q, PocketStopSide.PocketStopPhaseSideLimit k
      (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
      (activeCompl A γ c q) (δ q) q)
    (hM : TwoSeedPhaseMeans k rL rR P A γ δ)
    {s : ι → Ω → ℝ≥0} {E : ι → Set Ω}
    (hZero : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0)
    (hVisits : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i) :
    TwoSeedPhaseSideAt k rL rR P A γ c h₀ u :=
  twoSeedPhaseSideAt_of_means_anchor hk hA hPA hγ hPhase hM
    (PocketStopSide.ae_phase_anchor_of_countable_visits hZero hVisits)

end Test

section Input

/-- Aux. 122's bounded sector applies to an outer pocket's driven traversal.
The phase-word and retained-kernel producer is kept as the named input. -/
theorem twoSeedPhaseSideInput_of_means_outer {Ω : Type*} {k rL rR : ℝ}
    (hk : 4 < k) (hrL : -2 < rL) (hrL' : rL < k - 6)
    (hrR : -2 < rR) (hrR' : rR < k - 6)
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (h𝓦 : 𝓦 ≤ mΩ)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W : Ω → ℝ → ℝ}
    (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseMeansInput k rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseSideInput k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, hat⟩ := h A hA hAG hPA ψ hJ hPt
  refine ⟨n, hn, twoSeedPhaseSideAt_of_means hk hrL hrL' hrR hrR'
    (h𝓦 _ hA) hPA.ne' (fun ω hω => ?_) hat⟩
  exact ⟨((hcfg ω (hAG hω)).props (hJ ω hω)).1,
    ((hcfg ω (hAG hω)).props (hJ ω hω)).2.1⟩

/-- The same bounded-sector phase selection for an outer pocket opening at
the flow seed. No boundary-intersection trace theorem is used. -/
theorem twoSeedPhaseSideInputInf_of_means_outer {Ω : Type*} {k rL rR : ℝ}
    (hk : 4 < k) (hrL : -2 < rL) (hrL' : rL < k - 6)
    (hrR : -2 < rR) (hrR' : rR < k - 6)
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (h𝓦 : 𝓦 ≤ mΩ)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W : Ω → ℝ → ℝ}
    (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseMeansInputInf k rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseSideInputInf k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, hat⟩ := h A hA hAG hPA ψ hJ hPt
  refine ⟨n, hn, twoSeedPhaseSideAt_of_means hk hrL hrL' hrR hrR'
    (h𝓦 _ hA) hPA.ne' (fun ω hω => ?_) hat⟩
  exact ⟨((hcfg ω (hAG hω)).props (hJ ω hω)).1,
    ((hcfg ω (hAG hω)).props (hJ ω hω)).2.1⟩

end Input

end InteractingSLE.Sec7.OuterPh
