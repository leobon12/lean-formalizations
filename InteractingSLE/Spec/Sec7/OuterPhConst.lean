/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSideR7

/-!
# Outer-pocket phase constancy without upper weight bounds

PROVE-R7-OUTERPHASE, follow-up 5 §3.2. The retained phase means imply constancy
on the whole positive relative lifetime. This step uses no seed-weight bound:
freeze the coordinates at a pre-lifetime stop, apply the existing quotient and
lattice argument, and exhaust the lifetime by the coordinate announcing times.
The phase word and the Gaussian-kernel hypothesis remain separate inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.OuterPh

open MartChar PocketTraversal PhaseSel PocketMartLife Lemma71C PhaseSide Hsd

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {k : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
  {d : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0}

/-- The common lattice phase is constant up to any stop strictly before the
lifetime, for arbitrary weights. Only the continuity part of the retained
phase means is used after stopping. -/
theorem phase_eq_stop [IsFiniteMeasure P] (hk : 4 < k)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < T ω →
      ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
    (ω : Ω) {s t : ℝ≥0} (hs : 0 < s) (ht : 0 < t)
    (hsσ : s ≤ σ ω) (htσ : t ≤ σ ω) : d s ω = d t ω := by
  have hk0 : 0 < k := lt_trans (by norm_num) hk
  have hWc' := continuous_stopW hWc hσT
  let W' := stopW W σ
  let d' := stopD d σ
  let U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ =>
    meanExt k (shiftL k ρL (d' t ω)) (shiftR k ρR (d' t ω))
      (W' t ω) (fun i => geomLW W' xL i t ω) (fun j => geomRW W' xR j t ω) ξ + d' t ω
  have hU : ∀ ω t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => geomLW W' xL i t ω - W' t ω)
        (fun j => geomRW W' xR j t ω - W' t ω) (d' t ω))
      (forceJumpSet (fun i => geomLW W' xL i t ω - W' t ω)
        (fun j => geomRW W' xR j t ω - W' t ω)) (U ω t) := fun ω t =>
    isBoundedHarmonicExtension_unshift hk0
      (sub_nonpos.2 (geomLW_le hWc' xL ω t 0))
      (sub_nonneg.2 (le_geomRW hWc' xR ω t 0))
      (isBoundedHarmonicExtension_meanExt k _ _ (W' t ω) _ _)
  have he := PhaseSelFull.phase_eq_of_pos_before (L := (σ ω : ℝ≥0∞))
    (phaseStep_ne_zero hk) (hWc' ω)
    (fun i => (isForcePath_geomLW hWc' xL ω i).1)
    (fun j => (isForcePath_geomRW hWc' xR ω j).1)
    (fun t i => geomLW_le hWc' xL ω t i)
    (fun t j => le_geomRW hWc' xR ω t j)
    (antitone_geomLW hWc' xL ω 0) (monotone_geomRW hWc' xR ω 0)
    (isForcePath_geomLW hWc' xL ω 0).2.2.2
    (fun t ht htσ => by
      have htσ' : t ≤ σ ω := ENNReal.coe_le_coe.1 htσ
      simpa only [d', stopD, htσ', ↓reduceIte] using
        hd t ω ht (lt_of_le_of_lt htσ (hσT ω)))
    (hU ω) ((hasPhaseMeans_stop hk0 hWc hM hσ hσT U hU).2 ω)
    hs ht (ENNReal.coe_le_coe.2 hsσ) (ENNReal.coe_le_coe.2 htσ)
  simpa only [d', stopD, hsσ, htσ, ↓reduceIte] using he

end Stop

section Curve

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {k : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
  {xR : Ω → Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ}

/-- Constancy on the entire positive relative lifetime, with no upper or
lower weight bounds and no measurability assumption on the phase. -/
theorem phase_eq_of_hasPhaseMeans [IsFiniteMeasure P] [𝓕.IsRightContinuous]
    (hk : 4 < k) (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL)
    (hxRm : Measurable[𝓕 0] xR)
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) →
      ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t)
      xL xR d (fun ω => capLife (γ ω))) :
    ∀ ω (s t : ℝ≥0), 0 < s → 0 < t → (s : ℝ≥0∞) < capLife (γ ω) →
      (t : ℝ≥0∞) < capLife (γ ω) → d s ω = d t ω := by
  obtain ⟨τ, hτ, hτT, -, hτex, -, -⟩ := exists_announcing_coords hγ hunb hpre hxLm hxRm
  intro ω s t hs ht hsT htT
  obtain ⟨m, hm⟩ := hτex ω (max s t) (by
    change ((max s t : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)
    rw [ENNReal.coe_max]
    exact max_lt hsT htT)
  exact phase_eq_stop hk (fun ω => (hγ ω).segDriver_spec.2.1) hd hM
    (hτ m) (hτT m) ω hs ht ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm)

end Curve

section Test

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {k rL rR : ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ} {δ : ℝ≥0 → Ω → ℝ}

/-- The phase of a two-seed test is constant pathwise on its positive
lifetime, for arbitrary seed weights. -/
theorem phase_eq_of_twoSeedPhaseMeans (hk : 4 < k) (hA : MeasurableSet A)
    (hPA : P A ≠ 0)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hM : TwoSeedPhaseMeans k rL rR P A γ δ) :
    ∀ ω ∈ A, ∀ s t : ℝ≥0, 0 < s → 0 < t → (s : ℝ≥0∞) < capLife (γ ω) →
      (t : ℝ≥0∞) < capLife (γ ω) → δ s ω = δ t ω := by
  obtain ⟨hlat, 𝓕, h𝓕, hpre, hM⟩ := hM
  have := h𝓕
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA hPA
  intro ω hω s t hs ht hsT htT
  exact phase_eq_of_hasPhaseMeans (P := condSub P A) (𝓕 := 𝓕) hk
    (fun ω => (hγ ω ω.2).1) (fun ω => (hγ ω ω.2).2) hpre
    measurable_const measurable_const (fun t ω ht htT => hlat ω ω.2 t ht htT)
    hM ⟨ω, hω⟩ s t hs ht hsT htT

/-- The continuity needed in `Hsd.TwoSeedPhaseSideAt` follows from the
retained phase means for every weight pair. -/
theorem continuousOn_of_twoSeedPhaseMeans (hk : 4 < k) (hA : MeasurableSet A)
    (hPA : P A ≠ 0)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hM : TwoSeedPhaseMeans k rL rR P A γ δ) :
    ∀ ω ∈ A, ContinuousOn (fun t => δ t ω)
      {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)} := by
  intro ω hω t ht
  have hc : ContinuousOn (fun s => δ s ω)
      {s : ℝ≥0 | 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω)} :=
    continuousOn_const.congr fun s hs =>
      phase_eq_of_twoSeedPhaseMeans hk hA hPA hγ hM ω hω s t hs.1 ht.1 hs.2 ht.2
  exact hc t ht

end Test

end InteractingSLE.Sec7.OuterPh
