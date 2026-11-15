/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActVisit
import InteractingSLE.Spec.Sec5.MarkovOther
import InteractingSLE.Spec.Sec4.Aux25Path
import InteractingSLE.Spec.Restart.Kernel

/-!
# Interior visits from a protected conditional first-exit law

PROVE-POCKET-SIDEIN. The named `hRestart` is an ordinary disintegrating
conditional trace law, in the same form as the general restart consumers.
Only a protected positive segment is used. `hContinuation` identifies that
segment with the actual original curve in the pocket. No conditional law is
taken after selecting a future-dependent inner pocket or successful visit.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Sec5.MarkovOther Restart

/-- A physical visit to an open pocket has a rational original-time witness.
This also applies to an open subpocket avoiding certified closed frontiers. -/
theorem exists_rat_of_open_pocket_visit {η : ℝ → ℂ} {C : Set ℂ} {τ σ : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hC : IsOpen C) (hτ : 0 ≤ τ)
    (hvisit : (Sec6.visitSet η C τ σ).Nonempty) :
    ∃ r : ℚ, (r : ℝ) ∈ Sec6.visitSet η C τ σ := by
  have hη' : ContinuousOn η (Ioo τ σ) :=
    hη.mono (fun t ht => hτ.trans ht.1.le)
  exact Rat.denseRange_cast.exists_mem_open
    (hη'.isOpen_inter_preimage isOpen_Ioo hC) hvisit

/-- A protected positive part of the conditional trace contains an interior
point, at a rational own time. This follows from strict Loewner growth. -/
theorem ae_rat_interior_of_protected_traceLaw {S : Type*} [MeasurableSpace S]
    {Q : Measure S} {κ : ℝ} {c : BoundaryWord} {γ : S → ℝ≥0 → ℂ}
    {ζ : S → ℝ≥0∞} {L : S → ℝ≥0}
    (hLaw : IsFlowLineTraceLaw κ c Q γ ζ)
    (hProtected : ∀ᵐ s ∂Q, 0 < L s ∧ (L s : ℝ≥0∞) < ζ s) :
    ∀ᵐ s ∂Q, ∃ r : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < L s ∧
      γ s (Aux25.ratTime r) ∈ H := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := hLaw
  filter_upwards [hev.2.2.2.2, htr, hProtected] with s hp ht hL
  obtain ⟨r, hr₀, hrL, hrH⟩ := Aux25.exists_rat_mem_H_btwn ht
    hp.isForcePath.continuousOn_w hp.isForcePath.w_zero hL.1 hL.2
  exact ⟨r, hr₀, hrL, hrH⟩

/-- General-restart-compatible source input for an actual pocket visit.
The kernel disintegrates the complete retained datum and restart variable on
M. A chart continuation is used only up to the protected stop L, before ζ.
The resulting event is measurable via the countable own-time witnesses. -/
theorem ae_pocket_visit_of_conditional_restart {Ω D S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {κ : ℝ}
    {M : Set Ω} (hM : MeasurableSet M) {β : Ω → D} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel D S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {word : D → BoundaryWord} {γS : S → ℝ≥0 → ℂ} {ζ : S → ℝ≥0∞} {L : S → ℝ≥0}
    (hγS : ∀ t, Measurable fun s => γS s t) (hL : Measurable L)
    (hRestart : ∀ᵐ d ∂(P.restrict M).map β, IsFlowLineTraceLaw κ (word d) (K d) γS ζ)
    (hProtected : ∀ᵐ d ∂(P.restrict M).map β,
      ∀ᵐ s ∂K d, 0 < L s ∧ (L s : ℝ≥0∞) < ζ s)
    {η : Ω → ℝ → ℂ} {C : Ω → Set ℂ} {τ σ : Ω → ℝ}
    {U : D → Set ℂ} {ψ : D → ℂ → ℂ}
    (hψ : ∀ d, MapsTo (ψ d) H (U d))
    (hUC : ∀ ω ∈ M, U (β ω) ⊆ C ω)
    (hContinuation : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → t < L (X ω) →
      ∃ r ∈ Ioo (τ ω) (σ ω), η ω r = ψ (β ω) (γS (X ω) t)) :
    ∀ᵐ ω ∂P, ω ∈ M → (Sec6.visitSet (η ω) (C ω) (τ ω) (σ ω)).Nonempty := by
  let E : Set S := {s | ∃ r : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < L s ∧
    γS s (Aux25.ratTime r) ∈ H}
  have hE : MeasurableSet E := by
    simp only [E, ofPred_exists]
    exact MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
      ((measurableSet_lt measurable_const hL.coe_nnreal_real).inter
        (hγS (Aux25.ratTime r) QuantumZipper.isOpen_H.measurableSet))
  have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂K d, s ∈ E := by
    filter_upwards [hRestart, hProtected] with d hd hp
    exact ae_rat_interior_of_protected_traceLaw hd hp
  have hactual := Restart.ae_mem_of_compProd_eq hM hβ hX hlaw hE hKE
  filter_upwards [hactual, hContinuation] with ω hω hc hωM
  obtain ⟨r, hr₀, hrL, hrH⟩ := hω hωM
  have ht₀ : 0 < Aux25.ratTime r := Real.toNNReal_pos.2 hr₀
  have htL : Aux25.ratTime r < L (X ω) := by
    exact (Real.toNNReal_lt_iff_lt_coe (by positivity)).2 hrL
  obtain ⟨t, ht, he⟩ := hc hωM _ ht₀ htL
  refine ⟨t, ht, ?_⟩
  rw [he]
  exact hUC ω hωM (hψ _ hrH)

end InteractingSLE.Sec7.PocketStopSide
