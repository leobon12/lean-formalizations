/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAccessFields

/-! # Selected-access landing for the actual first contact on its regular event -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61FibData Aux61GInst Aux61Restart
open WangWu (negInv)

/-- The first-contact identity is needed only on the regular restart
event. Every bounded subwindow of a free seed window has selected-access
landing, including windows chosen from the fixed countable buffered family. -/
theorem hasAccessLanding_glued_subwindow {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {W : X → ℝ → ℝ} {β η : X → ℝ → ℂ}
    {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : ∀ x ∈ E, IsLoewnerTrace (W x) (β x))
    (hη : ∀ x ∈ E, ContinuousOn (η x) (Icc 0 r))
    (hηH : ∀ x ∈ E, MapsTo (η x) (Icc 0 r) Hbar) {b : X → ℂ}
    (hb : ∀ x ∈ E, b x ∈ retainedDomain (negInv '' fwdHull (W x) s) (η x) r)
    (hdom : ∀ x ∈ E, ((c x).dom : Set ℂ) =
      restartComponent (negInv '' fwdHull (W x) s) (η x) r (b x))
    (hT : ∀ x ∈ E, T x = hitTime ρ (fun x => (H \ negInv '' fwdHull (W x) s)ᶜ) x)
    {U V : Set ℂ} (hUb : Bornology.IsBounded U) {δ : ℝ}
    (hVU : V ⊆ seedExitWindow U δ)
    (hseed : ∀ x ∈ E, ∀ a : ℝ, |a| < δ →
      boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary (counterflowRecord (β x) s)) :
    HasAccessLanding E c ρ T V := by
  apply hasAccessLanding_mono_window hVU
  let K : X → Set ℂ := fun x => counterflowRecord (β x) s
  have hfill : ∀ x ∈ E, fillH (K x) = fwdHull (W x) s :=
    fun x hx => fillH_clipped_trace (hβ x hx) hs0
  have hK : ∀ x ∈ E, IsCompact (K x) := fun x hx =>
    isCompact_Icc.image_of_continuousOn
      (continuous_clipH.comp_continuousOn ((hβ x hx).2.1.mono Icc_subset_Ici_self))
  apply hasAccessLanding_of_retainedGeometry hs hUb δ K (fun x => η x '' Icc 0 r) b hK
  · intro x _
    rintro _ ⟨t, _, rfl⟩
    exact clipH_mem_Hbar _
  · intro x hx
    rw [hfill x hx]
    simpa only [restartComponent, retainedDomain, ← sdiff_sdiff] using hdom x hx
  · intro x hx
    exact boundedInverse_spec_of_traces (hβ x hx) hs0 (hη x hx) (hηH x hx)
      (hb x hx) (hs.conf x hx) (hdom x hx)
  · exact hseed
  · intro x hx _ hfin
    have hopen : IsOpen (H \ negInv '' fwdHull (W x) s) := by
      rw [← hfill x hx, WangWu.H_diff_image_negInv]
      exact WangWu.isOpen_image_negInv (isOpen_H_diff_fillH (hK x hx).isBounded) sdiff_subset
    rw [hfill x hx]
    exact mem_at_finite_hitTime (hs.contρ x hx) hopen.isClosed_compl (hT x hx) hfin

/-- A window whose real points all lie in the free seed interval is an
admissible subwindow; its nonreal buffer is unrestricted. -/
theorem subset_seedExitWindow_of_real_gap {U V : Set ℂ} {δ : ℝ} (hVU : V ⊆ U)
    (hreal : ∀ z ∈ V, z.im = 0 → |z.re| < δ) : V ⊆ seedExitWindow U δ := by
  intro z hz
  exact ⟨hVU hz, fun h => (not_le.2 (hreal z hz h.1)) h.2⟩

end InteractingSLE.Sec5.Aux61SlitW
