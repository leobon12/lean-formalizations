/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstRetainedLanding

/-! # Landing for the glued retained-chart geometry at its physical hitting time -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData Aux61Restart
open WangWu (negInv)

/-- A compact raw record of the retained counterflow trace; clipping only
changes values below the half-plane and preserves the filling. -/
def counterflowRecord (β : ℝ → ℂ) (s : ℝ) : Set ℂ :=
  (fun t => clipH (β t)) '' Icc 0 s

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
  {W : X → ℝ → ℝ} {β η : X → ℝ → ℂ} {s r : ℝ} {b : X → ℂ}

/-- On the source's physical restart data, every positive-time sample has a
free real seed collar. This is the pointwise input to rational localization. -/
theorem exists_glued_seed_gap
    (hs : IsRestartSpec E c ρ T) (hs0 : 0 ≤ s)
    (hβ : ∀ x ∈ E, IsLoewnerTrace (W x) (β x))
    (hη : ∀ x ∈ E, ContinuousOn (η x) (Icc 0 r))
    (hηH : ∀ x ∈ E, MapsTo (η x) (Icc 0 r) Hbar)
    (hb : ∀ x ∈ E, b x ∈ retainedDomain (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r)
    (hdom : ∀ x ∈ E, ((c x).dom : Set ℂ) =
      restartComponent (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r (b x))
    (hT : T = hitTime ρ (fun x => (H \ negInv '' QuantumZipper.fwdHull (W x) s)ᶜ)) :
    ∀ x ∈ E, 0 < T x → ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary (counterflowRecord (β x) s) := by
  intro x hx hT0
  have hF := boundedInverse_spec_of_traces (hβ x hx) hs0 (hη x hx) (hηH x hx)
    (hb x hx) (hs.conf x hx) (hdom x hx)
  have hstart : ρ x 0 ∈ H \ negInv '' QuantumZipper.fwdHull (W x) s := by
    have hn := notMem_of_lt_hitTime (ρ := ρ)
      (F := fun x => (H \ negInv '' QuantumZipper.fwdHull (W x) s)ᶜ)
      (x := x) (u := 0) (by simpa only [← hT, ENNReal.coe_zero] using hT0)
    exact not_not.1 hn
  have hfill : fillH (counterflowRecord (β x) s) = QuantumZipper.fwdHull (W x) s :=
    fillH_clipped_trace (hβ x hx) hs0
  apply exists_seed_gap_of_retainedGeometry hs hx hT0
    (isCompact_Icc.image_of_continuousOn (continuous_clipH.comp_continuousOn
      ((hβ x hx).2.1.mono Icc_subset_Ici_self)))
    (by rintro _ ⟨t, -, rfl⟩; exact clipH_mem_Hbar _) _ hF.1 hF.2.1
  change ρ x 0 ∈ H \ negInv '' fillH (counterflowRecord (β x) s)
  rwa [hfill]

/-- The source's physical first hitting time and retained chart satisfy
selected-access landing on every bounded window with a uniform free seed
collar. The inverse extension and the terminal contact are proved here. -/
theorem hasAccessLanding_glued_restart
    (hs : IsRestartSpec E c ρ T) (hs0 : 0 ≤ s)
    (hβ : ∀ x ∈ E, IsLoewnerTrace (W x) (β x))
    (hη : ∀ x ∈ E, ContinuousOn (η x) (Icc 0 r))
    (hηH : ∀ x ∈ E, MapsTo (η x) (Icc 0 r) Hbar)
    (hb : ∀ x ∈ E, b x ∈ retainedDomain (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r)
    (hdom : ∀ x ∈ E, ((c x).dom : Set ℂ) =
      restartComponent (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r (b x))
    (hT : T = hitTime ρ (fun x => (H \ negInv '' QuantumZipper.fwdHull (W x) s)ᶜ))
    {U : Set ℂ} (hUb : Bornology.IsBounded U) (δ : ℝ)
    (hseed : ∀ x ∈ E, ∀ a : ℝ, |a| < δ →
      boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary (counterflowRecord (β x) s)) :
    HasAccessLanding E c ρ T (seedExitWindow U δ) := by
  let K : X → Set ℂ := fun x => counterflowRecord (β x) s
  have hfill : ∀ x ∈ E, fillH (K x) = QuantumZipper.fwdHull (W x) s :=
    fun x hx => fillH_clipped_trace (hβ x hx) hs0
  apply hasAccessLanding_of_retainedGeometry hs hUb δ K (fun x => η x '' Icc 0 r) b
  · intro x hx
    exact isCompact_Icc.image_of_continuousOn
      (continuous_clipH.comp_continuousOn ((hβ x hx).2.1.mono Icc_subset_Ici_self))
  · intro x hx
    rintro _ ⟨t, -, rfl⟩
    exact clipH_mem_Hbar _
  · intro x hx
    rw [hfill x hx]
    simpa only [restartComponent, retainedDomain, ← sdiff_sdiff] using hdom x hx
  · intro x hx
    exact boundedInverse_spec_of_traces (hβ x hx) hs0 (hη x hx) (hηH x hx)
      (hb x hx) (hs.conf x hx) (hdom x hx)
  · exact hseed
  · intro x hx _ hfin
    have ho : IsOpen (H \ negInv '' QuantumZipper.fwdHull (W x) s) := by
      rw [← hfill x hx, WangWu.H_diff_image_negInv]
      exact WangWu.isOpen_image_negInv (isOpen_H_diff_fillH
        (isCompact_Icc.image_of_continuousOn
          (continuous_clipH.comp_continuousOn ((hβ x hx).2.1.mono Icc_subset_Ici_self))).isBounded)
          sdiff_subset
    rw [hfill x hx]
    exact mem_at_finite_hitTime (hs.contρ x hx) ho.isClosed_compl (congrFun hT x) hfin

end InteractingSLE.Sec5.Aux61GInst
