/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstChartExtension
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLanding

/-! # The actual retained chart has a bounded continuous inverse extension -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GInst
open WangWu (negInv)
open Aux61Restart Aux61FibData

/-- The bounded physical inverse, with the canonical boundary extension. -/
def boundedInverse (c : Chart) : ℂ → ℂ := extendFrom H (cayley ∘ c.2.1)

/-- Clipping a trace to the closed half-plane preserves its filling. -/
theorem fillH_clipped_trace {W : ℝ → ℝ} {β : ℝ → ℂ}
    (hβ : IsLoewnerTrace W β) {s : ℝ} (hs : 0 ≤ s) :
    fillH ((fun t => clipH (β t)) '' Icc 0 s) = QuantumZipper.fwdHull W s := by
  rw [hβ.2.2 s hs]
  apply fillH_congr
  have hc : IsCompact ((fun t => clipH (β t)) '' Icc 0 s) :=
    isCompact_Icc.image_of_continuousOn
      (continuous_clipH.comp_continuousOn (hβ.2.1.mono Icc_subset_Ici_self))
  rw [hc.isClosed.closure_eq, (hβ.isCompact_image s).isClosed.closure_eq]
  rw [show (fun t => clipH (β t)) '' Icc 0 s = clipH '' (β '' Icc 0 s) from
    (image_image clipH β _).symm]
  exact image_clipH_inter_H _

/-- The source's retained counterflow and finite own prefix supply every
inverse-extension input of the selected-access landing argument. -/
theorem boundedInverse_spec_of_traces {W : ℝ → ℝ} {β η : ℝ → ℂ} {s r : ℝ}
    (hβ : IsLoewnerTrace W β) (hs : 0 ≤ s)
    (hη : ContinuousOn η (Icc 0 r)) (hηH : MapsTo η (Icc 0 r) Hbar)
    {b : ℂ} (hb : b ∈ retainedDomain (negInv '' QuantumZipper.fwdHull W s) η r)
    {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = restartComponent (negInv '' QuantumZipper.fwdHull W s) η r b) :
    EqOn (boundedInverse c) (cayley ∘ c.2.1) H ∧ ContinuousOn (boundedInverse c) Hbar ∧
      DifferentiableOn ℂ (boundedInverse c) H ∧ InjOn (boundedInverse c) H ∧
      ∀ z : ℂ, z.im = 0 → boundedInverse c z ∉ boundedInverse c '' H := by
  let K := (fun t => clipH (β t)) '' Icc 0 s
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn
    (continuous_clipH.comp_continuousOn (hβ.2.1.mono Icc_subset_Ici_self))
  have hKH : K ⊆ Hbar := by rintro _ ⟨t, -, rfl⟩; exact clipH_mem_Hbar _
  have hKu : QuantumZipper.CA.Topo.ULC K := ulc_image_Icc (continuous_clipH.comp_continuousOn
    (hβ.2.1.mono Icc_subset_Ici_self))
  have hfill : fillH K = QuantumZipper.fwdHull W s := fillH_clipped_trace hβ hs
  have hb' : b ∈ (H \ negInv '' fillH K) \ η '' Icc 0 r := by
    rw [hfill]
    simpa only [retainedDomain, ← sdiff_sdiff] using hb
  have hdom' : (c.dom : Set ℂ) = connectedComponentIn
      ((H \ negInv '' fillH K) \ η '' Icc 0 r) b := by
    rw [hfill]
    simpa only [restartComponent, retainedDomain, ← sdiff_sdiff] using hdom
  obtain ⟨F, hFeq, hFc, hFd, hFi, hFR⟩ := exists_retained_inverse_extension hKc hKH hKu
    (isCompact_Icc.image_of_continuousOn hη) hηH.image_subset (ulc_image_Icc hη) hb' hc hdom'
  have he : EqOn (boundedInverse c) F Hbar := by
    intro z hz
    apply extendFrom_eq (closure_H ▸ hz)
    refine ((hFc z hz).mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).congr' ?_
    have hev : ∀ᶠ w : ℂ in 𝓝[H] z, w ∈ H := self_mem_nhdsWithin
    exact hev.mono fun w hw => hFeq hw
  have heH : EqOn (boundedInverse c) F H := he.mono QuantumZipper.H_subset_Hbar
  refine ⟨fun z hz => (heH hz).trans (hFeq hz), hFc.congr he, hFd.congr heH, ?_, ?_⟩
  · intro z hz w hw heq
    apply hFi hz hw
    rwa [← heH hz, ← heH hw]
  · intro z hz0 ⟨w, hw, hwz⟩
    have hzH : z ∈ Hbar := by change 0 ≤ z.im; rw [hz0]
    exact hFR z hz0 ⟨w, hw, by rw [← heH hw, ← he hzH]; exact hwz⟩

end InteractingSLE.Sec5.Aux61GInst
