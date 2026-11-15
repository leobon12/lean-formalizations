/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaMeanLimit

/-! # GW4: retain the selected phase through an actual reference collar -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H chiC logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField GW4Traverse Sec7.Aux119Heights
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The weighted phase, including its fixed inversion correction, passes
from a reference to the current chart along a zero-increment collar. This
keeps the already selected phase value rather than choosing another integer. -/
theorem tendsto_reference_weighted_phase {cur old : Chart} (hold : old.IsConformal)
    {A : ℂ → ℝ} {ξ x : ℂ} {χ c δ : ℝ}
    (hdom : ∀ᶠ y in 𝓝[H] ξ, cur.2.1 y ∈ old.dom)
    (htr : Tendsto (fun y => old.1 (cur.2.1 y)) (𝓝[H] ξ) (𝓝 x))
    (hLift : Tendsto (fun y => cur.2.2 (cur.2.1 y) - old.2.2 (cur.2.1 y))
      (𝓝[H] ξ) (𝓝 0))
    (hOld : Tendsto (fun y => χ * (old.2.2 (old.2.1 y) - A (old.2.1 y)) + c)
      (𝓝[H] x) (𝓝 δ)) :
    Tendsto (fun y => χ * (cur.2.2 (cur.2.1 y) - A (cur.2.1 y)) + c)
      (𝓝[H] ξ) (𝓝 δ) := by
  have htrH := tendsto_nhdsWithin_iff.2 ⟨htr, hdom.mono fun y hy => hold.fwd_mem hy⟩
  have h := (hLift.const_mul χ).add (hOld.comp htrH)
  simp only [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [hdom] with y hy
  simp only [Function.comp_apply, hold.inv_fwd hy]
  ring

/-- The exact actual component/ambient identity transports an ambient
height together with the selected weighted phase. Both source inversions
are retained in `hPhase`. -/
theorem tendsto_correctedMean_component_of_phased_ambient {κ : ℝ} (hκ : 0 < κ)
    {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {A : Set ℂ} (hAo : IsOpen (H \ A))
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (H \ A))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    {Wrel Wamb : ℝ → ℝ} {q t : ℝ} {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : ∀ᶠ a in l, f a ∈ H \ CLoc.chartSet c A) {h δ : ℝ}
    (hHeight : Tendsto (fun a =>
      harmRep (GW4Rel.invField κ M) (WangWu.negInv '' (H \ A)) (relInvC c (f a)) +
        chiC (16 / κ) * (logDerivFwd Wamb t (relInvC c (f a))).im) l (𝓝 h))
    (hPhase : Tendsto (fun a => chiC (16 / κ) *
      ((componentAmbientChart c Wrel q).2.2 (relInvC c (f a)) -
        (logDerivFwd Wamb t (relInvC c (f a))).im) +
        2 * Real.pi * chiC (16 / κ)) l (𝓝 δ)) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    let T := GW4Rel.invField κ (Chart.chartTransport hc 1 0 (chiC κ) M) -
      smoothDist upperHalfPlaneOpens u
    Tendsto (fun a => harmRep T (H \ CLoc.chartSet c A) (f a) + u (f a) +
      chiC (16 / κ) * (logDerivFwd Wrel q (f a)).im) l (𝓝 (h + δ)) := by
  refine (hHeight.add hPhase).congr' (hf.mono fun a ha => ?_)
  simpa only [add_assoc] using
    (correctedMean_component_ambient hκ hch hCo hCH hAo hM hu Wrel Wamb q t (f a) ha).symm

end InteractingSLE.Theorem14.GW4Fix
