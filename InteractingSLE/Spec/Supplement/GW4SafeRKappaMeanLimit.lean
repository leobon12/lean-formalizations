/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaPhase

/-! # GW4: transport an ambient boundary limit with the exact lattice phase -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H chiC logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField GW4Rel GW4Traverse Sec7.Aux119Heights Sec7.PhaseSel
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- Every supplied ambient prime-end height transports to the actual
component mean with the correct lattice offset. The mean identity is the
proved physical transport formula; the two boundary limits are local
inputs, not a representation or constancy premise. -/
theorem tendsto_correctedMean_component_of_ambient {κ : ℝ} (hκ : 0 < κ)
    {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {A : Set ℂ} (hAo : IsOpen (H \ A))
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (H \ A))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    {Wrel Wamb : ℝ → ℝ} {q t : ℝ} {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : ∀ᶠ a in l, f a ∈ H \ CLoc.chartSet c A) {n : ℤ} {h : ℝ}
    (hAmbientHeight : Tendsto (fun a =>
      harmRep (invField κ M) (WangWu.negInv '' (H \ A)) (relInvC c (f a)) +
        chiC (16 / κ) * (logDerivFwd Wamb t (relInvC c (f a))).im) l (𝓝 h))
    (hWinding : Tendsto (fun a =>
      (componentAmbientChart c Wrel q).2.2 (relInvC c (f a)) -
        (logDerivFwd Wamb t (relInvC c (f a))).im) l (𝓝 (2 * Real.pi * n))) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    let T := invField κ (Chart.chartTransport hc 1 0 (chiC κ) M) -
      smoothDist upperHalfPlaneOpens u
    Tendsto (fun a => harmRep T (H \ CLoc.chartSet c A) (f a) + u (f a) +
      chiC (16 / κ) * (logDerivFwd Wrel q (f a)).im) l
      (𝓝 (h + ((-n - 1 : ℤ) : ℝ) * phaseStep (16 / κ))) := by
  have hlim := hAmbientHeight.add ((hWinding.const_mul (chiC (16 / κ))).add_const
    (2 * Real.pi * chiC (16 / κ)))
  rw [component_phase_offset] at hlim
  refine hlim.congr' (hf.mono fun a ha => ?_)
  simpa only [add_assoc] using
    (correctedMean_component_ambient hκ hch hCo hCH hAo hM hu Wrel Wamb q t (f a) ha).symm

end InteractingSLE.Theorem14.GW4Fix
