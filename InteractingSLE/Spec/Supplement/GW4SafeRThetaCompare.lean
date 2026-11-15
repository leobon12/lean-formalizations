/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRThetaInversion
import InteractingSLE.Spec.Supplement.GW4SafeREtaPhysical
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Supplement.GW4SafeRDeltaLift

/-! # GW4: component and ambient means with their actual inherited lifts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField GW4Traverse Sec7.Aux119Heights Sec7.SideC12
open Sec7.PhaseSel
open WangWu (negInv)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The exact ambient/component mean comparison. The two source
inversions contribute the fixed `2πχ` lattice term in addition to the
inherited chart lift. -/
theorem harmRep_component_ambient {κ : ℝ} (hκ : 0 < κ)
    {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {A : Set ℂ} (hAo : IsOpen (H \ A))
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (H \ A))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    let T := GW4Rel.invField κ (Chart.chartTransport hc 1 0 (chiC κ) M) -
      smoothDist upperHalfPlaneOpens u
    ∀ y ∈ H \ CLoc.chartSet c A,
      harmRep T (H \ CLoc.chartSet c A) y + u y =
        harmRep (GW4Rel.invField κ M) (negInv '' (H \ A)) (relInvC c y) +
          chiC (16 / κ) * ((infinitySourceChart.trans c).trans infinitySourceChart).2.2
            (relInvC c y) + 2 * Real.pi * chiC (16 / κ) := by
  change ∀ y ∈ H \ CLoc.chartSet c A, _
  intro y hy
  have hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  have hyH := hy.1
  have hRyH := WangWu.negInv_mem_H hyH
  have hzA : c.2.1 (negInv y) ∈ H \ A := by
    rw [CLoc.H_diff_chartSet] at hy
    exact hy.2.2
  have hRz : negInv (relInvC c y) = c.2.1 (negInv y) := by
    change negInv (negInv (c.2.1 (negInv y))) = _
    exact WangWu.negInv_negInv _
  have hzI : relInvC c y ∈ negInv '' (H \ A) :=
    ⟨c.2.1 (negInv y), hzA, rfl⟩
  have hF : c.1 (negInv (relInvC c y)) = negInv y := by
    rw [hRz, hch.2.2.2.1.2 hRyH]
  have hL : infinitySourceChart.2.2 (relInvC c y) =
      -(2 * Real.pi) - infinitySourceChart.2.2 (c.2.1 (negInv y)) := by
    exact GW2JointKernel.infinitySourceChart_lift_negInv hzA.1
  have hMean := harmRep_component_invField hκ hch hCo hCH hAo hM hu hy
  have hAmb := harmRep_invField hκ hAo sdiff_subset hM hzI
  simp only at hMean hAmb
  rw [hMean, hAmb]
  simp only [sourceShift, add_zero]
  rw [hRz, Sec4.chiC_sixteen_div hκ]
  change _ = -(harmRep M (H \ A) (c.2.1 (negInv y))) +
    (-(Real.pi * chiC κ) + -chiC κ * infinitySourceChart.2.2 (c.2.1 (negInv y))) +
    -chiC κ * (infinitySourceChart.2.2 (c.1 (negInv (relInvC c y))) +
      (c.2.2 (negInv (relInvC c y)) + infinitySourceChart.2.2 (relInvC c y))) +
    2 * Real.pi * -chiC κ
  rw [hF, hRz, hL]
  ring

/-- After a relative Loewner stage, the only additional term in the
ambient comparison is the difference of the actual inherited logarithms,
with the fixed two-inversion correction retained. -/
theorem correctedMean_component_ambient {κ : ℝ} (hκ : 0 < κ)
    {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {A : Set ℂ} (hAo : IsOpen (H \ A))
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (H \ A))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (Wrel Wamb : ℝ → ℝ) (q t : ℝ) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    let T := GW4Rel.invField κ (Chart.chartTransport hc 1 0 (chiC κ) M) -
      smoothDist upperHalfPlaneOpens u
    ∀ y ∈ H \ CLoc.chartSet c A,
      harmRep T (H \ CLoc.chartSet c A) y + u y +
          chiC (16 / κ) * (QuantumZipper.logDerivFwd Wrel q y).im =
        harmRep (GW4Rel.invField κ M) (negInv '' (H \ A)) (relInvC c y) +
          chiC (16 / κ) * (QuantumZipper.logDerivFwd Wamb t (relInvC c y)).im +
          chiC (16 / κ) * ((componentAmbientChart c Wrel q).2.2 (relInvC c y) -
            (QuantumZipper.logDerivFwd Wamb t (relInvC c y)).im) +
          2 * Real.pi * chiC (16 / κ) := by
  change ∀ y ∈ H \ CLoc.chartSet c A, _
  intro y hy
  have he := harmRep_component_ambient hκ hch hCo hCH hAo hM hu y hy
  have hBase : ((infinitySourceChart.trans c).trans infinitySourceChart).1 (relInvC c y) = y := by
    change negInv (c.1 (negInv (negInv (c.2.1 (negInv y)))) ) = y
    rw [WangWu.negInv_negInv, hch.2.2.2.1.2 (WangWu.negInv_mem_H hy.1), WangWu.negInv_negInv]
  simp only [componentAmbientChart, Chart.loewner]
  rw [hBase, he]
  ring

/-- The integer supplied by R.5 is shifted by the two source inversions
when expressed in the phase lattice used by RepD. -/
theorem component_phase_offset (k : ℝ) (n : ℤ) :
    chiC k * (2 * Real.pi * (n : ℝ)) + 2 * Real.pi * chiC k =
      ((-n - 1 : ℤ) : ℝ) * phaseStep k := by
  simp only [phaseStep, Int.cast_sub, Int.cast_neg, Int.cast_one]
  ring

end InteractingSLE.Theorem14.GW4Fix
