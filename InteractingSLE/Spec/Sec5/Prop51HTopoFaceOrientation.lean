/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import InteractingSLE.Spec.Sec5.Prop51HTopoFace
import InteractingSLE.Foundations.OrientationWinding
import QuantumZipper.Proofs.Complex.HoloLog

/-!
# Winding orientation under the inverse counterflow chart

A univalent holomorphic map on the half-plane preserves the winding number of
every loop in the half-plane. The divided difference has a holomorphic logarithm,
so its contribution to the logarithmic increment of a loop is zero. This gives
the conformal orientation step without assuming any regularity of the physical
counterflow boundary.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open _root_.InteractingSLE.Orientation

/-- Holomorphic injective half-plane charts preserve all interior loop indices. -/
theorem windNum_comp_of_univalent_H {F : ℂ → ℂ}
    (hFd : DifferentiableOn ℂ F H) (hFi : InjOn F H)
    {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1)
    (hγH : MapsTo γ (Icc 0 1) H) {z : ℂ} (hz : z ∈ H)
    (hγz : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z) :
    windNum (F ∘ γ) (F z) = windNum γ z := by
  have hkd : DifferentiableOn ℂ (dslope F z) H :=
    (differentiableOn_dslope (QuantumZipper.isOpen_H.mem_nhds hz)).2 hFd
  have hk0 : ∀ w ∈ H, dslope F z w ≠ 0 := by
    intro w hw
    by_cases he : w = z
    · rw [he, dslope_same]
      exact QuantumZipper.CA.deriv_ne_zero_of_injOn QuantumZipper.isOpen_H hFd hFi hz
    · rw [dslope_of_ne _ he, slope_def_field]
      exact div_ne_zero (sub_ne_zero.2 (fun h => he (hFi hw hz h))) (sub_ne_zero.2 he)
  have hcomp : ∀ a ∉ H, ¬ IsBounded (connectedComponentIn Hᶜ a) := by
    intro a ha
    rw [compl_H, isPreconnected_lowerHalf.connectedComponentIn
      (show a.im ≤ 0 from not_lt.1 ha)]
    exact not_isBounded_lowerHalf
  obtain ⟨L, hLd, hLexp⟩ := QuantumZipper.CA.Homology.exists_holo_log
    QuantumZipper.isOpen_H convex_H.isPreconnected hcomp (dslope F z) hkd hk0
  obtain ⟨A, hAc, hAexp⟩ := Orientation.exists_lift hc hγz
  have hFAc : ContinuousOn (fun t => A t + L (γ t)) (Icc 0 1) :=
    hAc.add (hLd.continuousOn.comp hc hγH)
  have hFexp : ∀ t ∈ Icc (0 : ℝ) 1,
      exp (A t + L (γ t)) = (F ∘ γ) t - F z := by
    intro t ht
    rw [exp_add, hAexp t ht, hLexp (γ t) (hγH ht)]
    exact sub_smul_dslope F z (γ t)
  have hFc : ContinuousOn (F ∘ γ) (Icc 0 1) := hFd.continuousOn.comp hc hγH
  have hFz : ∀ t ∈ Icc (0 : ℝ) 1, (F ∘ γ) t ≠ F z :=
    fun t ht he => hγz t ht (hFi (hγH ht) hz he)
  have h1 := windNum_spec hc hγz hl hAc hAexp
  have h2 := windNum_spec hFc hFz (congrArg F hl) hFAc hFexp
  have he : ((windNum (F ∘ γ) (F z) : ℤ) : ℂ) *
      (2 * Real.pi * I) = ((windNum γ z : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [← h1, ← h2, hl]
    ring
  exact_mod_cast mul_right_cancel₀ QuantumZipper.CA.Topo.two_pi_I_ne_zero' he

/-- In particular the counterflow chart has the positive conformal orientation
at every interior excursion point. -/
theorem windNum_revChartInv {w : ℝ → ℝ} {s : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1)
    (hγH : MapsTo γ (Icc 0 1) H) {z : ℂ} (hz : z ∈ H)
    (hγz : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z) :
    windNum (revChartInv w s ∘ γ) (revChartInv w s z) = windNum γ z :=
  windNum_comp_of_univalent_H (isConformalBijection_revChartInv hw hw0 hs).1
    (isConformalBijection_revChartInv hw hw0 hs).2.injOn hc hl hγH hz hγz

end InteractingSLE.Sec5.Prop51HTopo
