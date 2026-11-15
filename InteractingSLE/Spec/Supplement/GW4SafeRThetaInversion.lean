/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRThetaTransport
import InteractingSLE.Spec.Supplement.GW4RelSpace
import InteractingSLE.Spec.Supplement.GW4CLocRat

/-! # GW4: the exact inversion and centering of the union mean -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Sec7.Aux119Heights Sec7.SideC12 GW4Rel
open WangWu (negInv reflectField)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- Subtracting the actual harmonic background subtracts it from the
canonical representative throughout the open domain. -/
theorem harmRep_sub_background {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    {T : DistOn upperHalfPlaneOpens} (hT : IsHarmonicDistOn T U)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    EqOn (harmRep (T - smoothDist upperHalfPlaneOpens u) U)
      (fun z => harmRep T U z - u z) U := by
  have hn : smoothDist upperHalfPlaneOpens (-u) = -smoothDist upperHalfPlaneOpens u :=
    Distribution.ofFun_neg
  rw [sub_eq_add_neg, ← hn]
  exact harmRep_add_smoothDist hU hUH hT hu.neg

/-- The source inversion has the exact SideC12 shift even when the input
is an uncentered union mean rather than an ambient GFF. -/
theorem harmRep_invField {κ : ℝ} (hκ : 0 < κ) {U : Set ℂ}
    (hU : IsOpen U) (hUH : U ⊆ H) {M : DistOn upperHalfPlaneOpens}
    (hM : IsHarmonicDistOn M U) :
    EqOn (harmRep (GW4Rel.invField κ M) (negInv '' U))
      (fun z => -harmRep M U (negInv z) +
        sourceShift (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0 z) (negInv '' U) := by
  have hTr : IsTranslateAddConst 0 0 (GW4Rel.invField κ M) (GW4Rel.invField κ M) := by
    simpa using Sec7.StripSysField.isTranslateAddConst_zero_self (GW4Rel.invField κ M) 0
  rw [field_eq_reflect_add (isChartTransport_invField hκ M) hTr]
  have hR := WangWu.isHarmonicDistOn_reflectField hU hUH hM
  have he := harmRep_add_smoothDist (WangWu.isOpen_image_negInv hU hUH)
    (WangWu.image_negInv_subset_H hUH) hR
    (sourceShift_harmonic (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0)
  intro z hz
  rw [he hz]
  simp only
  rw [harmRep_reflect hU hUH hM hz]

/-- The uncentered physical union mean read in the actual component and
counterflow coordinates, with its full inherited lift and deterministic
background, has this precise representative. -/
theorem harmRep_component_invField {κ : ℝ} (hκ : 0 < κ)
    {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {A : Set ℂ} (hAo : IsOpen (H \ A))
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (H \ A))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    let T := GW4Rel.invField κ (Chart.chartTransport hc 1 0 (chiC κ) M) -
      smoothDist upperHalfPlaneOpens u
    EqOn (fun z => harmRep T (H \ CLoc.chartSet c A) z + u z)
      (fun z => -(harmRep M (H \ A) (c.2.1 (negInv z)) +
        chiC κ * c.2.2 (c.2.1 (negInv z))) +
          sourceShift (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0 z)
      (H \ CLoc.chartSet c A) := by
  let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  let O := Restart.MarkovChart.chartPre c (H \ A)
  let T := Chart.chartTransport hc 1 0 (chiC κ) M
  have hOo : IsOpen O := Restart.MarkovChart.isOpen_chartPre hc hAo
  have hOH : O ⊆ H := Restart.MarkovChart.chartPre_subset_H _ _
  have hD : (c.dom : Set ℂ) = C := CLoc.coe_dom_of_isComponentChart hch hCo hCH
  have hTc : ContinuousOn c.2.2 c.dom := hD ▸ hch.2.2.2.2.2.1
  have hTh : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom :=
    hD ▸ CLoc.harmonicOnNhd_lift_of_isComponentChart hch hCo hCH
  have hTO : IsHarmonicDistOn T O := by
    refine Sec7.Lemma72C.isHarmonicDistOn_chartTransport hc hTc hTh hOo hOH ?_ 0 (chiC κ)
    rw [Restart.MarkovChart.image_chartPre hc]
    exact IsHarmonicDistOn.mono hM inter_subset_left
  have hImage : H \ CLoc.chartSet c A = negInv '' O := by
    rw [CLoc.H_diff_chartSet]
    ext z
    constructor
    · intro hz
      exact ⟨negInv z, hz.2, WangWu.negInv_negInv z⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨WangWu.negInv_mem_H (hOH hw), ?_⟩
      change negInv (negInv w) ∈ O
      simpa only [WangWu.negInv_negInv] using hw
  have hInv : IsHarmonicDistOn (GW4Rel.invField κ T) (negInv '' O) := by
    have hTr : IsTranslateAddConst 0 0 (GW4Rel.invField κ T) (GW4Rel.invField κ T) := by
      simpa using Sec7.StripSysField.isTranslateAddConst_zero_self (GW4Rel.invField κ T) 0
    rw [field_eq_reflect_add (isChartTransport_invField hκ T) hTr]
    exact Coupling.IsHarmonicDistOn.add' (WangWu.isOpen_image_negInv hOo hOH)
      (WangWu.isHarmonicDistOn_reflectField hOo hOH hTO)
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist
        (sourceShift_harmonic (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0))
        (WangWu.image_negInv_subset_H hOH))
  change EqOn (fun z => harmRep (GW4Rel.invField κ T - smoothDist upperHalfPlaneOpens u)
    (H \ CLoc.chartSet c A) z + u z) _ _
  intro z hz
  have hz' : z ∈ negInv '' O := hImage ▸ hz
  have hzO : negInv z ∈ O := by
    obtain ⟨w, hw, rfl⟩ := hz'
    simpa only [WangWu.negInv_negInv] using hw
  change harmRep (GW4Rel.invField κ T - smoothDist upperHalfPlaneOpens u)
    (H \ CLoc.chartSet c A) z + u z = _
  rw [hImage, harmRep_sub_background (WangWu.isOpen_image_negInv hOo hOH)
    (WangWu.image_negInv_subset_H hOH) hInv hu hz']
  simp only
  rw [harmRep_invField hκ hOo hOH hTO hz']
  simp only
  rw [harmRep_component_transport hch hCo hCH hAo hM 0 (chiC κ) hzO]
  simp only [add_zero]
  ring

end InteractingSLE.Theorem14.GW4Fix
