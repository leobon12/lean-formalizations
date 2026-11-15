/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfComponent

/-!
# Relative uniformization of the selected compact face at infinity

PROVE-R7-GAPEQ. The landed ambient inverse and compactification are conformal
and injective. GC2 identifies the image of their selected component in the
pocket coordinate with the relative surviving half-plane domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 R7StopIn

/-- A selected compact component chart followed by the pocket coordinate is
the conformal map onto the relative surviving domain. -/
theorem isConformalBijection_relative_face {W : ℝ → ℝ} {η : ℝ → ℂ}
    {C Γ : Set ℂ} {y₀ q : ℂ} {τ u p : ℝ} {ψ : ℂ → ℂ}
    (hP : IsErasurePocketInf η C y₀ τ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hCH : C ⊆ H) (hψ : IsJordanCoordInf C y₀ ψ)
    (hu : u ∈ Ico 0 (clockEnd η C τ))
    (hchart : R7EndFace.InfiniteFaceChart W C (pocketFibreInf η C τ u) p Γ q) :
    IsConformalBijection (fun ζ => ψ (trMap W 0 (pocketFibreInf η C τ u) (psiMapInv p ζ)))
      (innerSide Γ) (H \ fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u)) := by
  let s := pocketFibreInf η C τ u
  let χ := fun ζ => trMap W 0 s (psiMapInv p ζ)
  let E := connectedComponentIn (C ∩ (H \ fwdHull W s)) q
  have hs : 0 ≤ s := hP.fibre_nonneg hu
  have hFH : innerSide Γ ⊆ H := innerSide_subset_H hchart.1 hchart.2.1
  have hψH : ∀ ζ ∈ innerSide Γ, psiMapInv p ζ ∈ H := fun ζ hζ => psiMapInv_mem_H (hFH hζ)
  have hfeq : ∀ w ∈ H, trMap W 0 s w = fwdMapInv W s w := fun w hw => by
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs hw,
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero]
  have hχd : DifferentiableOn ℂ χ (innerSide Γ) := by
    intro ζ hζ
    have hz0 : ζ ≠ 0 := WangWu.ne_zero_of_mem_H (hFH hζ)
    have hd : DifferentiableAt ℂ (psiMapInv p) ζ :=
      (differentiableAt_const _).sub (differentiableAt_id.inv hz0)
    have hd2 := QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hs _ (hψH ζ hζ)
    have hd3 := hd2.comp ζ hd.differentiableWithinAt hψH
    exact hd3.congr (fun ζ' hζ' => hfeq _ (hψH ζ' hζ')) (hfeq _ (hψH ζ hζ))
  have hχi : InjOn χ (innerSide Γ) := by
    intro ζ hζ ζ' hζ' he
    change trMap W 0 s (psiMapInv p ζ) = trMap W 0 s (psiMapInv p ζ') at he
    rw [hfeq _ (hψH ζ hζ), hfeq _ (hψH ζ' hζ')] at he
    have hi := QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hs (hψH ζ hζ) (hψH ζ' hζ') he
    have he' := congrArg (psiMap p) hi
    rwa [psiMap_psiMapInv, psiMap_psiMapInv] at he'
  have hχ : IsConformalBijection χ (innerSide Γ) E := by
    refine ⟨hχd, ?_⟩
    have hi := hχi.bijOn_image
    rwa [hchart.2.2.2.2.2] at hi
  have hEC : E ⊆ C := (connectedComponentIn_subset _ _).trans inter_subset_left
  have himage := image_unbounded_component hP hη hCH hψ hu rfl hchart.2.2.2.2.1
  have hψE : IsConformalBijection ψ E
      (H \ fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u)) := by
    refine ⟨hψ.2.2.2.1.1.mono hEC, ?_⟩
    have hi := (hψ.2.2.2.1.2.injOn.mono hEC).bijOn_image
    rwa [himage] at hi
  exact isConformalBijection_comp hψE hχ

end InteractingSLE.Sec7.R7RelativeInf
