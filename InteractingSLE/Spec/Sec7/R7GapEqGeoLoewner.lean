/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqGeoFace

/-!
# The finite driver from target-face geometry

PROVE-R7-GAPEQ. The geometric input identifies the image of a Jordan face with the target
component and confines active interior visits to that face. The relative conformal chart and
confinement of all retained mapped values are proved. Mapped gap equality remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.R7GapEqGeo

open Sec6 R7StopIn R7GapEqFin

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- The ambient map-out inverse followed by the pocket coordinate is the relative conformal
face chart, once the face image is the target component. -/
theorem isConformalBijection_target_face (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hCH : C ⊆ H) (hψ : IsJordanCoord C x₀ y₀ ψ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ)) {q : ℂ} {F : Set ℂ}
    (hFH : F ⊆ H)
    (himage : trMap W 0 (pocketFibre η C τ σ u) '' F =
      connectedComponentIn (C ∩ (H \ fwdHull W (pocketFibre η C τ σ u))) q)
    (hxcl : x₀ ∈ closure (trMap W 0 (pocketFibre η C τ σ u) '' F)) :
    MapsTo (trMap W 0 (pocketFibre η C τ σ u)) F C ∧
      IsConformalBijection (ψ ∘ trMap W 0 (pocketFibre η C τ σ u)) F
        (H \ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u)) := by
  let s := pocketFibre η C τ σ u
  let E := trMap W 0 s '' F
  have hEC : E ⊆ C := (himage ▸ connectedComponentIn_subset _ _).trans inter_subset_left
  have hs0 : 0 ≤ s := hP.nonneg.trans (hP.fibre_mem u).1
  have hfeq : ∀ w ∈ H, trMap W 0 s w = fwdMapInv W s w := fun w hw => by
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs0 hw,
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero]
  have hf : IsConformalBijection (trMap W 0 s) F E := by
    refine ⟨((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hs0).mono hFH).congr
      (fun w hw => hfeq w (hFH hw)), ?_⟩
    refine (show InjOn (trMap W 0 s) F from ?_).bijOn_image
    intro w hw w' hw' heq
    rw [hfeq w (hFH hw), hfeq w' (hFH hw')] at heq
    exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hs0 (hFH hw) (hFH hw') heq
  have himg := image_target_component hP hη hCH hψ hu himage hxcl
  have hψE : IsConformalBijection ψ E
      (H \ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u)) := by
    refine ⟨hψ.2.2.2.1.1.mono hEC, ?_⟩
    have hb := (hψ.2.2.2.1.2.injOn.mono hEC).bijOn_image
    rwa [himg] at hb
  exact ⟨fun w hw => hEC ⟨w, hw, rfl⟩, isConformalBijection_comp hψE hf⟩

/-- **Relative Loewner evolution from the target face.** Compared with the previous finite
reduction, the relative conformal image and closed-face confinement are conclusions.
`hgeometry` is the exact remaining planar input; `hmapped` is the remaining prime-end input. -/
theorem relLoewner_of_target_faces (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hCH : C ⊆ H) (hψ : IsJordanCoord C x₀ y₀ ψ)
    (hmapped : ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      trMap W s a 0 = trMap W s b 0)
    (hgeometry : ∀ u ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ),
      ∃ (Γ : Set ℂ) (p q : ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ p ∈ Γᶜ ∧
        IsBounded (connectedComponentIn Γᶜ p) ∧ connectedComponentIn Γᶜ p ⊆ H ∧
        trMap W 0 (pocketFibre η C τ σ u) '' connectedComponentIn Γᶜ p =
          connectedComponentIn (C ∩ (H \ fwdHull W (pocketFibre η C τ σ u))) q ∧
        x₀ ∈ closure (trMap W 0 (pocketFibre η C τ σ u) '' connectedComponentIn Γᶜ p) ∧
        ∀ t, pocketFibre η C τ σ u ≤ t → η t ∈ C →
          trMap W (pocketFibre η C τ σ u) t 0 ∈ H →
          trMap W (pocketFibre η C τ σ u) t 0 ∈ connectedComponentIn Γᶜ p) :
    RelLoewner (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) := by
  apply relLoewner_of_mapped_faces hP hη hW hW0 hψ hmapped
  intro S hS u hu
  have huL : u ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ) := ⟨hu.1, hu.2.trans hS.2⟩
  obtain ⟨Γ, p, q, hΓ, hp, hFb, hFH, himage, hxcl, h11⟩ := hgeometry u huL
  obtain ⟨hfC, hκ⟩ := isConformalBijection_target_face hP hη hW hW0 hCH hψ huL hFH himage hxcl
  refine ⟨Γ, p, hΓ, hp, hFb, hFH, hfC, hκ, fun v hv => ?_⟩
  have hvL : v ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ) := ⟨hu.1.trans hv.1, hv.2.trans_lt hS.2⟩
  apply ownFuture_mem_closure_face hη hW hW0 hP.isOpen
    (hP.nonneg.trans (hP.fibre_mem u).1) h11
  exact closure_mono (s := {t | pocketFibre η C τ σ v < t ∧ η t ∈ C})
    (t := {t | pocketFibre η C τ σ u < t ∧ η t ∈ C})
    (fun t ht => ⟨(hP.monotone_fibre hv.1).trans_lt ht.1, ht.2⟩)
    (hP.mem_closure_of_right (hP.fibre_lt_σ hvL) (hP.clock_lt_of_fibre ⟨hvL.1, hvL.2.le⟩))

end InteractingSLE.Sec7.R7GapEqGeo
