/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfConformal
import InteractingSLE.Spec.Sec7.R7RelativeInfCriterion

/-!
# Relative Loewner evolution from compact current component charts

PROVE-R7-GAPEQ. Mapped gaps make the collapsed ambient future continuous.
Choose a pole outside this compact path, confine it in the selected Jordan
face, and reuse the boundary lift and Yuan driver construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 R7StopIn

/-- Actual compact component charts and mapped gaps imply the exact relative
Loewner predicate. A global interior-trace assumption is not needed. -/
theorem relLoewner_of_compact_charts {W : ℝ → ℝ} {η : ℝ → ℂ}
    {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsErasurePocketInf η C y₀ τ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hCH : C ⊆ H) (hψ : IsJordanCoordInf C y₀ ψ)
    (hgap : ∀ s a b : ℝ, τ ≤ s → s < a → a < b →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | τ < t ∧ η t ∈ C} →
      b ∈ closure {t | a < t ∧ η t ∈ C} → trMap W s a 0 = trMap W s b 0)
    (hcharts : ∀ s, τ ≤ s → ∀ B : ℝ, ∃ p < B, ∃ (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W C s p Γ q ∧
      ∀ t, s ≤ t → η t ∈ C → trMap W s t 0 ∈ H →
        psiMap p (trMap W s t 0) ∈ innerSide Γ) :
    RelLoewner (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ) := by
  apply relLoewner_of_jordan_faces hP hη hW hW0 hψ
  intro S hS u hu
  have huL : u ∈ Ico 0 (clockEnd η C τ) := ⟨hu.1, hu.2.trans hS.2⟩
  have hvL : ∀ v ∈ Icc u S, v ∈ Ico 0 (clockEnd η C τ) :=
    fun v hv => ⟨hu.1.trans hv.1, hv.2.trans_lt hS.2⟩
  let s := pocketFibreInf η C τ u
  let Δ := fun v => trMap W s (pocketFibreInf η C τ v) 0
  have hτs : τ ≤ s := hP.fibre_mem huL
  have hs : 0 ≤ s := hP.fibre_nonneg huL
  have hΔc : ContinuousOn Δ (Icc u S) := continuousOn_collapsed_future hP hη hW hW0
    hgap hu.1 hu.2.le hS.2
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hΔc).isBounded.exists_norm_le
  obtain ⟨p, hp, Γ, q, hchart, h11⟩ := hcharts s hτs (-|M| - 1)
  have hΔp : ∀ v ∈ Icc u S, Δ v ≠ p := by
    intro v hv he
    have hn : ‖Δ v‖ ≤ M := hM _ ⟨v, hv, rfl⟩
    rw [he, norm_real, Real.norm_eq_abs] at hn
    have hp0 : p < 0 := by linarith only [hp, abs_nonneg M]
    rw [abs_of_neg hp0] at hn
    linarith only [hn, hp, le_abs_self M]
  let Δ' := fun v => psiMap p (Δ v)
  let χ := fun ζ => trMap W 0 s (psiMapInv p ζ)
  let κ := fun ζ => ψ (χ ζ)
  have hΔ'c : ContinuousOn Δ' (Icc u S) := continuousOn_psiMap.comp hΔc hΔp
  have hΔ'0 : ∀ v ∈ Icc u S, Δ' v ≠ 0 :=
    fun v hv he => hΔp v hv (psiMap_eq_zero_iff.1 he)
  have hfib : ∀ v ∈ Icc u S, s ≤ pocketFibreInf η C τ v :=
    fun v hv => hP.monotoneOn_fibre huL (hvL v hv) hv.1
  have hχΔ : ∀ v ∈ Icc u S, χ (Δ' v) = erasedPathInf η C τ v := by
    intro v hv
    dsimp only [χ, Δ', Δ]
    rw [psiMapInv_psiMap, traceMapOut_trMap_zero hη hW hW0 hs (hfib v hv)]
    rfl
  have hΔF : MapsTo Δ' (Icc u S) (closure (innerSide Γ)) := by
    intro v hv
    have hcl : pocketFibreInf η C τ v ∈ closure {t | s < t ∧ η t ∈ C} :=
      closure_mono (s := {t | pocketFibreInf η C τ v < t ∧ η t ∈ C})
        (t := {t | s < t ∧ η t ∈ C})
        (fun t ht => ⟨(hfib v hv).trans_lt ht.1, ht.2⟩) (hP.fibre_mem_closure (hvL v hv))
    have hm := ownFuture_mem_closure_face hη hW hW0 hP.isOpen hs
      (F := psiMap p ⁻¹' innerSide Γ) h11 hcl
    have hc : ContinuousAt (psiMap p) (Δ v) := continuousOn_psiMap.continuousAt
      (isOpen_compl_singleton.mem_nhds (hΔp v hv))
    exact closure_mono (image_preimage_subset _ _) (hc.continuousWithinAt.mem_closure_image hm)
  have hκ := isConformalBijection_relative_face hP hη hW hW0 hCH hψ huL hchart
  have hχC : MapsTo χ (innerSide Γ) (closure C) := by
    intro ζ hζ
    have hm : χ ζ ∈ connectedComponentIn (C ∩ (H \ fwdHull W s)) q :=
      hchart.2.2.2.2.2 ▸ mem_image_of_mem χ hζ
    exact subset_closure ((connectedComponentIn_subset _ _ hm).1)
  have hκc : ∀ v ∈ Icc u S, ContinuousWithinAt κ (innerSide Γ) (Δ' v) := by
    intro v hv
    have hpInv : ContinuousAt (psiMapInv p) (Δ' v) := continuousOn_psiMapInv.continuousAt
      (isOpen_compl_singleton.mem_nhds (hΔ'0 v hv))
    have hInvH : psiMapInv p (Δ' v) ∈ Hbar := by
      dsimp only [Δ']
      rw [psiMapInv_psiMap]
      exact YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hs (hfib v hv)
    have hχc : ContinuousWithinAt χ (innerSide Γ) (Δ' v) :=
      ((YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs) _ hInvH).comp
        hpInv.continuousWithinAt fun ζ hζ => QuantumZipper.H_subset_Hbar
          (psiMapInv_mem_H (innerSide_subset_H hchart.1 hchart.2.1 hζ))
    have hm : χ (Δ' v) ∈ closure C := hχΔ v hv ▸ hP.erasedPath_mem (hvL v hv)
    exact (hψ.1 _ hm).comp hχc hχC
  obtain ⟨⟨z, hz, hin⟩, hFb, -⟩ := jordan_sides hchart.1 hchart.2.1
  refine ⟨Γ, z, κ, Δ', hchart.1, hz, ?_⟩
  rw [← hin]
  exact ⟨hFb, hκ, hΔ'c, hΔF, hκc, fun v hv => congrArg ψ (hχΔ v hv)⟩

end InteractingSLE.Sec7.R7RelativeInf
