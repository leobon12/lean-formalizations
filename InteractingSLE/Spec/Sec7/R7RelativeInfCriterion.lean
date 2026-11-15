/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfGrowth
import InteractingSLE.Spec.Sec7.R7GapEqFinFace

/-!
# Yuan's driver criterion for infinite mixed erasure

PROVE-R7-GAPEQ. Reuse the finite-face boundary extension lemma. Jordan face
lifts imply relative no-return, and ambient strict growth supplies criterion B;
Yuan then constructs the strictly increasing capacity clock and continuous driver.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.YuanCharacterisation (invExt)

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 R7StopIn

/-- The exact selected bounded-face data imply Aux. 41 at infinity. Both strict
relative hull growth and the continuous driver are conclusions. -/
theorem relLoewner_of_jordan_faces
    {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsErasurePocketInf η C y₀ τ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsJordanCoordInf C y₀ ψ)
    (hfaces : ∀ S ∈ Ioo (0 : ℝ) (clockEnd η C τ), ∀ u ∈ Ico (0 : ℝ) S,
      ∃ (Γ : Set ℂ) (q : ℂ) (κ : ℂ → ℂ) (Δ : ℝ → ℂ),
        LQGMetric.JordanMap.IsJordanCurve Γ ∧ q ∈ Γᶜ ∧
        IsBounded (connectedComponentIn Γᶜ q) ∧
        IsConformalBijection κ (connectedComponentIn Γᶜ q)
          (H \ fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u)) ∧
        ContinuousOn Δ (Icc u S) ∧ MapsTo Δ (Icc u S) (closure (connectedComponentIn Γᶜ q)) ∧
        (∀ v ∈ Icc u S, ContinuousWithinAt κ (connectedComponentIn Γᶜ q) (Δ v)) ∧
        ∀ v ∈ Icc u S, κ (Δ v) = ψ (erasedPathInf η C τ v)) :
    RelLoewner (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ) := by
  intro S hS0 hSL
  let ζ := fun v => ψ (erasedPathInf η C τ v)
  have hsub : Icc (0 : ℝ) S ⊆ Ico 0 (clockEnd η C τ) :=
    fun v hv => ⟨hv.1, hv.2.trans_lt hSL⟩
  have hc : ContinuousOn ζ (Icc 0 S) := hψ.1.comp
    (hP.continuousOn_erasedPath.mono hsub)
    fun v hv => hP.erasedPath_mem (hsub hv)
  have h0 : ζ 0 = 0 := by
    change ψ (erasedPathInf η C τ 0) = 0
    rw [hP.erasedPath_zero]
    exact hψ.2.2.2.2.2.1
  have hH : MapsTo ζ (Icc 0 S) Hbar := fun v hv => hψ.2.2.1 (hP.erasedPath_mem (hsub hv))
  have hlocal : ∀ u ∈ Ico (0 : ℝ) S,
      (∃ β : ℝ → ℂ, ContinuousOn β (Icc u S) ∧ MapsTo β (Icc u S) Hbar ∧
        ∀ v ∈ Icc u S, invExt (fillH (ζ '' Icc 0 u)) (β v) = ζ v) ∧
      MapsTo ζ (Icc u S) (closure (H \ fillH (ζ '' Icc 0 u))) := by
    intro u hu
    obtain ⟨Γ, q, κ, Δ, hΓ, hq, hFb, hκ, hΔc, hΔF, hκc, hκΔ⟩ := hfaces S ⟨hS0, hSL⟩ u hu
    exact R7GapEqFin.exists_continuous_relative_lift hu.1 (hc.mono (Icc_subset_Icc_right hu.2.le))
      (hH.mono_left (Icc_subset_Icc_right hu.2.le)) h0 hΓ hq hFb hκ hΔc hΔF hκc hκΔ
  have hA : DrivingCriterionA ζ S := by
    intro u hu z hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact (hlocal u ⟨hu.1.le, hu.2⟩).2 ⟨hv.1.le, hv.2⟩
  have hB : DrivingCriterionB ζ S := drivingCriterionB_erasure hP hη hW hW0 hψ hSL
  have hm := strictMonoOn_fillH_of_drivingCriteria hc hA hB
  have hii : YuanCharacterisation.HasContinuousOwnFuture ζ S := fun u hu => (hlocal u hu).1
  exact (exists_loewner_and_hasSimpleApproxOn_of_hasContinuousOwnFuture hS0 hc h0 hH hm hii
    (show S / 2 < S by linarith only [hS0])).1

end InteractingSLE.Sec7.R7RelativeInf
