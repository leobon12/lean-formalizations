/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinGrowth

/-!
# The relative own-future from a current Jordan face

PROVE-R7-GAPEQ continuation. Reuse the Jordan boundary extension and the inverse extension of
the relative hull. The face is the selected target component; no claim identifies it with all
of `C ∩ D_s`, which can contain forbidden outer bulges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.YuanCharacterisation (invExt)

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7StopIn

/-- A continuous lift into the closure of the selected bounded Jordan face yields a continuous
own-future in the relative half-plane chart. Continuity of the physical coordinate at the lifted
trace also excludes the chart's pole. This is the boundary step of Aux. 41 for a mixed face. -/
theorem exists_continuous_relative_lift
    {ζ Δ : ℝ → ℂ} {κ : ℂ → ℂ} {u S : ℝ} {Γ : Set ℂ} {q : ℂ}
    (hu : 0 ≤ u) (hc : ContinuousOn ζ (Icc 0 u)) (hH : MapsTo ζ (Icc 0 u) Hbar) (h0 : ζ 0 = 0)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hq : q ∈ Γᶜ)
    (hFb : IsBounded (connectedComponentIn Γᶜ q))
    (hκ : IsConformalBijection κ (connectedComponentIn Γᶜ q) (H \ fillH (ζ '' Icc 0 u)))
    (hΔc : ContinuousOn Δ (Icc u S))
    (hΔF : MapsTo Δ (Icc u S) (closure (connectedComponentIn Γᶜ q)))
    (hκc : ∀ v ∈ Icc u S, ContinuousWithinAt κ (connectedComponentIn Γᶜ q) (Δ v))
    (hκΔ : ∀ v ∈ Icc u S, κ (Δ v) = ζ v) :
    (∃ β : ℝ → ℂ, ContinuousOn β (Icc u S) ∧ MapsTo β (Icc u S) Hbar ∧
      ∀ v ∈ Icc u S, invExt (fillH (ζ '' Icc 0 u)) (β v) = ζ v) ∧
    MapsTo ζ (Icc u S) (closure (H \ fillH (ζ '' Icc 0 u))) := by
  let F := connectedComponentIn Γᶜ q
  let K := fillH (ζ '' Icc 0 u)
  let G := ConformalImage.mapOut K
  have hK : IsHPHull K := YuanCharacterisation.isHPHull_fillH_image hc hu h0
  have hG : IsMapOut K G := ConformalImage.isMapOut_mapOut hK
  obtain ⟨hinvc, hinvG⟩ := invExt_facts hu hc hH h0
  have hΦ : IsConformalBijection (G ∘ κ) F H := isConformalBijection_comp hG.1 hκ
  obtain ⟨p, hpΓ, Φ, hΦeq, hΦc, hΦH, hΦt⟩ :=
    exists_bdryExt_of_isConformalBijection hΓ hq hFb hΦ
  have hpF : p ∉ F := fun hp => connectedComponentIn_subset Γᶜ q hp hpΓ
  have hFsub : F ⊆ closure F \ {p} := fun w hw =>
    ⟨subset_closure hw, fun he => hpF (he ▸ hw)⟩
  have hΔp : ∀ v ∈ Icc u S, Δ v ≠ p := by
    intro v hv hvp
    have hpcl : p ∈ closure F := hvp ▸ hΔF hv
    have : (𝓝[F] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
    obtain ⟨M, hM⟩ := hG.exists_norm_le hK
    have hg := hκc v hv
    rw [hvp] at hg
    have h1 : ∀ᶠ w in 𝓝[F] p, ‖κ w‖ < ‖κ p‖ + 1 := by
      filter_upwards [hg.tendsto.eventually (ball_mem_nhds (κ p) one_pos)] with w hw
      have hn := norm_sub_norm_le (κ w) (κ p)
      rw [dist_eq_norm] at hw
      linarith
    have h2 : ∀ᶠ w in 𝓝[F] p, ‖κ p‖ + 1 + M < ‖(G ∘ κ) w‖ :=
      (tendsto_norm_atTop_iff_cobounded.2 hΦt).eventually (eventually_gt_atTop _)
    obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    have hz : κ w ∈ H \ K := hκ.2.mapsTo hwF
    have hn := hM _ hz
    change ‖κ p‖ + 1 + M < ‖G (κ w)‖ at hw2
    linarith
  constructor
  · refine ⟨fun v => Φ (Δ v), hΦc.comp hΔc fun v hv => ⟨hΔF hv, hΔp v hv⟩,
      fun v hv => hΦH ⟨hΔF hv, hΔp v hv⟩, fun v hv => ?_⟩
    have : (𝓝[F] (Δ v)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hΔF hv)
    have hmem : Δ v ∈ closure F \ {p} := ⟨hΔF hv, hΔp v hv⟩
    have hc₁ : ContinuousWithinAt (fun w => invExt K (Φ w)) F (Δ v) :=
      ((hinvc _ (hΦH hmem)).comp (hΦc _ hmem) hΦH).mono hFsub
    have heq : ∀ w ∈ F, invExt K (Φ w) = κ w := fun w hw => by
      rw [hΦeq hw]
      exact hinvG _ (hκ.2.mapsTo hw)
    have he := tendsto_nhds_unique
      (hc₁.tendsto.congr' (eventually_nhdsWithin_of_forall heq)) (hκc v hv).tendsto
    exact he.trans (hκΔ v hv)
  · intro v hv
    rw [← hκΔ v hv]
    exact closure_mono (image_subset_iff.2 fun w hw => hκ.2.mapsTo hw)
      ((hκc v hv).mem_closure_image (hΔF hv))

/-- **Aux. 41 from selected Jordan faces.** This reduction proves the driver conclusion from
geometric face charts and continuous lifts; strict relative hull growth is derived from the
erasure and strict ambient growth, rather than assumed. The exact remaining face input is
displayed in `hfaces`, and does not assert a Loewner driver. -/
theorem relLoewner_of_jordan_faces
    {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsJordanCoord C x₀ y₀ ψ)
    (hfaces : ∀ S ∈ Ioo (0 : ℝ) (pocketClock η C τ σ σ), ∀ u ∈ Ico (0 : ℝ) S,
      ∃ (Γ : Set ℂ) (q : ℂ) (κ : ℂ → ℂ) (Δ : ℝ → ℂ),
        LQGMetric.JordanMap.IsJordanCurve Γ ∧ q ∈ Γᶜ ∧
        IsBounded (connectedComponentIn Γᶜ q) ∧
        IsConformalBijection κ (connectedComponentIn Γᶜ q)
          (H \ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u)) ∧
        ContinuousOn Δ (Icc u S) ∧ MapsTo Δ (Icc u S) (closure (connectedComponentIn Γᶜ q)) ∧
        (∀ v ∈ Icc u S, ContinuousWithinAt κ (connectedComponentIn Γᶜ q) (Δ v)) ∧
        ∀ v ∈ Icc u S, κ (Δ v) = ψ (erasedPath η C τ σ v)) :
    RelLoewner (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) := by
  intro S hS0 hSL
  let ζ := fun v => ψ (erasedPath η C τ σ v)
  have hsub : Icc (0 : ℝ) S ⊆ Ico 0 (pocketClock η C τ σ σ) :=
    fun v hv => ⟨hv.1, hv.2.trans_lt hSL⟩
  have hc : ContinuousOn ζ (Icc 0 S) := hψ.1.comp
    (hP.continuousOn_erasedPath.mono fun v hv => ⟨hv.1, hv.2.trans hSL.le⟩)
    fun v hv => hP.erasedPath_mem (hsub hv)
  have h0 : ζ 0 = 0 := by
    change ψ (erasedPath η C τ σ 0) = 0
    rw [hP.erasedPath_zero]
    exact hψ.2.2.2.2.2.1
  have hH : MapsTo ζ (Icc 0 S) Hbar := fun v hv => hψ.2.2.1 (hP.erasedPath_mem (hsub hv))
  have hlocal : ∀ u ∈ Ico (0 : ℝ) S,
      (∃ β : ℝ → ℂ, ContinuousOn β (Icc u S) ∧ MapsTo β (Icc u S) Hbar ∧
        ∀ v ∈ Icc u S, invExt (fillH (ζ '' Icc 0 u)) (β v) = ζ v) ∧
      MapsTo ζ (Icc u S) (closure (H \ fillH (ζ '' Icc 0 u))) := by
    intro u hu
    obtain ⟨Γ, q, κ, Δ, hΓ, hq, hFb, hκ, hΔc, hΔF, hκc, hκΔ⟩ := hfaces S ⟨hS0, hSL⟩ u hu
    exact exists_continuous_relative_lift hu.1 (hc.mono (Icc_subset_Icc_right hu.2.le))
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

end InteractingSLE.Sec7.R7GapEqFin
