/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinFace

/-!
# Mapped erasure gaps and the finite relative driver

PROVE-R7-GAPEQ continuation. The ambient own-future collapses continuously when mapped gap
endpoints agree. Together with the actual selected-face chart and confinement, this proves
`R7StopIn.RelLoewner`. The two remaining geometric inputs are explicit in the final theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7StopIn

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- The restriction identity for right erasure fibres needs only the clock properties of
`IsErasurePocket`. Adapt the landed contained-pocket identity to that weaker geometry. -/
theorem fibreRight_restrict_erasure (hP : IsErasurePocket η C x₀ y₀ τ σ) {u S v : ℝ}
    (hu : 0 ≤ u) (hS : S < pocketClock η C τ σ σ) (hv : v ∈ Icc u S) :
    fibreRight (pocketClock η C τ σ) (pocketFibre η C τ σ u) (pocketFibre η C τ σ S) v =
      pocketFibre η C τ σ v := by
  have hv0 : 0 ≤ v := hu.trans hv.1
  have hℓs := hP.clock_fibre ⟨hu, (hv.1.trans hv.2).trans hS.le⟩
  have hℓv := hP.clock_fibre ⟨hv0, hv.2.trans hS.le⟩
  have hvA : pocketFibre η C τ σ v ∈
      {t ∈ Icc (pocketFibre η C τ σ u) (pocketFibre η C τ σ S) |
        pocketClock η C τ σ t ≤ max v (pocketClock η C τ σ (pocketFibre η C τ σ u))} :=
    ⟨⟨hP.monotone_fibre hv.1, hP.monotone_fibre hv.2⟩, by rw [hℓv]; exact le_max_left _ _⟩
  refine le_antisymm (csSup_le ⟨_, hvA⟩ fun t ht => ?_) (le_csSup ⟨_, fun t ht => ht.1.2⟩ hvA)
  rw [hℓs, max_eq_left hv.1] at ht
  exact le_fibreRight ⟨(hP.fibre_mem u).1.trans ht.1.1, ht.1.2.trans (hP.fibre_mem S).2⟩
    (by rw [IsErasurePocket.clock_τ, max_eq_left hv0]; exact ht.2)

/-- Mapped gap equality, stated at ordinary closed gaps rather than clock fibres, makes the
collapsed ambient own-future continuous. This is exactly the missing prime-end assertion;
physical endpoint equality alone is not substituted for it. -/
theorem continuousOn_mapped_erasure
    (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hmapped : ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      trMap W s a 0 = trMap W s b 0)
    {u S : ℝ} (hu : 0 ≤ u) (huS : u ≤ S) (hSL : S < pocketClock η C τ σ σ) :
    ContinuousOn (fun v => trMap W (pocketFibre η C τ σ u) (pocketFibre η C τ σ v) 0)
      (Icc u S) := by
  let s := pocketFibre η C τ σ u
  let T := pocketFibre η C τ σ S
  have huL : u < pocketClock η C τ σ σ := huS.trans_lt hSL
  have hτs : τ ≤ s := (hP.fibre_mem u).1
  have hsσ : s < σ := hP.fibre_lt_σ ⟨hu, huL⟩
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  have hsT : s ≤ T := hP.monotone_fibre huS
  have hTσ : T < σ := hP.fibre_lt_σ ⟨hu.trans huS, hSL⟩
  have hℓs : pocketClock η C τ σ s = u := hP.clock_fibre ⟨hu, huL.le⟩
  have hℓT : pocketClock η C τ σ T = S := hP.clock_fibre ⟨hu.trans huS, hSL.le⟩
  have hc := continuousOn_collapsed_ownFuture hη hW hW0 hP.continuous_clock hP.monotone_clock
    hs0 hsT (S := T) (fun a ha b hb hab hℓab hmax => ?_)
  · rw [hℓs, hℓT] at hc
    exact hc.congr fun v hv => congrArg (fun t => trMap W s t 0)
      (fibreRight_restrict_erasure hP hu hSL hv).symm
  · have hbσ : b < σ := hb.2.trans_lt hTσ
    obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre hτs
      (hP.clock_lt_of_fibre ⟨hu.trans huS, hSL.le⟩) ha hb hab hbσ hℓab hmax
    have hsa : s < a := by
      refine lt_of_le_of_ne ha.1 fun he => ?_
      rw [← he] at hℓab
      exact (hP.clock_lt_of_fibre ⟨hu, huL.le⟩ b
        ⟨lt_of_le_of_lt (le_of_eq he) hab, hbσ.le⟩).ne hℓab
    exact hmapped s ⟨hτs, hsσ⟩ a b hsa hab hbσ hgap (hacl.resolve_left hsa.ne') hbcl

/-- **The finite mixed/outer relative driver from the current-face geometry and mapped gaps.**
The face is a bounded Jordan component in the ambient own chart. Its conformal image is the
relative surviving domain, and the retained mapped future is confined to its closure.
Everything else, including continuity of the collapsed own-future and strict hull growth,
is proved here from landed erasure and Loewner results.

`hmapped` and `hface` are named exact remaining inputs; this theorem does not assert them
unconditionally for the random mixed pocket. -/
theorem relLoewner_of_mapped_faces
    (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsJordanCoord C x₀ y₀ ψ)
    (hmapped : ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      trMap W s a 0 = trMap W s b 0)
    (hface : ∀ S ∈ Ioo (0 : ℝ) (pocketClock η C τ σ σ), ∀ u ∈ Ico (0 : ℝ) S,
      ∃ (Γ : Set ℂ) (q : ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ q ∈ Γᶜ ∧
        IsBounded (connectedComponentIn Γᶜ q) ∧ connectedComponentIn Γᶜ q ⊆ H ∧
        MapsTo (trMap W 0 (pocketFibre η C τ σ u)) (connectedComponentIn Γᶜ q) C ∧
        IsConformalBijection (ψ ∘ trMap W 0 (pocketFibre η C τ σ u))
          (connectedComponentIn Γᶜ q)
          (H \ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u)) ∧
        ∀ v ∈ Icc u S,
          trMap W (pocketFibre η C τ σ u) (pocketFibre η C τ σ v) 0 ∈
            closure (connectedComponentIn Γᶜ q)) :
    RelLoewner (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) := by
  apply relLoewner_of_jordan_faces hP hη hW hW0 hψ
  intro S hS u hu
  obtain ⟨Γ, q, hΓ, hq, hFb, hFH, hfC, hκ, hΔF⟩ := hface S hS u hu
  let s := pocketFibre η C τ σ u
  let Δ := fun v => trMap W s (pocketFibre η C τ σ v) 0
  have hs0 : 0 ≤ s := hP.nonneg.trans (hP.fibre_mem u).1
  have hfΔ : ∀ v ∈ Icc u S, trMap W 0 s (Δ v) = erasedPath η C τ σ v :=
    fun v hv => traceMapOut_trMap_zero hη hW hW0 hs0 (hP.monotone_fibre hv.1)
  have hFHbar : closure (connectedComponentIn Γᶜ q) ⊆ Hbar := by
    rw [← closure_H]
    exact closure_mono hFH
  have hfc : ContinuousOn (trMap W 0 s) Hbar :=
    YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs0
  have hCsub : C ⊆ closure C \ {x₀} := fun z hz =>
    ⟨subset_closure hz, fun he => hP.notMem_x (he ▸ hz)⟩
  refine ⟨Γ, q, ψ ∘ trMap W 0 s, Δ, hΓ, hq, hFb, hκ,
    continuousOn_mapped_erasure hP hη hW hW0 hmapped hu.1 hu.2.le hS.2, hΔF, ?_, ?_⟩
  · intro v hv
    have hmem : trMap W 0 s (Δ v) ∈ closure C \ {x₀} := by
      rw [hfΔ v hv]
      exact hP.erasedPath_mem ⟨hu.1.trans hv.1, hv.2.trans_lt hS.2⟩
    exact (hψ.1 _ hmem).comp ((hfc _ (hFHbar (hΔF v hv))).mono
      fun w hw => QuantumZipper.H_subset_Hbar (hFH hw)) fun w hw => hCsub (hfC hw)
  · intro v hv
    exact congrArg ψ (hfΔ v hv)

end InteractingSLE.Sec7.R7GapEqFin
