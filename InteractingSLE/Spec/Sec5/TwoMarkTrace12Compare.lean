/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkRegular5Limits
import InteractingSLE.Spec.Sec5.Aux61R45Visit

/-!
# Comparison contacts from a completed trace prefix

The deterministic GB7a contact construction needs a completed trace only up to
the candidate visit. Its comparison witness remains valid at any larger horizon.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Trace12

open Zhan.Retarget

/-- Increasing the source horizon increases the image capacity horizon. -/
theorem newHorizon_mono {a : ℝ} {w v : ℝ≥0 → ℝ} {S T : ℝ≥0∞} (hST : S ≤ T) :
    newHorizon a w v S ≤ newHorizon a w v T := by
  unfold newHorizon
  refine iSup_le fun s => iSup_le fun hs => ?_
  exact le_iSup_of_le s (le_iSup_of_le (hs.trans_le hST) le_rfl)

/-- A comparison witness uses only a finite contact time bounded by its horizon. -/
theorem rightCmpPath_mono {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {S T : ℝ≥0∞} {k : Fin nR} {k2 : Option (Fin nR)} {c : ℝ} {q : ℝ≥0}
    (h : GB7a.RightCmpPath ρL ρR w vL vR S k k2 c q) (hST : S ≤ T) :
    GB7a.RightCmpPath ρL ρR w vL vR T k k2 c q := by
  obtain ⟨t, hqt, ht, hgap, henergy, hlim⟩ := h
  exact ⟨t, hqt, ht.trans hST, hgap, henergy, hlim⟩

/-- A completed generating trace gives the joint finite state limit needed by GB7a. -/
theorem state_limit_of_completed_trace {κ : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {S : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b S)
    (hΓ : IsGeneratingTrace w S Γ) {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) = S) :
    ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun u => (w u, fun i => vL i u, fun j => vR j u))
        (𝓝[<] t) (𝓝 (w₀, vL₀, vR₀)) := by
  have hg : IsGeneratingTrace w (t : ℝ≥0∞) Γ := ht.symm ▸ hΓ
  obtain ⟨w₀, hw⟩ := Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace hg
    (ht.symm ▸ hp.continuousOn_w) hp.w_zero ht0
  obtain ⟨hL, hR⟩ := Regular5.exists_force_limits_of_driver_limit hp ht ⟨w₀, hw⟩
  choose vL₀ hvL using hL
  choose vR₀ hvR using hR
  exact ⟨w₀, vL₀, vR₀, hw.prodMk_nhds ((tendsto_pi_nhds.2 hvL).prodMk_nhds (tendsto_pi_nhds.2 hvR))⟩

/-- A left visit of any completed prefix gives a comparison contact before the full horizon. -/
theorem left_comparison_of_completed_prefix {κ : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {S T : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T)
    (hST : S ≤ T) (hord : IsOrderedForceWord xL xR)
    (hΓ : IsGeneratingTrace w S Γ) (hinj : InjOn Γ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ S})
    {k : Fin nL} {a : ℝ} (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hvisit : ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ S ∧ ∃ y ∈ Ioo a (xL k), Γ u = (y : ℂ)) :
    ∃ q : ℚ, GB7a.RightCmpPath ρR ρL (fun u => -w u)
      (fun i u => -vR i u) (fun i u => -vL i u) T k none
      (∑ i ∈ Finset.univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal := by
  have hlocal := hp.mono hST
  obtain ⟨q, hq⟩ := Aux61R45.leftCmpPath_of_visit_upTo hlocal hord hΓ hinj
    (fun t ht0 ht => state_limit_of_completed_trace hlocal hΓ ht0 ht) hnext hvisit
  exact ⟨q, rightCmpPath_mono hq hST⟩

end InteractingSLE.Sec5.TwoMark.Trace12
