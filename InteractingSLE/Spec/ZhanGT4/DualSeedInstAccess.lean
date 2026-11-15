/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdEight
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformGeometry

/-!
# Actual source-chain accesses from separated hull enclosures

Packet PROVE-ZHAN-GT4-A22. The chosen source image chain has an alive
mutual tip even at frozen height zero. Seed chart clearance is uniform
before the first path, all its seed coordinates and both times.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- The landed choice used by the source record is an actual image chain
whenever the two hulls stay in separated enclosures. -/
theorem seedSrcOwn_of_enclosures {W Wf : ℝ → ℝ} {S t δ : ℝ} {H₁ H₂ : Set ℂ}
    (hW : Continuous W) (h0 : W 0 = 0) (hS : 0 < S) (hWf : Continuous Wf) (ht : 0 ≤ t)
    (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    (hK : fwdHull W S ⊆ H₁) (hKf : fwdHull Wf t ⊆ H₂) :
    OwnData W (fwdHull Wf t) (frzChart Wf t) S
      (seedSrcClock W S Wf t) (seedSrcDriver W S Wf t) :=
  A1EightSeed.ownData_imgChain
    (A1EightSeed.exists_ownData_of_encl hW h0 hS hWf ht hδ hsep hK hKf)

/-- Separated enclosures prove aliveness of the actual frozen tip for any
image chain. This includes height zero and does not require protected marks. -/
theorem OwnData.tip_alive_of_enclosures {W Wf a U : ℝ → ℝ} {S t δ : ℝ} {H₁ H₂ : Set ℂ}
    (h : OwnData W (fwdHull Wf t) (frzChart Wf t) S a U)
    (h₁ : IsHPHull H₁) (h₂ : IsHPHull H₂) (hδ : 0 < δ)
    (hsep : ∀ z ∈ H₂, ∀ w ∈ H₁, 2 * δ ≤ ‖z - w‖)
    (hWf : Continuous Wf) (ht : 0 ≤ t) (h0 : W 0 ≠ Wf 0)
    (hsrc : ((Wf 0 : ℝ) : ℂ) ∈ closure H₂)
    (hK : fwdHull W S ⊆ H₁) (hKf : fwdHull Wf t ⊆ H₂) :
    ∃ q, IsForwardSol U ((Wf t : ℝ) : ℂ) (a S) q := by
  have hsep' : ∀ z ∈ H₁, ∀ w ∈ H₂, 2 * δ ≤ ‖z - w‖ := by
    intro z hz w hw
    rw [norm_sub_rev]
    exact hsep w hw z hz
  obtain ⟨r, hr, hclear⟩ := exists_le_norm_fwdMap_uniform h₂ h₁.2.1 h₁.1 hδ hsep'
  obtain ⟨q, hq, hU0⟩ := h.toImgData.exists_start_alive hWf ht h0
  have hn := re_ne_zero_of_im_eq_zero (hq.2 t ⟨ht, le_rfl⟩).1
    (im_eq_zero_of_isForwardSol_real hWf hq ⟨ht, le_rfl⟩)
  have hne : Wf t ≠ U 0 := by
    intro he
    apply hn
    linarith only [hU0, he]
  exact h.toImgData.exists_tip_alive hr
    (fun z hz => hclear Wf hWf hsrc t hKf t ⟨ht, le_rfl⟩ z (hK hz)) hne ⟨h.pos.le, le_rfl⟩

/-- One enclosure constant clears every integrated seed interval from the
entire image of the opposite enclosure, before any choice of the paths. -/
theorem exists_seed_clearance_of_enclosures {H₁ H₂ : Set ℂ}
    (h₁ : IsHPHull H₁) (h₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) :
    ∃ r > (0 : ℝ), ∀ (W Vlo Vhi : ℝ → ℝ) (S : ℝ),
      Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure H₁ → fwdHull W S ⊆ H₁ →
      IsSeedCoordinate W Vlo S → IsSeedCoordinate W Vhi S →
      ∀ s ∈ Icc (0 : ℝ) S, ∀ x ∈ uIcc (Vlo s) (Vhi s),
        Disjoint (ball (x : ℂ) r) (frzChart W s '' H₂) := by
  obtain ⟨r, hr, hm⟩ := exists_le_norm_fwdMap_sub_seed_interval_uniform h₁ h₂.2.1 h₂.1 hδ hsep
  refine ⟨r, hr, fun W Vlo Vhi S hW hsrc hK hlo hhi s hs x hx => ?_⟩
  refine Set.disjoint_left.2 ?_
  rintro z hz ⟨w, hw, rfl⟩
  have hb := hm W Vlo Vhi S hW hsrc hK hlo hhi s hs w hw x hx
  rw [mem_ball, dist_eq_norm] at hz
  exact not_lt_of_ge hb hz

end InteractingSLE.ZhanGT4
