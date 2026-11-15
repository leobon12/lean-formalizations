/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLateChart

/-!
# G8: transporting boundary clearance and the filled collar

Packet PROVE-G8-DET. Continuity of the initial joint inverse transports
physical exclusion from an own hull to exclusion from the closed relative
image hull. It also transports the physical filled collar to the image hull.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.RLC.G8Det.Late

theorem image_remaining {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a u σ r : ℝ≥0} (hau : a ≤ u) (huσ : u ≤ σ)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) :
    (obstacleMap α β a r ∘ cutMap α a) '' (ownHull α u \ jointHull α β a r) =
      obstacleMap α β a r '' fwdHull (cutDrive w a) ((u : ℝ) - a) := by
  have hi := cutMap_image_ownHull hcα hw hw0 hgen hau
  have hdiff : ownHull α u \ jointHull α β a r = ownHull α u \ ownHull α a := by
    apply Subset.antisymm
    · exact sdiff_subset_sdiff_right (ownHull_subset le_rfl)
    · intro z hz
      refine ⟨hz.1, fun hB => ?_⟩
      have hgK : cutMap α a z ∈ fwdHull (cutDrive w a) ((u : ℝ) - a) := hi ▸ ⟨z, hz, rfl⟩
      have hgA : cutMap α a z ∈ cutObstacle α β a r := ⟨z, ⟨hB, hz.2⟩, rfl⟩
      exact Set.disjoint_left.1 hd (subset_closure hgA)
        (subset_closure ((QuantumZipper.fwdHull_mono (W := cutDrive w a)).1
          (sub_le_sub_right (by exact_mod_cast huσ) _) hgK))
  rw [hdiff]
  calc
    _ = obstacleMap α β a r '' (cutMap α a '' (ownHull α u \ ownHull α a)) :=
      (image_image _ _ _).symm
    _ = _ := congrArg (fun S => obstacleMap α β a r '' S) hi

theorem inv_image_remaining_subset {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a u σ r : ℝ≥0} (hau : a ≤ u) (huσ : u ≤ σ)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) (d : InitialChart α β a r) :
    d.inv '' (obstacleMap α β a r '' fwdHull (cutDrive w a) ((u : ℝ) - a)) ⊆ ownHull α u := by
  rw [← image_remaining hcα hw hw0 hgen hau huσ hd, image_image]
  rintro z ⟨v, hv, rfl⟩
  have hvD : v ∈ activeDomain α a β r := by
    rw [domain_eq hcα hcβ]
    exact ⟨fillH_subset_H _ hv.1, hv.2⟩
  change d.inv (obstacleMap α β a r (cutMap α a v)) ∈ ownHull α u
  rw [d.inv_fwd v hvD]
  exact hv.1

theorem image_remaining_subset_H {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a u σ r : ℝ≥0} (hau : a ≤ u) (huσ : u ≤ σ)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) (d : InitialChart α β a r) :
    obstacleMap α β a r '' fwdHull (cutDrive w a) ((u : ℝ) - a) ⊆ H := by
  rw [← image_remaining hcα hw hw0 hgen hau huσ hd]
  rintro z ⟨v, hv, rfl⟩
  apply d.maps_fwd
  rw [domain_eq hcα hcβ]
  exact ⟨fillH_subset_H _ hv.1, hv.2⟩

/-- Boundary marks whose inverse points miss the closed physical hull also
miss the closed image hull. -/
theorem notMem_closure_image {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a u σ r : ℝ≥0} (hau : a ≤ u) (huσ : u ≤ σ)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) (d : InitialChart α β a r)
    {x : ℝ} {p : ℂ} (hinv : d.inv x = p) (hp : p ∉ closure (ownHull α u)) :
    (x : ℂ) ∉ closure (obstacleMap α β a r '' fwdHull (cutDrive w a) ((u : ℝ) - a)) := by
  intro hx
  have hsub := image_remaining_subset_H hcα hcβ hw hw0 hgen hau huσ hd d
  have hcont := (d.continuous_inv (x : ℂ) (show (x : ℂ) ∈ Hbar from by
    change 0 ≤ (x : ℂ).im
    simp only [ofReal_im, le_refl])).mono
    (hsub.trans QuantumZipper.H_subset_Hbar)
  have hcl := hcont.mem_closure_image hx
  rw [hinv] at hcl
  exact hp (closure_mono (inv_image_remaining_subset hcα hcβ hw hw0 hgen hau huσ hd d) hcl)

/-- Continuity of the joint inverse transfers an upper physical collar to an
upper collar in the initial joint chart. -/
theorem image_collar {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a σ r : ℝ≥0} (haσ : a ≤ σ)
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) (d : InitialChart α β a r)
    (hcollar : ∃ ε > 0, ∀ z : ℂ, z ∈ H → ‖z - 1‖ < ε → z ∈ ownHull α σ) :
    ∃ δ > 0, ∀ z : ℂ, z ∈ H → ‖z - hydroMark α β a r 1‖ < δ →
      z ∈ obstacleMap α β a r '' fwdHull (cutDrive w a) ((σ : ℝ) - a) := by
  obtain ⟨ε, hε, hfill⟩ := hcollar
  have hcont := (d.continuous_inv (hydroMark α β a r 1)
    (show ((hydroMark α β a r 1 : ℝ) : ℂ) ∈ Hbar from by
      change 0 ≤ ((hydroMark α β a r 1 : ℝ) : ℂ).im
      simp only [ofReal_im, le_refl])).mono
    QuantumZipper.H_subset_Hbar
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.1 hcont ε hε
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  have hnear' := hnear hz (show dist z (hydroMark α β a r 1 : ℂ) < δ by
    simpa only [dist_eq_norm] using hdist)
  rw [d.inv_right, dist_eq_norm] at hnear'
  have hmem : d.inv z ∈ ownHull α σ \ jointHull α β a r :=
    ⟨hfill _ (domain_subset_own hcα hcβ a r (d.maps_inv hz)).1 hnear',
      (domain_eq hcα hcβ a r ▸ d.maps_inv hz).2⟩
  rw [← image_remaining hcα hw hw0 hgen haσ le_rfl hd]
  exact ⟨d.inv z, hmem, d.fwd_inv z hz⟩

end InteractingSLE.RLC.G8Det.Late
