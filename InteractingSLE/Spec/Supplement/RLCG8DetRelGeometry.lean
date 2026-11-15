/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRelBoundary

/-!
# G8's late-cut geometry and the relative physical chart

Packet PROVE-G8-DET. `LateCutGeometry` records the remaining geometric
obligations in the original cut chart. Its hulls and maps are the actual
filled prefixes and their canonical mapping-out functions. It contains no
new driver, capacity clock, forward solution or chart-gap estimate.

The union identity, closed-hull clearance and boundary identifications in this
structure are not proved here. They are the precise remaining mathematical
input. Aux. 8 and all consequences of those obligations are proved separately.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.RLC.G8Det

/-- The filled prefix of the first curve. -/
def ownHull (α : ℝ≥0 → ℂ) (a : ℝ≥0) : Set ℂ := fillH (α '' Icc 0 a)

/-- The joint filled prefix. -/
def jointHull (α β : ℝ≥0 → ℂ) (u r : ℝ≥0) : Set ℂ := fillH (Restart.prefixSet α u β r)

/-- The hydrodynamic chart at the original first-curve cut. -/
def cutMap (α : ℝ≥0 → ℂ) (a : ℝ≥0) : ℂ → ℂ := ConformalImage.mapOut (ownHull α a)

/-- The original driver after the cut, in its uncentered cut coordinates. -/
def cutDrive (w : ℝ≥0 → ℝ) (a : ℝ≥0) (t : ℝ) : ℝ := w ((a : ℝ) + t).toNNReal

/-- The additional retained hull in the cut chart. In particular it includes
any pockets created by the union, rather than just the image of the β trace. -/
def cutObstacle (α β : ℝ≥0 → ℂ) (a r : ℝ≥0) : Set ℂ :=
  cutMap α a '' (jointHull α β a r \ ownHull α a)

/-- Map out that additional retained hull. -/
def obstacleMap (α β : ℝ≥0 → ℂ) (a r : ℝ≥0) : ℂ → ℂ :=
  ConformalImage.mapOut (cutObstacle α β a r)

theorem domain_eq {α β : ℝ≥0 → ℂ} (hcα : Continuous α) (hcβ : Continuous β) (u r : ℝ≥0) :
    activeDomain α u β r = H \ jointHull α β u r :=
  Restart.activeDomain_eq ((isCompact_Icc.image hcα).union (isCompact_Icc.image hcβ)).isClosed

theorem domain_anti {α β : ℝ≥0 → ℂ} (hcα : Continuous α) (hcβ : Continuous β)
    {a u r : ℝ≥0} (hau : a ≤ u) : activeDomain α u β r ⊆ activeDomain α a β r := by
  rw [domain_eq hcα hcβ, domain_eq hcα hcβ]
  exact Supp9D.H_diff_fillH_anti
    (union_subset_union_left _ (image_mono (Icc_subset_Icc_right hau)))

theorem ownHull_subset {α β : ℝ≥0 → ℂ} {a u r : ℝ≥0} (hau : a ≤ u) :
    ownHull α a ⊆ jointHull α β u r :=
  fillH_mono (subset_union_of_subset_left (image_mono (Icc_subset_Icc_right hau)) _)

theorem isHPHull_ownHull {α : ℝ≥0 → ℂ} (hc : Continuous α) (h0 : α 0 = 0) (a : ℝ≥0) :
    IsHPHull (ownHull α a) :=
  Restart.isHPHull_fillH_image hc.continuousOn (by rw [h0]; exact le_refl 0)

theorem isHPHull_jointHull {α β : ℝ≥0 → ℂ} (hcα : Continuous α) (hcβ : Continuous β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (u r : ℝ≥0) : IsHPHull (jointHull α β u r) :=
  Restart.isHPHull_fillH_prefixSet hcα.continuousOn hcβ.continuousOn
    (by rw [hα0]; exact ofReal_im 0) (by rw [hβ0]; exact ofReal_im 0)

theorem isHPHull_cutObstacle {α β : ℝ≥0 → ℂ} (hcα : Continuous α) (hcβ : Continuous β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (a r : ℝ≥0) : IsHPHull (cutObstacle α β a r) :=
  (ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcα hα0 a)).isHPHull_image
    (isHPHull_ownHull hcα hα0 a) (isHPHull_jointHull hcα hcβ hα0 hβ0 a r) (ownHull_subset le_rfl)

/-- The remaining late-cut obligations, entirely in the original driver and
the canonical cut maps. `left` is the retained β tip and `right` is `1`.
The strict order is the cut-time instance of Aux. 85. -/
structure LateCutGeometry (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) where
  cut : ℝ≥0
  cut_lt : cut < σ
  seed : ℝ
  left : ℝ
  right : ℝ
  seed_limit : Tendsto (obstacleMap α β cut r) (𝓝[H] (cutDrive w cut 0 : ℂ)) (𝓝 (seed : ℂ))
  left_lt_seed : left < seed
  seed_lt_right : seed < right
  hull_union : ∀ u ∈ Icc cut σ,
    cutMap α cut '' (jointHull α β u r \ ownHull α cut) =
      cutObstacle α β cut r ∪ fwdHull (cutDrive w cut) ((u : ℝ) - cut)
  clearance : Disjoint (closure (cutObstacle α β cut r))
    (closure (fwdHull (cutDrive w cut) ((σ : ℝ) - cut)))
  left_limit : Tendsto (obstacleMap α β cut r ∘ cutMap α cut)
    (𝓝[activeDomain α cut β r] (β r)) (𝓝[H] (left : ℂ))
  right_limit : Tendsto (obstacleMap α β cut r ∘ cutMap α cut)
    (𝓝[activeDomain α cut β r] 1) (𝓝[H] (right : ℂ))
  left_avoids : (left : ℂ) ∉ closure
    (obstacleMap α β cut r '' fwdHull (cutDrive w cut) ((σ : ℝ) - cut))
  right_avoids : ∀ t ∈ Ico 0 ((σ : ℝ) - cut), (right : ℂ) ∉ closure
    (obstacleMap α β cut r '' fwdHull (cutDrive w cut) t)
  right_filled : ∃ δ > 0, ∀ z : ℂ, z ∈ H → ‖z - right‖ < δ →
    z ∈ obstacleMap α β cut r '' fwdHull (cutDrive w cut) ((σ : ℝ) - cut)
  tip_limit : ∀ u ∈ Ioo cut σ,
    Tendsto (fun z => fwdMap (cutDrive w cut) ((u : ℝ) - cut) (cutMap α cut z) +
      cutDrive w cut ((u : ℝ) - cut))
      (𝓝[activeDomain α u β r] (α u)) (𝓝[H] (cutDrive w cut ((u : ℝ) - cut) : ℂ))

namespace LateCutGeometry

variable {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {σ r : ℝ≥0}
variable (d : LateCutGeometry α β w σ r)

theorem time_pos : 0 < (σ : ℝ) - d.cut := sub_pos.2 (by exact_mod_cast d.cut_lt)

theorem continuous_cutDrive (hw : Continuous w) : Continuous (cutDrive w d.cut) :=
  hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))

/-- The original chart sends each later physical domain into the complement
of the obstacle and restarted hull. -/
theorem mapsTo_cut (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    {u : ℝ≥0} (hu : u ∈ Icc d.cut σ) :
    MapsTo (cutMap α d.cut) (H \ jointHull α β u r)
      (H \ (cutObstacle α β d.cut r ∪ fwdHull (cutDrive w d.cut) ((u : ℝ) - d.cut))) := by
  have hK := isHPHull_ownHull hcα hα0 d.cut
  have hB := isHPHull_jointHull hcα hcβ hα0 hβ0 u r
  have hg : IsMapOut (ownHull α d.cut) (cutMap α d.cut) := ConformalImage.isMapOut_mapOut hK
  rw [← d.hull_union u hu, hg.H_diff_image (ownHull_subset hu.1) hB.1]
  exact fun z hz => ⟨z, hz, rfl⟩

end LateCutGeometry
end InteractingSLE.RLC.G8Det
