/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRelGeometry

/-!
# G8: boundary identification in the relative Loewner chart

Packet PROVE-G8-DET. From the explicit late-cut geometry, Aux. 8 supplies
the driver and clock. Mapping-out uniqueness and the boundary intertwining
identify the moving first tip; surviving real flows identify retained marks.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap IsForwardSol)

namespace InteractingSLE.RLC.G8Det.LateCutGeometry

variable {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {σ r : ℝ≥0}
variable (d : LateCutGeometry α β w σ r)

/-- Apply Aux. 8 to the actual mapped additional retained hull. -/
theorem exists_image (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) :
    Nonempty (RelativeImage (cutDrive w d.cut) (cutObstacle α β d.cut r)
      (obstacleMap α β d.cut r) ((σ : ℝ) - d.cut)) :=
  exists_relativeImage (d.continuous_cutDrive hw) d.time_pos
    (isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r)
    (ConformalImage.isMapOut_mapOut (isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r)) d.clearance

variable (e : RelativeImage (cutDrive w d.cut) (cutObstacle α β d.cut r)
  (obstacleMap α β d.cut r) ((σ : ℝ) - d.cut))

theorem time_mem {u : ℝ≥0} (hu : u ∈ Icc d.cut σ) :
    (u : ℝ) - d.cut ∈ Icc 0 ((σ : ℝ) - d.cut) :=
  ⟨sub_nonneg.2 (by exact_mod_cast hu.1), sub_le_sub_right (by exact_mod_cast hu.2) _⟩

/-- The canonical physical chart is the relative map after both fixed maps. -/
theorem mapOut_eq (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) {u : ℝ≥0} (hu : u ∈ Icc d.cut σ) :
    EqOn (ConformalImage.mapOut (jointHull α β u r))
      (fun z => fwdMap e.driver (e.clock ((u : ℝ) - d.cut))
        (obstacleMap α β d.cut r (cutMap α d.cut z)) + e.driver (e.clock ((u : ℝ) - d.cut)))
      (activeDomain α u β r) := by
  rw [domain_eq hcα hcβ]
  exact e.mapOut_eq (d.continuous_cutDrive hw) (isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r)
    (ConformalImage.isMapOut_mapOut (isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r)) d.clearance
    (isHPHull_ownHull hcα hα0 d.cut) (isHPHull_jointHull hcα hcβ hα0 hβ0 u r)
    (ownHull_subset hu.1) (ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcα hα0 d.cut))
    (d.time_mem hu) (d.hull_union u hu)

/-- Aux. 8's boundary intertwining gives the first tip's relative driver. -/
theorem mapOut_tip (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) {u : ℝ≥0} (hu : u ∈ Ioo d.cut σ) :
    Tendsto (ConformalImage.mapOut (jointHull α β u r))
      (𝓝[activeDomain α u β r] (α u)) (𝓝 (e.driver (e.clock ((u : ℝ) - d.cut)) : ℂ)) := by
  have ht := d.time_mem ⟨hu.1.le, hu.2.le⟩
  have hV := d.continuous_cutDrive hw
  have hA := isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r
  have hK := isHPHull_fwdHull hV ht.1
  have hdt := d.clearance.mono_right
    (closure_mono ((QuantumZipper.fwdHull_mono (W := cutDrive w d.cut)).1 ht.2))
  have hR := (isMapOut_fwdMap_any hV ht.1).isHPHull_image_of_disjoint_closure hK hA hdt.symm
  obtain ⟨R, hR⟩ := hR.exists_isMapOut
  have haux := e.intertwine _ ht R hR
  have hlim := haux.2.comp (d.tip_limit u hu)
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  have hgz := d.mapsTo_cut hcα hcβ hα0 hβ0 ⟨hu.1.le, hu.2.le⟩
    (domain_eq hcα hcβ u r ▸ hz)
  exact ((d.mapOut_eq e hcα hcβ hα0 hβ0 hw ⟨hu.1.le, hu.2.le⟩ hz).trans
    (haux.1 _ hgz)).symm

/-- Every retained mark with an initial real boundary value has the boundary
value of its relative forward flow while it remains alive. -/
theorem mapOut_passive (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) {u : ℝ≥0} (hu : u ∈ Icc d.cut σ) {p : ℂ} {y : ℝ}
    (hlim : Tendsto (obstacleMap α β d.cut r ∘ cutMap α d.cut)
      (𝓝[activeDomain α d.cut β r] p) (𝓝[H] (y : ℂ)))
    (halive : ∃ v, IsForwardSol e.driver (y : ℂ) (e.clock ((u : ℝ) - d.cut)) v) :
    Tendsto (ConformalImage.mapOut (jointHull α β u r)) (𝓝[activeDomain α u β r] p)
      (𝓝 (fwdMap e.driver (e.clock ((u : ℝ) - d.cut)) y + e.driver (e.clock ((u : ℝ) - d.cut)))) :=
  tendsto_of_passive e.continuous_driver (e.clock_nonneg (d.time_mem hu)) halive
    (hlim.mono_left (nhdsWithin_mono _ (domain_anti hcα hcβ hu.1)))
    (d.mapOut_eq e hcα hcβ hα0 hβ0 hw hu)

theorem driver_zero (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) : e.driver 0 = d.seed :=
  e.driver_zero (d.continuous_cutDrive hw) d.time_pos.le
    (isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r) d.seed_limit
    (ConformalImage.isMapOut_mapOut (isHPHull_cutObstacle hcα hcβ hα0 hβ0 d.cut r))

/-- The old tip survives through the completed relative hull. -/
theorem left_alive (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) :
    ∃ v, IsForwardSol e.driver (d.left : ℂ) (e.clock ((σ : ℝ) - d.cut)) v := by
  refine alive_of_notMem_closure e.continuous_driver ?_ (e.clock_pos d.time_pos).le ?_
  · rw [d.driver_zero e hcα hcβ hα0 hβ0 hw]
    exact d.left_lt_seed.ne
  · rw [e.hull_eq _ ⟨d.time_pos.le, le_rfl⟩]
    exact d.left_avoids

/-- `1` survives before the terminal relative time and dies at that time. -/
theorem right_swallow (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) : RealSwallowAt e.driver d.right (e.clock ((σ : ℝ) - d.cut)) := by
  refine ⟨e.clock_pos d.time_pos, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, he⟩ := e.clock_surj d.time_pos hs
    refine alive_of_notMem_closure e.continuous_driver ?_ hs.1 ?_
    · rw [d.driver_zero e hcα hcβ hα0 hβ0 hw]
      exact d.seed_lt_right.ne'
    · rw [← he, e.hull_eq t ⟨ht.1, ht.2.le⟩]
      exact d.right_avoids t ht
  · refine GB1.not_alive_of_hull e.continuous_driver (e.clock_pos d.time_pos).le ?_
    obtain ⟨δ, hδ, hfill⟩ := d.right_filled
    refine ⟨δ, hδ, fun z hz hdist => ?_⟩
    rw [e.hull_eq _ ⟨d.time_pos.le, le_rfl⟩]
    exact hfill z hz hdist

end InteractingSLE.RLC.G8Det.LateCutGeometry
