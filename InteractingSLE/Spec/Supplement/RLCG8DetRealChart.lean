/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRealCollar
import InteractingSLE.Foundations.Loewner.YuanCorollary13

/-! # G8: the continuous inverse of the original cut chart -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.RLC.G8Det.RealBoundary

/-- The continuous inverse of the uncentered cut map. -/
def cutInv (w : ℝ≥0 → ℝ) (a : ℝ≥0) (z : ℂ) : ℂ :=
  trMap (fun s : ℝ => w s.toNNReal) 0 a (z - w a)

/-- The actual remaining trace in uncentered cut coordinates. -/
def cutTrace (w : ℝ≥0 → ℝ) (a : ℝ≥0) (t : ℝ) : ℂ :=
  loewnerTip (QuantumZipper.RS.shiftDrive (fun s : ℝ => w s.toNNReal) a) t + w a

variable {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}

theorem continuousOn_cutInv (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) (a : ℝ≥0) : ContinuousOn (cutInv w a) Hbar := by
  apply (YuanSimpleApprox.trMap_continuousOn (isLoewnerTrace_of_isGeneratingTrace hgen)
    (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) le_rfl a.2).comp
      (continuous_id.sub continuous_const).continuousOn
  intro z hz
  simpa only [Hbar, mem_ofPred_eq, Pi.sub_apply, id_eq, sub_im, ofReal_im, sub_zero] using hz

theorem cutInv_mem_domain (hcα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a : ℝ≥0} {z : ℂ} (hz : z ∈ H) :
    cutInv w a z ∈ H \ ownHull α a := by
  rw [Late.ownHull_eq_fwdHull hcα hgen]
  exact Sec6.trMap_zero_mem_domain (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) a.2 (Restart.sub_ofReal_mem_H hz (w a))

theorem cutMap_cutInv (hcα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a : ℝ≥0} {z : ℂ} (hz : z ∈ H) :
    cutMap α a (cutInv w a z) = z := by
  rw [Late.cutMap_eq_original hcα hw hw0 hgen a (cutInv_mem_domain hcα hw hw0 hgen hz)]
  dsimp only [cutInv]
  calc
    _ = (z - w a) + w a := congrArg (fun v : ℂ => v + w a)
      (Sec6.fwdMap_trMap_zero (hw.comp continuous_real_toNNReal)
        (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) a.2
        (Restart.sub_ofReal_mem_H hz (w a)))
    _ = z := sub_add_cancel _ _

theorem cutInv_cutMap (hcα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a : ℝ≥0} {z : ℂ} (hz : z ∈ H \ ownHull α a) :
    cutInv w a (cutMap α a z) = z := by
  rw [Late.cutMap_eq_original hcα hw hw0 hgen a hz]
  dsimp only [cutInv]
  rw [add_sub_cancel_right]
  apply Sec6.trMap_zero_fwdMap (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) a.2
  rwa [Late.ownHull_eq_fwdHull hcα hgen] at hz

theorem cutInv_mem_joint (hcα : Continuous α)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a r : ℝ≥0} {z : ℂ} (hz : z ∈ cutObstacle α β a r) :
    cutInv w a z ∈ jointHull α β a r := by
  obtain ⟨p, hp, rfl⟩ := hz
  rw [cutInv_cutMap hcα hw hw0 hgen ⟨fillH_subset_H _ hp.1, hp.2⟩]
  exact hp.1

theorem cutInv_mem_joint_domain (hcα : Continuous α) (hcβ : Continuous β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a r : ℝ≥0} {z : ℂ} (hz : z ∈ H \ cutObstacle α β a r) :
    cutInv w a z ∈ activeDomain α a β r := by
  rw [domain_eq hcα hcβ]
  refine ⟨(cutInv_mem_domain hcα hw hw0 hgen hz.1).1, fun hp => ?_⟩
  exact hz.2 ⟨cutInv w a z, ⟨hp, (cutInv_mem_domain hcα hw hw0 hgen hz.1).2⟩,
    cutMap_cutInv hcα hw hw0 hgen hz.1⟩

/-- The upper frontier of the additional image hull comes entirely from beta.
The old alpha trace has already been mapped out. -/
theorem cutInv_upper_frontier_mem_beta (hcα : Continuous α) (hcβ : Continuous β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a r : ℝ≥0} {z : ℂ} (hz : z ∈ cutObstacle α β a r)
    (hzcl : z ∈ closure (H \ cutObstacle α β a r)) : cutInv w a z ∈ β '' Icc 0 r := by
  have hzH : z ∈ H := by
    obtain ⟨p, hp, rfl⟩ := hz
    exact (ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcα hgen.1 a)).1.2.mapsTo
      ⟨fillH_subset_H _ hp.1, hp.2⟩
  have hcl : cutInv w a z ∈ closure (activeDomain α a β r) := by
    have him : cutInv w a '' (H \ cutObstacle α β a r) ⊆ activeDomain α a β r :=
      image_subset_iff.2 (fun _ hp => cutInv_mem_joint_domain hcα hcβ hw hw0 hgen hp)
    apply closure_mono him
    exact ((continuousOn_cutInv hw hw0 hgen a z (H_subset_Hbar hzH)).mono
      (fun _ hp => H_subset_Hbar hp.1)).mem_closure_image hzcl
  rw [domain_eq hcα hcβ] at hcl
  have hp := mem_closure_of_mem_fillH_of_mem_closure (cutInv_mem_joint hcα hw hw0 hgen hz) hcl
  change cutInv w a z ∈ closure (α '' Icc 0 a ∪ β '' Icc 0 r) at hp
  rw [((isCompact_Icc.image hcα).union (isCompact_Icc.image hcβ)).isClosed.closure_eq] at hp
  rcases hp with hpα | hpβ
  · exact False.elim ((cutInv_mem_domain hcα hw hw0 hgen hzH).2
      (mem_fillH_of_mem_closure (cutInv_mem_domain hcα hw hw0 hgen hzH).1 (subset_closure hpα)))
  · exact hpβ

end InteractingSLE.RLC.G8Det.RealBoundary
