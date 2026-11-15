/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLatePhysical
import InteractingSLE.Foundations.Loewner.ConformalImageFullAux8

/-!
# G8: the original tip limit and the relative seed boundary value

Packet PROVE-G8-DET. The landed simple-trace boundary theorem gives the tip
limit, and the flow property identifies the two consecutive original maps.
Closed restriction clearance gives the seed value by Schwarz reflection.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.RLC.G8Det.Late

theorem cutMap_eq_original {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hc : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    (a : ℝ≥0) : EqOn (cutMap α a)
      (fun z => fwdMap (fun s : ℝ => w s.toNNReal) a z + w a) (H \ ownHull α a) := by
  have hK := isHPHull_ownHull hc hgen.1 a
  apply (ConformalImage.isMapOut_mapOut hK).eqOn hK
  rw [ownHull_eq_fwdHull hc hgen]
  simpa only [Function.comp_apply, Real.toNNReal_coe] using
    isMapOut_fwdMap (W := fun s : ℝ => w s.toNNReal) (hw.comp continuous_real_toNNReal)
      (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) a.coe_nonneg

/-- The original centered map tends to zero at its interior simple tip. -/
theorem tendsto_own_tip {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hi : Function.Injective α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {u : ℝ≥0} (huH : α u ∈ H) :
    Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) u)
      (𝓝[H \ ownHull α u] (α u)) (𝓝 0) := by
  have hu0 : 0 < u := by
    by_contra h
    have hu : u = 0 := le_antisymm (not_lt.1 h) zero_le
    rw [hu, hgen.1] at huH
    exact lt_irrefl 0 (show 0 < (0 : ℂ).im from huH)
  exact (Sec7.ReverseArc.isChart hgen hw.continuousOn hw0 hi.injOn ENNReal.coe_lt_top hu0).tendsto_tip huH

theorem domain_subset_own {α β : ℝ≥0 → ℂ} (hcα : Continuous α) (hcβ : Continuous β) (u r : ℝ≥0) :
    activeDomain α u β r ⊆ H \ ownHull α u := by
  rw [domain_eq hcα hcβ]
  exact sdiff_subset_sdiff_right (ownHull_subset le_rfl)

/-- The two original forward maps agree with the original map at the later
time, on the current joint domain. -/
theorem old_chain_eq {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a u r : ℝ≥0} (hau : a ≤ u) :
    EqOn (fun z => fwdMap (cutDrive w a) ((u : ℝ) - a) (cutMap α a z) +
        cutDrive w a ((u : ℝ) - a))
      (fun z => fwdMap (fun s : ℝ => w s.toNNReal) u z + w u) (activeDomain α u β r) := by
  intro z hz
  let W : ℝ → ℝ := fun s => w s.toNNReal
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hzU := domain_subset_own hcα hcβ u r hz
  have hzA : z ∈ H \ ownHull α a :=
    ⟨hzU.1, fun h => hzU.2 (fillH_mono (image_mono (Icc_subset_Icc_right hau)) h)⟩
  have hflow : ∃ v, QuantumZipper.IsForwardSol W z ((a : ℝ) + ((u : ℝ) - a)) v := by
    rw [add_sub_cancel]
    apply QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull u.coe_nonneg hzU.1
    rw [← ownHull_eq_fwdHull hcα hgen]
    exact hzU.2
  have he := QuantumZipper.fwdMap_add hW hzU.1 a.coe_nonneg
    (sub_nonneg.2 (show (a : ℝ) ≤ u by exact_mod_cast hau)) hflow
  rw [add_sub_cancel] at he
  change fwdMap (cutDrive w a) ((u : ℝ) - a) (cutMap α a z) +
    cutDrive w a ((u : ℝ) - a) = fwdMap W u z + w u
  rw [cutMap_eq_original hcα hw hw0 hgen a hzA]
  have hdrive : cutDrive w a = fun t => (W ((a : ℝ) + t) - W a) + W a :=
    funext fun t => (sub_add_cancel _ _).symm
  rw [show w a = W a from by simp only [W, Real.toNNReal_coe], hdrive,
    ConformalImageFull.fwdMap_add_const, add_sub_cancel_right, ← he]
  congr 1
  simp only [sub_add_cancel, add_sub_cancel, W, Real.toNNReal_coe]

/-- The tip limit appearing in `LateCutGeometry` follows from simplicity and
the original generating trace; it is not a further restriction hypothesis. -/
theorem tip_limit {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hi : Function.Injective α)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a u r : ℝ≥0} (hau : a ≤ u) (huH : α u ∈ H) :
    Tendsto (fun z => fwdMap (cutDrive w a) ((u : ℝ) - a) (cutMap α a z) +
      cutDrive w a ((u : ℝ) - a)) (𝓝[activeDomain α u β r] (α u))
      (𝓝[H] (cutDrive w a ((u : ℝ) - a) : ℂ)) := by
  have hc := (tendsto_own_tip hi hw hw0 hgen huH).mono_left
    (nhdsWithin_mono _ (domain_subset_own hcα hcβ u r))
  have hlim := hc.add_const (w u : ℂ)
  rw [zero_add] at hlim
  have he := old_chain_eq hcα hcβ hw hw0 hgen hau (r := r)
  have hval : cutDrive w a ((u : ℝ) - a) = w u := by
    simp only [cutDrive, add_sub_cancel, Real.toNNReal_coe]
  rw [hval] at he ⊢
  refine tendsto_nhdsWithin_iff.2 ⟨hlim.congr'
    (eventually_mem_nhdsWithin.mono fun z hz => (he hz).symm), ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  have hez := he hz
  dsimp only at hez
  rw [hez]
  have hmap := (isMapOut_fwdMap (W := fun s : ℝ => w s.toNNReal) (hw.comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) u.coe_nonneg).1.2.mapsTo
  have hzU := domain_subset_own hcα hcβ u r hz
  rw [ownHull_eq_fwdHull hcα hgen] at hzU
  simpa only [Function.comp_apply, Real.toNNReal_coe] using hmap hzU

/-- At a real point outside the closed obstacle, the mapping-out boundary
value exists and is real. -/
theorem exists_real_boundary_value {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ}
    (hφ : IsMapOut A φ) {y : ℝ} (hy : (y : ℂ) ∉ closure A) :
    ∃ c : ℝ, Tendsto φ (𝓝[H] (y : ℂ)) (𝓝 (c : ℂ)) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hy
  have hd : Disjoint (ball (y : ℂ) δ) A :=
    Set.disjoint_left.2 fun z hz hzA => hsub hz (subset_closure hzA)
  obtain ⟨him, hlim⟩ := hφ.tendsto_limUnder_of_disjoint hA hδ hd
  exact ⟨_, by rwa [Restart.ofReal_re_eq him]⟩

end InteractingSLE.RLC.G8Det.Late
