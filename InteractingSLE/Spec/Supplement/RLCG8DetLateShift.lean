/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLateUnion

/-!
# G8: the actual restarted hull and the joint union identity

Packet PROVE-G8-DET. The deterministic domain Markov property identifies the
first curve's remaining hull in its own canonical chart. Combined with the
Janiszewski pullback, closed-hull separation implies `LateCutGeometry.hull_union`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.RLC.G8Det.Late

theorem ownHull_eq_fwdHull {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hc : Continuous α) (hgen : IsGeneratingTrace w ⊤ α) (a : ℝ≥0) :
    ownHull α a = fwdHull (fun s : ℝ => w s.toNNReal) a :=
  ((fillH_eq_iff_isFilling_of_isClosed (isCompact_Icc.image hc).isBounded
    (isCompact_Icc.image hc).isClosed (QuantumZipper.fwdHull_mono.2 _)).1
      (hgen.2.2 a ENNReal.coe_lt_top)).symm

/-- The uncentered original map sends the remaining own hull to the hull
of the original driver read after the cut. -/
theorem image_increment {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    (fun z => fwdMap W a z + W a) '' (fwdHull W (a + s) \ fwdHull W a) =
      fwdHull (fun t => W (a + t)) s := by
  have hD : (fun t => (W (a + t) - W a) + W a) = fun t => W (a + t) :=
    funext fun t => sub_add_cancel _ _
  have htrans := ConformalImageFull.fwdHull_add_const (fun t => W (a + t) - W a) (W a) s
  rw [hD] at htrans
  rw [htrans, QuantumZipper.fwdHull_add_diff hW ha hs]
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨fwdMap W a v, hv.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hvH : v + (W a : ℂ) ∈ H := by
      show 0 < (v + (W a : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using (show 0 < v.im from hv.1)
    obtain ⟨z, hz, he⟩ := (isMapOut_fwdMap hW hW0 ha).1.2.surjOn hvH
    have hzv : fwdMap W a z = v := add_right_cancel he
    exact ⟨z, ⟨hz, hzv ▸ hv⟩, he⟩

/-- The canonical cut map has exactly the restarted own hull as its image. -/
theorem cutMap_image_ownHull {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hc : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a u : ℝ≥0} (hau : a ≤ u) :
    cutMap α a '' (ownHull α u \ ownHull α a) = fwdHull (cutDrive w a) ((u : ℝ) - a) := by
  let W : ℝ → ℝ := fun s => w s.toNNReal
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simpa only [W, Real.toNNReal_zero] using hw0
  have hK := isHPHull_ownHull hc hgen.1 a
  have hg : IsMapOut (ownHull α a) (fun z => fwdMap W a z + W a) := by
    rw [ownHull_eq_fwdHull hc hgen]
    exact isMapOut_fwdMap hW hW0 a.coe_nonneg
  have he := (ConformalImage.isMapOut_mapOut hK).eqOn hK hg
  have himg : cutMap α a '' (ownHull α u \ ownHull α a) =
      (fun z => fwdMap W a z + W a) '' (ownHull α u \ ownHull α a) :=
    image_congr fun z hz => he ⟨fillH_subset_H _ hz.1, hz.2⟩
  rw [himg, ownHull_eq_fwdHull hc hgen u, ownHull_eq_fwdHull hc hgen a]
  have ht : (0 : ℝ) ≤ u - a := sub_nonneg.2 (by exact_mod_cast hau)
  have h := image_increment hW hW0 a.coe_nonneg ht
  rw [add_sub_cancel] at h
  exact h

/-- The union clause of `LateCutGeometry` follows from its separation clause
and the generating property of the original first curve. -/
theorem hull_union_of_clearance {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0}
    (hd : Disjoint (closure (cutObstacle α β a r))
      (closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)))) :
    ∀ u ∈ Icc a σ, cutMap α a '' (jointHull α β u r \ ownHull α a) =
      cutObstacle α β a r ∪ fwdHull (cutDrive w a) ((u : ℝ) - a) := by
  intro u hu
  have hKP := ownHull_subset (α := α) (β := β) (r := r) (a := a) le_rfl
  have hKQ : ownHull α a ⊆ ownHull α u := fillH_mono (image_mono (Icc_subset_Icc_right hu.1))
  have hi := cutMap_image_ownHull hcα hw hw0 hgen hu.1
  have hdu : Disjoint (closure (cutMap α a '' (jointHull α β a r \ ownHull α a)))
      (closure (cutMap α a '' (ownHull α u \ ownHull α a))) := by
    rw [hi]
    exact hd.mono_right (closure_mono ((QuantumZipper.fwdHull_mono (W := cutDrive w a)).1
      (sub_le_sub_right (by exact_mod_cast hu.2) _)))
  have hfill := fillH_union_eq_of_disjoint_images (isHPHull_ownHull hcα hα0 a)
    (isHPHull_jointHull hcα hcβ hα0 hβ0 a r) (isHPHull_ownHull hcα hα0 u)
    hKP hKQ (ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcα hα0 a)) hdu
  have he : Restart.prefixSet α a β r ∪ α '' Icc 0 u = Restart.prefixSet α u β r := by
    apply Subset.antisymm
    · exact union_subset (union_subset_union_left _ (image_mono (Icc_subset_Icc_right hu.1)))
        subset_union_left
    · exact union_subset (subset_union_right) (subset_union_of_subset_left subset_union_right _)
  rw [he] at hfill
  change jointHull α β u r = jointHull α β a r ∪ ownHull α u at hfill
  rw [hfill, union_sdiff_distrib, image_union, hi]
  rfl

end InteractingSLE.RLC.G8Det.Late
