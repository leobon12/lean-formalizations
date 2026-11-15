/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonHull

/-!
# Physical hull models for finite chart operations

The hull after a stage is the old hull together with the inverse image of
the stage hull. Its normalized mapping-out map follows from the existing
composition and real-translation theorems for compact half-plane hulls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.WalkIntCanon

def hullModel_id : HullModel Chart.id where
  hull := ∅
  shift := 0
  isHull := isHPHull_empty
  dom_eq := by simpa using WalkNorm.coe_dom_id
  mapOut := by
    convert isMapOut_empty_id using 1
    funext z
    simp [Chart.id]

def HullModel.recenter {c : Chart} (M : HullModel c) (a : ℝ) :
    HullModel (c.recenter a) where
  hull := M.hull
  shift := M.shift + a
  isHull := M.isHull
  dom_eq := by rw [WalkSide.dom_recenter]; exact M.dom_eq
  mapOut := by
    have he : (fun z => (c.recenter a).1 z + ((M.shift + a : ℝ) : ℂ)) =
        fun z => c.1 z + (M.shift : ℂ) := by
      funext z
      change c.1 z - (a : ℂ) + ((M.shift + a : ℝ) : ℂ) = _
      push_cast
      ring
    rw [he]
    exact M.mapOut

/-- The inverse image of a stage complement is the complement of the
physical union hull. -/
theorem HullModel.image_inv_diff {c : Chart} (M : HullModel c)
    (hc : c.IsConformal) {J : Set ℂ} (hJ : J ⊆ H) :
    c.2.1 '' (H \ J) = H \ (M.hull ∪ c.2.1 '' J) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hd := hc.inv_mem_dom hw.1
    have hd' : c.2.1 w ∈ H \ M.hull := by rwa [← M.dom_eq]
    refine ⟨hd'.1, ?_⟩
    rintro (hz | ⟨u, hu, he⟩)
    · exact hd'.2 hz
    · exact hw.2 (hc.injOn (hJ hu) hw.1 he ▸ hu)
  · intro hz
    have hd : z ∈ c.dom := by
      change z ∈ (c.dom : Set ℂ)
      rw [M.dom_eq]
      exact ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
    refine ⟨c.1 z, ⟨hc.fwd_mem hd, ?_⟩, hc.inv_fwd hd⟩
    exact fun h => hz.2 (Or.inr ⟨c.1 z, h, hc.inv_fwd hd⟩)

def HullModel.loewner {c : Chart} (M : HullModel c) (h : IsNormalized c)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    HullModel (c.loewner W t) := by
  let K := M.hull ∪ c.2.1 '' fwdHull W t
  have hJ := isHPHull_fwdHull hW ht
  have hdom : ((c.loewner W t).dom : Set ℂ) = H \ K := by
    rw [(h.conformal.loewner hW hW0 ht).coe_dom]
    change (fun z => c.2.1 (fwdMapInv W t z)) '' H = H \ K
    rw [← image_image, QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht]
    exact M.image_inv_diff h.conformal hJ.1
  have hK : IsHPHull K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro z (hz | ⟨w, hw, rfl⟩)
      · exact M.isHull.1 hz
      · exact h.conformal.2.1 (hJ.1 hw)
    · refine M.isHull.2.1.union ?_
      obtain ⟨B, hB⟩ := h.inverse_bound
      obtain ⟨R, hR⟩ := hJ.2.1.exists_norm_le
      refine isBounded_iff_forall_norm_le.2 ⟨R + B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (norm_le_norm_add_norm_sub' (c.2.1 z) z).trans
        (add_le_add (hR z hz) (hB z (hJ.1 hz)))
    · rw [← hdom]
      exact (c.loewner W t).dom.isOpen
    · rw [← hdom]
      exact isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
        (h.conformal.loewner hW hW0 ht).isConformalBijection
        (by simpa using isHPHull_empty.2.2.2)
  refine ⟨K, M.shift + W t, hK, hdom, ?_⟩
  have himage : (fun z => c.1 z + (M.shift : ℂ)) '' (K \ M.hull) =
      (fun z => z + (M.shift : ℂ)) '' fwdHull W t := by
    ext z
    constructor
    · rintro ⟨w, ⟨hw | ⟨u, hu, rfl⟩, hn⟩, rfl⟩
      · exact (hn hw).elim
      · exact ⟨u, hu, by dsimp only; rw [h.conformal.2.2 _ (hJ.1 hu)]⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨c.2.1 u, ⟨Or.inr ⟨u, hu, rfl⟩, ?_⟩, ?_⟩
      · have hd := h.conformal.inv_mem_dom (hJ.1 hu)
        change c.2.1 u ∈ (c.dom : Set ℂ) at hd
        rw [M.dom_eq] at hd
        exact hd.2
      · dsimp only
        rw [h.conformal.2.2 _ (hJ.1 hu)]
  have htrans : IsMapOut
      ((fun z => c.1 z + (M.shift : ℂ)) '' (K \ M.hull))
      (fun z => fwdMap W t (z - M.shift) + W t + M.shift) := by
    rw [himage]
    exact Sec7.ReverseArc.isMapOut_translate (isMapOut_fwdMap hW hW0 ht) M.shift
  have hg := M.mapOut.comp M.isHull hK subset_union_left htrans
  convert hg using 1
  funext z
  simp only [Chart.loewner, Function.comp_apply, add_sub_cancel_right, ofReal_add]
  ring

end InteractingSLE.Theorem14.WalkIntCanon
