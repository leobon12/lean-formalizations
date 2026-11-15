/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonModel
import InteractingSLE.Foundations.Loewner.TraceClose
import InteractingSLE.Foundations.Loewner.ConformalImageLoewner
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Spec.Supplement.SBLwChart

/-!
# The hull after a piece, at its lifetime, by capacity (the terminal hull identity of the step `ℓ → ℓ + 2`)

Packet REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8: the step from the retained law at stage `ℓ`
to stage `ℓ + 2`). After B's piece `ℓ` the retained hull is the old hull together with the pull-back, through the
stage chart `c`, of the relative Loewner hull at the piece's relative lifetime `T`:
`fill(A ∪ B_{<ℓ+2}) = fill(A ∪ B_{<ℓ}) ∪ c⁻¹(K_T)`. The relative versions give this identity only at times before the
lifetime. No trace of the relative driver at `T` is available (a good record is only uniformly continuous), so the
identity at `T` is obtained from capacity: the hull model of `c.loewner W t` has capacity `hcap(old) + 2t`
(composition rule), and a hull inside the one at `T` that contains the hulls at a cofinal set of earlier times has at
least its capacity, hence equals it (strict monotonicity of capacity).

* `loewner_hull`: the hull of `HullModel.loewner` (definitional);
* **`hcapSet_loewner_hull`**: `hcap(old ∪ c⁻¹(K_t)) = hcap(old) + 2t`;
* **`loewner_hull_eq_of_cofinal`**: the terminal hull identity from below;
* `fillH_subset_of_inter_H_subset`: the fill of a set whose points in `ℍ` lie in a hull lies in that hull.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.SB.Qw

open WalkIntCanon

/-- The hull of the Loewner step of a hull model: the old hull and the pull-back of the Loewner hull. -/
theorem loewner_hull {c : Chart} (M : HullModel c) (hn : IsNormalized c) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (M.loewner hn hW hW0 ht).hull = M.hull ∪ c.2.1 '' fwdHull W t := rfl

/-- **Capacity of the hull after a Loewner step**: `hcap(old ∪ c⁻¹(K_t)) = hcap(old) + 2t`. -/
theorem hcapSet_loewner_hull {c : Chart} (M : HullModel c) (hn : IsNormalized c) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ConformalImage.hcapSet (M.loewner hn hW hW0 ht).hull = ConformalImage.hcapSet M.hull + 2 * t := by
  have hJ := isHPHull_fwdHull hW ht
  have hX := (M.loewner hn hW hW0 ht).isHull
  rw [loewner_hull] at hX ⊢
  have hsub : M.hull ⊆ M.hull ∪ c.2.1 '' fwdHull W t := subset_union_left
  have hadd := HPHull.hcap_eq_add (A := ⟨M.hull, M.isHull⟩) (B := ⟨_, hX⟩) hsub M.mapOut
  have himage : (fun z => c.1 z + (M.shift : ℂ)) '' ((M.hull ∪ c.2.1 '' fwdHull W t) \ M.hull) =
      affHomeo 1 one_pos M.shift '' fwdHull W t := by
    ext z
    constructor
    · rintro ⟨w, ⟨hw | ⟨u, hu, rfl⟩, hn'⟩, rfl⟩
      · exact (hn' hw).elim
      · refine ⟨u, hu, ?_⟩
        rw [ConformalImageFull.affHomeo_one_apply]
        dsimp only
        rw [hn.conformal.2.2 _ (hJ.1 hu)]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨c.2.1 u, ⟨Or.inr ⟨u, hu, rfl⟩, ?_⟩, ?_⟩
      · have hd := hn.conformal.inv_mem_dom (hJ.1 hu)
        change c.2.1 u ∈ (c.dom : Set ℂ) at hd
        rw [M.dom_eq] at hd
        exact hd.2
      · rw [ConformalImageFull.affHomeo_one_apply]
        dsimp only
        rw [hn.conformal.2.2 _ (hJ.1 hu)]
  have htr := HPHull.hcap_affHomeo (x := M.shift) ⟨_, hJ⟩ one_pos
  have hcongr := HPHull.hcap_congr (A := ⟨_, M.mapOut.isHPHull_image M.isHull hX hsub⟩)
    (B := ⟨_, hJ.image_affHomeo one_pos⟩) himage
  rw [ConformalImage.hcapSet_eq hX, ConformalImage.hcapSet_eq M.isHull, hadd, hcongr, htr]
  have h2 : HPHull.hcap ⟨fwdHull W t, hJ⟩ = 2 * t := hcap_fwdHull hW hW0 ht
  rw [h2]
  ring

/-- **The terminal hull identity from below**: a hull `Z` inside the hull of the Loewner step at `T`, containing the
old hull and the hulls of the steps at a cofinal set of earlier times, is the hull at `T`. -/
theorem loewner_hull_eq_of_cofinal {c : Chart} (M : HullModel c) (hn : IsNormalized c) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {Z : Set ℂ} (hZ : IsHPHull Z)
    (hZT : Z ⊆ (M.loewner hn hW hW0 hT).hull) (hKZ : M.hull ⊆ Z)
    (hcof : ∀ s : ℝ, 0 ≤ s → s < T → ∃ (s' : ℝ) (hs' : 0 ≤ s'), s ≤ s' ∧ (M.loewner hn hW hW0 hs').hull ⊆ Z) :
    Z = (M.loewner hn hW hW0 hT).hull := by
  have hXT := (M.loewner hn hW hW0 hT).isHull
  refine TraceClose.eq_of_subset_of_hcap_le (A := ⟨Z, hZ⟩) (B := ⟨_, hXT⟩) hZT ?_
  have hcapT := hcapSet_loewner_hull M hn hW hW0 hT
  rw [ConformalImage.hcapSet_eq hXT] at hcapT
  change HPHull.hcap ⟨_, hXT⟩ ≤ HPHull.hcap ⟨Z, hZ⟩
  rw [hcapT, ← ConformalImage.hcapSet_eq hZ]
  have hK : ConformalImage.hcapSet M.hull ≤ ConformalImage.hcapSet Z := by
    rw [ConformalImage.hcapSet_eq M.isHull, ConformalImage.hcapSet_eq hZ]
    exact HPHull.hcap_mono (A := ⟨_, M.isHull⟩) (B := ⟨_, hZ⟩) hKZ
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  by_cases hy0 : y ≤ ConformalImage.hcapSet M.hull
  · exact hy0.trans hK
  replace hy0 : ConformalImage.hcapSet M.hull < y := lt_of_not_ge hy0
  set s : ℝ := (y - ConformalImage.hcapSet M.hull) / 2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsT : s < T := by rw [hs]; linarith
  obtain ⟨s', hs'0, hss', hsub⟩ := hcof s hs0 hsT
  have hX' := (M.loewner hn hW hW0 hs'0).isHull
  have hmono : ConformalImage.hcapSet (M.loewner hn hW hW0 hs'0).hull ≤ ConformalImage.hcapSet Z := by
    rw [ConformalImage.hcapSet_eq hX', ConformalImage.hcapSet_eq hZ]
    exact HPHull.hcap_mono (A := ⟨_, hX'⟩) (B := ⟨_, hZ⟩) hsub
  rw [hcapSet_loewner_hull M hn hW hW0 hs'0] at hmono
  rw [hs] at hss'
  linarith

/-- The fill of a set whose points in `ℍ` lie in a hull lies in that hull. -/
theorem fillH_subset_of_inter_H_subset {X S : Set ℂ} (hX : IsHPHull X) (hS : S ∩ H ⊆ X) : fillH S ⊆ X := by
  rw [← Lw.fillH_inter_H' S]
  exact (fillH_mono hS).trans hX.fillH_eq.subset

end InteractingSLE.Theorem14.SB.Qw
