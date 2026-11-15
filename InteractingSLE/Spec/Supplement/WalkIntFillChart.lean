/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillUnion

/-!
# Normalized reference charts of physical compact hulls

Use the existing hydrodynamic mapping-out function, its holomorphic inverse,
and its canonical derivative logarithm. The stored lift then has the exact
zero normalization at imaginary infinity, with no branch hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFill

open WalkIntCanon

/-- Every compact half-plane hull has a physical model with a normalized
chart. No boundary extension or incident-component inclusion is asserted. -/
theorem exists_normalized_hullChart {K : Set ℂ} (hK : IsHPHull K) :
    ∃ (c : Chart) (M : HullModel c), IsNormalized c ∧ M.hull = K := by
  let g := ConformalImage.mapOut K
  have hg : IsMapOut K g := ConformalImage.isMapOut_mapOut hK
  let e := QuantumZipper.CA.univalentOPH hK.isOpen hg.1.1 hg.1.2.injOn
  have himage : g '' (H \ K) = H := hg.1.2.image_eq
  have hmaps : ∀ w ∈ H, e.symm w ∈ H \ K := by
    intro w hw
    apply e.map_target
    change w ∈ (QuantumZipper.CA.univalentOPH hK.isOpen hg.1.1 hg.1.2.injOn).target
    rwa [QuantumZipper.CA.univalentOPH_target, himage]
  have hright : ∀ w ∈ H, g (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hK.isOpen hg.1.1 hg.1.2.injOn
      (himage.symm ▸ hw)
  have hleft : ∀ z ∈ H \ K, e.symm (g z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hK.isOpen hg.1.1 hg.1.2.injOn hz
  let c : Chart := (g, e.symm, fun z => (Restart.canonDerivLog K z).im)
  have hc : c.IsConformal := by
    refine ⟨?_, fun w hw => (hmaps w hw).1, hright⟩
    have hi := QuantumZipper.CA.differentiableOn_univalentOPH_symm hK.isOpen
      hg.1.1 hg.1.2.injOn
    rwa [himage] at hi
  have hdom : (c.dom : Set ℂ) = H \ K := by
    rw [hc.coe_dom]
    refine Subset.antisymm (fun _ ⟨w, hw, he⟩ => he ▸ hmaps w hw) ?_
    intro z hz
    exact ⟨g z, hg.1.2.mapsTo hz, hleft z hz⟩
  have hL := Restart.isCanonicalDerivLog_canonDerivLog hK
  obtain ⟨B, hB⟩ := hg.exists_norm_sub_le hK
  have hinv : ∀ w ∈ H, ‖c.2.1 w - w‖ ≤ B := by
    intro w hw
    have hb := hB _ (hmaps w hw)
    rw [hright w hw, norm_sub_rev] at hb
    exact hb
  have hn : IsNormalized c := by
    refine ⟨hc, ?_, ⟨B, hinv⟩, ?_⟩
    · refine ⟨Restart.canonDerivLog K, ?_, fun _ _ => rfl⟩
      change IsDerivLog g (Restart.canonDerivLog K) (c.dom : Set ℂ)
      rw [hdom]
      exact hL.1
    · have hh := tendsto_highHalfPlane_of_bound hc.2.1 hinv
      have hlim := (tendsto_canonicalLog_of_im_atTop hK hg hL
        tendsto_im_highHalfPlane).comp hh
      exact (continuous_im.tendsto 0 |>.comp hlim)
  refine ⟨c, ⟨K, 0, hK, hdom, ?_⟩, hn, rfl⟩
  simpa only [ofReal_zero, add_zero] using hg

end InteractingSLE.Theorem14.WalkIntFill
