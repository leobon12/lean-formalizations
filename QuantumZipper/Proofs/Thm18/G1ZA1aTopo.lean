import QuantumZipper.Proofs.Thm18.G1ZA1aAff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a (ii), topology of the side components

* `bijOn_cc_of_inv`: mutually inverse maps, continuous on `S'` and `S`, carry the connected
  component of `S'` at `p` bijectively onto the component of `S` at `M p` (mathlib
  `ContinuousOn.mapsTo_connectedComponentIn`).
* `sideDom_eq_cc`: each side component is a connected component of `ℍ \ η` (left:
  `CA.Uniformizer.leftComponent_eq`; right: by the reflection `z ↦ −z̄`).
* `sideDom_nhd`: points of `ℍ` near a real point of the side half-line lie in the side component
  (`CA.Uniformizer.exists_nhd_mem_cc`, reflected for the right side).

Own elementary arguments.
-/

noncomputable section

open Filter Set Complex Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

theorem bijOn_cc_of_inv {S S' : Set ℂ} {M N : ℂ → ℂ} (hMc : ContinuousOn M S')
    (hNc : ContinuousOn N S) (hMS : MapsTo M S' S) (hNS : MapsTo N S S')
    (hNM : ∀ z ∈ S', N (M z) = z) (hMN : ∀ w ∈ S, M (N w) = w) {p : ℂ} (hp : p ∈ S') :
    BijOn M (connectedComponentIn S' p) (connectedComponentIn S (M p)) := by
  have h1 : MapsTo M (connectedComponentIn S' p) (connectedComponentIn S (M p)) := fun z hz =>
    connectedComponentIn_mono _ hMS.image_subset (hMc.mapsTo_connectedComponentIn hp hz)
  have h2 : MapsTo N (connectedComponentIn S (M p)) (connectedComponentIn S' p) := by
    intro w hw
    have := connectedComponentIn_mono _ hNS.image_subset
      (hNc.mapsTo_connectedComponentIn (hMS hp) hw)
    rwa [hNM p hp] at this
  refine ⟨h1, fun z hz w hw h => ?_, fun w hw =>
    ⟨N w, h2 hw, hMN w (connectedComponentIn_subset _ _ hw)⟩⟩
  rw [← hNM z (connectedComponentIn_subset _ _ hz), h, hNM w (connectedComponentIn_subset _ _ hw)]

theorem refl_image_slitH (η : ℝ → ℂ) : refl '' slitH (refl ∘ η) = slitH η := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : refl (refl u) ∈ H \ (refl ∘ η) '' Ici (0 : ℝ) := by rw [refl_refl]; exact hu
    exact refl_mem_slit_iff.1 this
  · intro hw
    exact ⟨refl w, refl_mem_slit_iff.2 hw, refl_refl w⟩

theorem refl_image_slitH' (η : ℝ → ℂ) : refl '' slitH η = slitH (refl ∘ η) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact refl_mem_slit_iff.2 hu
  · intro hw
    refine ⟨refl w, refl_mem_slit_iff.1 ?_, refl_refl w⟩
    rw [refl_refl]; exact hw

theorem sideDom_eq_cc {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    ∃ q : ℂ, sideDom η left = connectedComponentIn (slitH η) q := by
  cases left
  · have hη' := isSimpleChord_refl_comp hη
    refine ⟨refl (zStar (refl ∘ η)), ?_⟩
    show rightComponent η = _
    apply Subset.antisymm
    · intro z hz
      have hL : refl z ∈ connectedComponentIn (slitH (refl ∘ η)) (zStar (refl ∘ η)) := by
        rw [← leftComponent_eq hη']; exact mem_rightComponent_iff.1 hz
      have := continuous_refl.continuousOn.mapsTo_connectedComponentIn
        (connectedComponentIn_nonempty_iff.1 ⟨_, hL⟩) hL
      rwa [refl_refl, refl_image_slitH] at this
    · intro z hz
      rw [mem_rightComponent_iff, leftComponent_eq hη']
      have hq : refl (zStar (refl ∘ η)) ∈ slitH η :=
        connectedComponentIn_nonempty_iff.1 ⟨_, hz⟩
      have := continuous_refl.continuousOn.mapsTo_connectedComponentIn hq hz
      rwa [refl_refl, refl_image_slitH'] at this
  · exact ⟨zStar η, leftComponent_eq hη⟩

theorem sideDom_nhd {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) {x : ℝ}
    (hx : x ∈ g1SideHalf left) :
    ∃ δ > 0, ∀ w ∈ H, dist w (x : ℂ) < δ → w ∈ sideDom η left := by
  cases left
  · have hx' : 0 < x := by simpa [g1SideHalf] using hx
    obtain ⟨δ, hδ, h⟩ := exists_nhd_mem_cc (isSimpleChord_refl_comp hη) (neg_lt_zero.2 hx')
    refine ⟨δ, hδ, fun w hw hd => ?_⟩
    show w ∈ rightComponent η
    rw [mem_rightComponent_iff, leftComponent_eq (isSimpleChord_refl_comp hη)]
    refine h _ (refl_mem_H_iff.2 hw) ?_
    rw [← refl_ofReal x, dist_eq_norm, show refl w - refl (x : ℂ) = refl (w - x) by
      simp only [CA.Uniformizer.refl, map_sub]; ring, norm_refl, ← dist_eq_norm]
    exact hd
  · have hx' : x < 0 := by simpa [g1SideHalf] using hx
    obtain ⟨δ, hδ, h⟩ := exists_nhd_mem_cc hη hx'
    refine ⟨δ, hδ, fun w hw hd => ?_⟩
    show w ∈ leftComponent η
    rw [leftComponent_eq hη]
    exact h w hw hd

end G1ZA1a
end Thm18Asm
end QuantumZipper
