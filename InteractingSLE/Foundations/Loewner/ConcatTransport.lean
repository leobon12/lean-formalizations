import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# Transport of the unbounded component at a Loewner concatenation

The prefix map identifies the complement of the filled joined path with the image of the
complement of the filled continuation. This is a deterministic component argument.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.LoewnerConcat

/-- Transport the unbounded component when the new path in the prefix domain is the image
of a path in the half-plane. The displacement bounds preserve unboundedness in both directions. -/
theorem compl_fillH_eq_image {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {a : ℝ} (ha : 0 ≤ a) {A B P : Set ℂ}
    (hA : fwdHull W a = fillH A) (hAP : A ⊆ P)
    (hB : IsCompact B) (hP : IsCompact P)
    (hPB : P ∩ (H \ fwdHull W a) = fwdMapInv W a '' (B ∩ H)) :
    H \ fillH P = fwdMapInv W a '' (H \ fillH B) := by
  let F := fwdMapInv W a
  let G := fwdMap W a
  let D := H \ fwdHull W a
  have hFD : ∀ w ∈ H, F w ∈ D := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha hw
  have hFG : ∀ z ∈ D, F (G z) = z := fun z hz =>
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ha hz
  have hGH : MapsTo G D H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha
  have hFc : ContinuousOn F H := continuousOn_fwdMapInv hW hW0 ha
  have hGc : ContinuousOn G D :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ha).continuousOn
  have hFi : InjOn F H := (isConformalBijection_fwdMapInv hW hW0 ha).2.injOn
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ha
  have hPD : H \ fillH P ⊆ D := by
    intro z hz
    exact ⟨hz.1, fun hzK => hz.2 (fillH_mono hAP (hA ▸ hzK))⟩
  have hpc (S : Set ℂ) (hS : Bornology.IsBounded S) : IsPreconnected (H \ fillH S) := by
    obtain ⟨R, hR, hSR⟩ := exists_closure_subset_ball hS
    rw [H_diff_fillH hR hSR]
    exact isPreconnected_connectedComponentIn
  have hforward : F '' (H \ fillH B) ⊆ H \ fillH P := by
    apply subset_H_diff_fillH_of_isPreconnected hP.isBounded
    · exact (hpc B hB.isBounded).image F (hFc.mono sdiff_subset)
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨(hFD w hw.1).1, ?_⟩
      rw [hP.isClosed.closure_eq]
      intro hp
      have hp' : F w ∈ P ∩ D := ⟨hp, hFD w hw.1⟩
      rw [hPB] at hp'
      obtain ⟨v, hv, heq⟩ := hp'
      have hvw : v = w := hFi hv.2 hw.1 heq
      exact hw.2 ⟨hw.1, Or.inl (subset_closure (hvw ▸ hv.1))⟩
    · exact not_isBounded_image_of_norm_sub_le (not_isBounded_H_diff_fillH hB.isBounded)
        (fun w hw => hC w hw.1)
  have hback : G '' (H \ fillH P) ⊆ H \ fillH B := by
    apply subset_H_diff_fillH_of_isPreconnected hB.isBounded
    · exact (hpc P hP.isBounded).image G (hGc.mono hPD)
    · rintro _ ⟨z, hz, rfl⟩
      have hzD := hPD hz
      refine ⟨hGH hzD, ?_⟩
      rw [hB.isClosed.closure_eq]
      intro hb
      have hp : F (G z) ∈ P ∩ D := by
        rw [hPB]
        exact ⟨G z, ⟨hb, hGH hzD⟩, rfl⟩
      rw [hFG z hzD] at hp
      exact hz.2 ⟨hz.1, Or.inl (subset_closure hp.1)⟩
    · apply not_isBounded_image_of_norm_sub_le (not_isBounded_H_diff_fillH hP.isBounded)
      intro z hz
      have h := hC (G z) (hGH (hPD hz))
      change ‖F (G z) - G z‖ ≤ C at h
      rw [hFG z (hPD hz), norm_sub_rev] at h
      exact h
  exact Subset.antisymm (fun z hz => ⟨G z, hback ⟨z, hz, rfl⟩, hFG z (hPD hz)⟩)
    hforward

end InteractingSLE.LoewnerConcat
