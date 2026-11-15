/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeDetAssembly

/-!
# Recovering a wall interval from its two endpoints

Continuation of PROVE-POCKETSHAPE. Connectedness of the closed piece fills the interval
between its endpoints; connectedness after deleting both endpoints excludes any extension
beyond that interval. No boundary orientation or shape-existence input is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.PocketShapeFin

/-- A connected piece of an embedded ray, connected after deleting its two endpoints,
is exactly the interval between those endpoints. -/
theorem eq_image_Icc_of_connected_endpoints {α : ℝ≥0 → ℂ}
    (hα : Topology.IsEmbedding α) {A : Set ℂ} (hA : A ⊆ range α)
    (hc : IsPreconnected A) {s u : ℝ≥0} (hsu : s < u)
    (hs : α s ∈ A) (hu : α u ∈ A)
    (hpunct : IsPreconnected (A \ {α s, α u})) : A = α '' Icc s u := by
  have hT : IsPreconnected (α ⁻¹' A) := by
    rw [← hα.isInducing.isPreconnected_image, image_preimage_eq_of_subset hA]
    exact hc
  have hP : IsPreconnected (α ⁻¹' (A \ {α s, α u})) := by
    rw [← hα.isInducing.isPreconnected_image,
      image_preimage_eq_of_subset (sdiff_subset.trans hA)]
    exact hpunct
  obtain ⟨m, hsm, hmu⟩ := exists_between hsu
  have hm : α m ∈ A := hT.Icc_subset hs hu ⟨hsm.le, hmu.le⟩
  have hmP : m ∈ α ⁻¹' (A \ {α s, α u}) :=
    ⟨hm, fun he => by
      rcases he with he | he
      · exact hsm.ne' (hα.injective he)
      · exact hmu.ne (hα.injective he)⟩
  apply Subset.antisymm
  · intro z hz
    obtain ⟨r, rfl⟩ := hA hz
    refine ⟨r, ⟨le_of_not_gt ?_, le_of_not_gt ?_⟩, rfl⟩
    · intro hrs
      have hrP : r ∈ α ⁻¹' (A \ {α s, α u}) :=
        ⟨hz, fun he => by
          rcases he with he | he
          · exact hrs.ne (hα.injective he)
          · exact (hrs.trans hsu).ne (hα.injective he)⟩
      exact (hP.Icc_subset hrP hmP ⟨hrs.le, hsm.le⟩).2 (Or.inl rfl)
    · intro hur
      have hrP : r ∈ α ⁻¹' (A \ {α s, α u}) :=
        ⟨hz, fun he => by
          rcases he with he | he
          · exact (hsu.trans hur).ne' (hα.injective he)
          · exact hur.ne' (hα.injective he)⟩
      exact (hP.Icc_subset hmP hrP ⟨hmu.le, hur.le⟩).2 (Or.inr rfl)
  · rintro _ ⟨r, hr, rfl⟩
    exact hT.Icc_subset hs hu hr

end InteractingSLE.Theorem14.PocketShapeFin
