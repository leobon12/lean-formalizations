import HigherDimLQGMetric.Routing.Lemma41Traverse

/-! The trimmed witness and its affine reparameterization have the same image. -/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace HigherDimLQGMetric

theorem lemma41_affine_marked_image {X : Type*} (γ : ℝ → X) {s t : ℝ} (hst : s < t) :
    (fun r : ℝ => γ (s + (t - s) * r)) '' Icc (0 : ℝ) 1 = γ '' Icc s t := by
  let φ : ℝ → ℝ := fun r => s + (t - s) * r
  have hφc : Continuous φ := continuous_const.add (continuous_const.mul continuous_id)
  have hφm : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    dsimp [φ]
    simpa only [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hab (sub_pos.mpr hst).le) s)
  have himg : φ '' Icc (0 : ℝ) 1 = Icc s t := by
    have h := hφc.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) hφm
    convert h using 1
    · simp [φ]
  change (γ ∘ φ) '' Icc (0 : ℝ) 1 = γ '' Icc s t
  rw [image_comp, himg]

theorem lemma41_affine_marked_interior {X : Type*} (γ : ℝ → X) {s t : ℝ}
    (hst : s < t) :
    (fun r : ℝ => γ (s + (t - s) * r)) '' Ioo (0 : ℝ) 1 = γ '' Ioo s t := by
  let φ : ℝ → ℝ := fun r => s + (t - s) * r
  have hφc : Continuous φ := continuous_const.add (continuous_const.mul continuous_id)
  have hφm : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    dsimp [φ]
    simpa only [add_comm] using
      (add_lt_add_left (mul_lt_mul_of_pos_left hab (sub_pos.mpr hst)) s)
  have himg : φ '' Ioo (0 : ℝ) 1 = Ioo s t := by
    have h := hφc.continuousOn.image_Ioo_of_strictMonoOn
      (by norm_num : (0 : ℝ) ≤ 1) hφm
    convert h using 1
    · simp [φ]
  change (γ ∘ φ) '' Ioo (0 : ℝ) 1 = γ '' Ioo s t
  rw [image_comp, himg]

theorem lemma41_split_arc_image {X : Type*} (γ : ℝ → X) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    γ '' Icc (0 : ℝ) 1 =
      (γ '' Icc 0 s) ∪ (γ '' Icc s t) ∪ (γ '' Icc t 1) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases le_total u s with hus | hsu
    · exact Or.inl (Or.inl ⟨u, ⟨hu.1, hus⟩, rfl⟩)
    · rcases le_total u t with hut | htu
      · exact Or.inl (Or.inr ⟨u, ⟨hsu, hut⟩, rfl⟩)
      · exact Or.inr ⟨u, ⟨htu, hu.2⟩, rfl⟩
  · rintro ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    · exact ⟨u, ⟨hu.1, hu.2.trans (hst.trans ht)⟩, rfl⟩
    · exact ⟨u, ⟨hs.trans hu.1, hu.2.trans ht⟩, rfl⟩
    · exact ⟨u, ⟨hs.trans (hst.trans hu.1), hu.2⟩, rfl⟩

end HigherDimLQGMetric
