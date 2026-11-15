/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketMirrorTopology

/-!
# The sign of a boundary coordinate on either side of a disc crosscut

PROVE-POCKETSHAPE. Apply the existing crosscut winding theorem in disc
coordinates. Reflection gives its lower-side counterpart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology Metric Function
open scoped ComplexConjugate
open QuantumZipper (H Hbar isOpen_H)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.PocketMirror

open WangWu Sec7.PocketJordan InteractingSLE.Orientation

/-- A normalized boundary coordinate is positive on an upper-side marked crosscut arc. -/
theorem re_pos_of_disc_crossSide {α : ℝ → ℂ} (hα : IsDiscCrosscut α)
    {D : Set ℂ} (hDo : IsOpen D) (hDpc : IsPreconnected D) (hDb : D ⊆ ball 0 1)
    (hDα : Disjoint D (crossRange α)) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hI : {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure D} = Icc a b)
    {Ψ : ℂ → ℂ} (hU : IsBdryUniformizer D (α a) (α b) Ψ)
    (hside : D ⊆ crossSide α 1) : ∀ s ∈ Ioo a b, 0 < (Ψ (α s)).re := by
  let C := H ∩ cayley ⁻¹' D
  have hCH : C ⊆ H := inter_subset_left
  have hCo : IsOpen C := (show ContinuousOn cayley H from fun z hz =>
    (QuantumZipper.CA.differentiableAt_cayley
      (Sec7.Lemma71F.add_I_ne_zero_of_mem_H hz)).continuousAt.continuousWithinAt)
      |>.isOpen_inter_preimage isOpen_H hDo
  have hCeq : cayleyInv '' D = C := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨QuantumZipper.CA.cayleyInv_mem_H (by simpa only [mem_ball, dist_zero_right] using hDb hw), ?_⟩
      change cayley (cayleyInv w) ∈ D
      rwa [QuantumZipper.CA.cayley_cayleyInv (ne_one_of_mem_ball (hDb hw))]
    · intro z hz
      exact ⟨cayley z, hz.2, QuantumZipper.CA.cayleyInv_cayley (Sec7.Lemma71F.add_I_ne_zero_of_mem_H hz.1)⟩
  have hCD : cayley '' C = D := by
    rw [← hCeq, image_image]
    exact (image_congr fun z hz => QuantumZipper.CA.cayley_cayleyInv (ne_one_of_mem_ball (hDb hz))).trans (image_id D)
  have hCpc : IsPreconnected C := hCeq ▸ hDpc.image _ (fun z hz =>
    (continuousAt_cayleyInv (ne_one_of_mem_ball (hDb hz))).continuousWithinAt)
  have hCα : ∀ z ∈ C, cayley z ∉ α '' Icc 0 1 :=
    fun z hz h => disjoint_left.1 hDα hz.2 h
  have hUC : IsBdryUniformizer (cayley '' C) (α a) (α b) Ψ := by rw [hCD]; exact hU
  have hf : IsConformalBijection (Ψ ∘ cayley) C H := by
    have hc := Sec7.Lemma71F.isConformalBijection_cayley_image hCH
    rw [hCD] at hc
    exact isConformalBijection_comp hU.conf hc
  have hIC : {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure (cayley '' C)} = Icc a b := by rwa [hCD]
  have hsideC : cayley '' C ⊆ crossSide α 1 := by rwa [hCD]
  obtain ⟨hVpc, hVu, hVsub, hVd⟩ := Sec7.Prop74B.crossSide_neg_props hα
  refine Sec7.Prop74B.re_pos_of_crossLoop hα.cont hα.inj hα.zero hα.one hCo hCpc hCH hCα
    ha0 hab hb1 hIC hf hUC.cont hUC.inj hUC.mapsTo hUC.zero hUC.tendsto (fun _ _ => rfl)
    (fun z hz => windNum_crossLoop_of_mem_crossSide_one hα (hsideC hz)) ?_
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hm01 : m ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine ⟨α m, ⟨m, hm, rfl⟩, ?_, _, hVpc, hVu,
    closure_mono hVsub (hα.crossRange_subset_closure_crossSide (Or.inr rfl)
      ⟨m, Ioo_subset_Icc_self hm01, rfl⟩), ?_⟩
  · intro h
    have hlt := hα.mem_disc m hm01
    rw [mem_ball, dist_zero_right, h.1] at hlt
    exact lt_irrefl _ hlt
  · refine disjoint_left.2 fun z hz hzc => disjoint_left.1 hVd hz ?_
    rcases hzc with (h | h) | h
    · exact Or.inl (Or.inl (closure_mono hsideC h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- A normalized boundary coordinate is negative on a lower-side marked crosscut arc. -/
theorem re_neg_of_disc_crossSide {α : ℝ → ℂ} (hα : IsDiscCrosscut α)
    {D : Set ℂ} (hDo : IsOpen D) (hDpc : IsPreconnected D) (hDb : D ⊆ ball 0 1)
    (hDα : Disjoint D (crossRange α)) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hI : {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure D} = Icc a b)
    {Ψ : ℂ → ℂ} (hU : IsBdryUniformizer D (α a) (α b) Ψ)
    (hside : D ⊆ crossSide α (-1)) : ∀ s ∈ Ioo a b, (Ψ (α s)).re < 0 := by
  have hDo' : IsOpen (conj '' D) := conjCLE.toHomeomorph.isOpenMap _ hDo
  have hDb' : conj '' D ⊆ ball (0 : ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [mem_ball, dist_zero_right, norm_conj] using hDb hz
  have hDα' : Disjoint (conj '' D) (crossRange (conj ∘ α)) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨s, hs, he⟩
    exact disjoint_left.1 hDα hz ⟨s, hs, conjCLE.injective he⟩
  have hI' : {s ∈ Icc (0 : ℝ) 1 | (conj ∘ α) s ∈ closure (conj '' D)} = Icc a b := by
    rw [← hI, ← conj_image_closure]
    ext s
    have hi : Injective (conj : ℂ → ℂ) := conjCLE.injective
    simp only [mem_ofPred_eq, comp_apply, hi.mem_set_image]
  have hside' : conj '' D ⊆ crossSide (conj ∘ α) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_crossSide_conj_upper.2 (hside hz)
  have hp := re_pos_of_disc_crossSide (isDiscCrosscut_conj hα) hDo'
    (hDpc.image _ continuous_conj.continuousOn) hDb' hDα' ha0 hab hb1 hI'
    (isBdryUniformizer_mirror hDo hU) hside'
  intro s hs
  have h := hp s hs
  simp only [mirrorUniformizer, comp_apply, conj_conj, neg_re, conj_re] at h
  linarith

end InteractingSLE.Theorem14.PocketMirror
