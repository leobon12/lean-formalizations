/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9CTip
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# Lemma S3: an upper collar along a real suffix is unfilled

Packet PROVE-T14-S3, specification p. 580. The unused proper tail certifies
access to infinity before the real suffix is added. Adding that suffix does
not change the filling. No relative Loewner driver is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- Every point strictly after a proper curve's compact prefix is free for
that prefix. The entire unused tail supplies the access to infinity. -/
theorem isFreeAt_of_lt_proper_prefix {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) {a t : ℝ≥0} (hat : a < t) :
    HalfPlaneSep.IsFreeAt (γ '' Icc 0 a) (γ t) := by
  have hc : IsCompact (γ '' Icc 0 a) := isCompact_Icc.image hγ.1
  apply HalfPlaneSep.isFreeAt_of_not_isBounded hc.isClosed hc.isBounded
    (isPreconnected_Ioi.image γ hγ.1.continuousOn)
    (Supp9B.not_isBounded_image_Ioi hγ.2.2.2 a) _ _ ⟨t, hat, rfl⟩
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨hγ.2.2.1 s, ?_⟩
  rintro ⟨r, hr, hrs⟩
  exact (not_le.2 hs) (hγ.2.1 hrs ▸ hr.2)

/-- A suffix contained in the real line adds no half-plane filling. -/
theorem fillH_prefix_eq_of_real_suffix {γ : ℝ≥0 → ℂ} {a b : ℝ≥0}
    (hab : a ≤ b) (hreal : ∀ t ∈ Icc a b, (γ t).im = 0) :
    fillH (γ '' Icc 0 b) = fillH (γ '' Icc 0 a) := by
  rw [← Icc_union_Icc_eq_Icc (show (0 : ℝ≥0) ≤ a from zero_le) hab, image_union]
  apply Restart.fillH_union_of_forall_notMem_H
  rintro _ ⟨t, ht, rfl⟩ hH
  exact (ne_of_gt (show 0 < (γ t).im from hH)) (hreal t ht)

/-- An interior point of a real suffix has an upper half-disc in the
unbounded domain of the prefix including that suffix. -/
theorem isFreeAt_of_real_suffix {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) {a b t : ℝ≥0} (hat : a < t) (htb : t ≤ b)
    (hreal : ∀ s ∈ Icc a b, (γ s).im = 0) :
    HalfPlaneSep.IsFreeAt (γ '' Icc 0 b) (γ t) := by
  unfold HalfPlaneSep.IsFreeAt
  rw [fillH_prefix_eq_of_real_suffix (hat.le.trans htb) hreal]
  exact isFreeAt_of_lt_proper_prefix hγ hat

end InteractingSLE.Theorem14.SB.S3
