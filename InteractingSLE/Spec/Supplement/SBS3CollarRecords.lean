/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Supplement.S9BExtend
import InteractingSLE.Spec.Supplement.SBTail2Induction

/-!
# Lemma S3: a proper lift traverses nonnegative real contacts as records

Packet PROVE-T14-S3, specification p. 580. Compare the lift with the positive
real ray using the existing closed-side duality and contact-order theorem.
The proper-target requirement is retained; no relative driver is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace InteractingSLE.Theorem14.SB.S3

/-- The nonnegative real ray parametrized by its real coordinate. -/
def positiveRealRay (s : ℝ≥0) : ℂ := ((s : ℝ) : ℂ)

theorem isProperCurve_positiveRealRay : Supp9B.IsProperCurve positiveRealRay := by
  refine ⟨by unfold positiveRealRay; fun_prop, ?_, fun _ => by simp [positiveRealRay], ?_⟩
  · intro s t h
    exact NNReal.coe_injective (Complex.ofReal_injective h)
  · simp only [positiveRealRay, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (NNReal.coe_nonneg _)]
    exact NNReal.tendsto_coe_atTop.2 tendsto_id

/-- Nonnegative real contacts of a proper curve from zero occur in spatial
order. Closed-side duality puts the curve to the left of the real ray. -/
theorem nonneg_real_contact_order {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ)
    (hγ0 : γ 0 = 0) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y)
    {s t : ℝ≥0} (hs : γ s = x) (ht : γ t = y) : s < t := by
  have hγim : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hordR : range positiveRealRay ⊆ Supp9B.closedRightSide γ := by
    rintro _ ⟨r, rfl⟩
    exact ofReal_mem_closedRightSide_of_seed_le hγ hγim
      (by rw [hγ0, Complex.zero_re]; exact r.2)
  have hord := Supp9B.range_subset_closedLeftSide_of_closedRightSide
    isProperCurve_positiveRealRay hγ rfl hγim (by rw [hγ0]; rfl) hordR
  apply Supp9B.contact_order isProperCurve_positiveRealRay hγ rfl hγim
    (by rw [hγ0]; rfl) hord
    (s := x.toNNReal) (s' := y.toNNReal)
  · simpa only [positiveRealRay, Real.coe_toNNReal _ hx] using hs.symm
  · simpa only [positiveRealRay, Real.coe_toNNReal _ (hx.trans hxy.le)] using ht.symm
  · exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg hx).2 hxy

/-- Every earlier real contact is strictly left of a nonnegative real
contact. Thus that contact is a new right real record, including when
earlier contacts lie on the negative real axis. -/
theorem re_lt_of_real_before_nonneg_contact {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) {x : ℝ} (hx : 0 ≤ x)
    {s t : ℝ≥0} (hst : s < t) (hs : (γ s).im = 0) (ht : γ t = x) :
    (γ s).re < x := by
  have hsr : γ s = ((γ s).re : ℂ) := Complex.ext rfl (by simp only [Complex.ofReal_im, hs])
  by_contra h
  rcases eq_or_lt_of_le (not_lt.1 h) with heq | hlt
  · exact hst.ne (hγ.2.1 (hsr.trans (by rw [← heq, ht])))
  · exact (not_lt.2 hst.le) (nonneg_real_contact_order hγ hγ0 hx hlt ht hsr)

/-- A nonnegative real tip bounds every retained real point of its prefix. -/
theorem re_le_of_real_before_nonneg_contact {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) {x : ℝ} (hx : 0 ≤ x)
    {s t : ℝ≥0} (hst : s ≤ t) (hs : (γ s).im = 0) (ht : γ t = x) :
    (γ s).re ≤ x := by
  rcases hst.lt_or_eq with hlt | rfl
  · exact (re_lt_of_real_before_nonneg_contact hγ hγ0 hx hlt hs ht).le
  · rw [ht, Complex.ofReal_re]

end InteractingSLE.Theorem14.SB.S3
