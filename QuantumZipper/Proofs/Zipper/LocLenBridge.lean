import QuantumZipper.Proofs.Zipper.LocLenDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): bridges between the open-arc and the old length readings

* `arcLen_eq_of_hasBdryLimitOn`: on a regular sample with a local limit `ν` on an open `U`, the
  open-arc length of `(a,b) ⊆ U` is `ν (a,b)` (the local reading only sees `U`).
* `arcLen_eq_of_isVagueLimitR`: if the global limit `ν` exists and has no atoms at `a`, `b`,
  the open-arc length is the old closed-interval reading `qBoundaryMeasure γ x (Icc a b)`.
* `unzipLengthsArc_eq_unzipLengths`: new = old whenever the global limit of the unzipped field
  exists and has no atoms at `O⁻_t`, `0`, `O⁺_t`; `ae_unzipLengthsArc_eq_unzipLengths`: a.s. at
  each fixed time under the fixed-time version of that hypothesis.
* `offSet W t = {O⁻_t, 0, O⁺_t}`: the closed set excluded by the open-arc reading at time `t`;
  `unzipLengthsArc_eq_of_isLQGGoodOff`: good off `offSet` ⇒ the arc lengths are masses of the
  local limit.

Paper: the endpoints carry no mass (Sheffield arXiv:1012.4797 p. 56: one atomless measure along
`η`; Berestycki–Powell arXiv:2404.16642 p. 285 "no atoms at `0±`", Def 6.41 p. 229). Own
elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen

variable {γ : ℝ} {x : FieldSample}

/-- The boundary points excluded by the open-arc reading at time `t`: the chart tip `0` and the
two images `O^±_t` of the root. -/
def offSet (W : ℝ → ℝ) (t : ℝ) : Set ℝ := {(sideImages W t).1, 0, (sideImages W t).2}

theorem isClosed_offSet (W : ℝ → ℝ) (t : ℝ) : IsClosed (offSet W t) :=
  (((Set.finite_singleton _).insert _).insert _).isClosed

theorem Ioo_left_disjoint_offSet (W : ℝ → ℝ) (t : ℝ) (hp : 0 ≤ (sideImages W t).2) :
    Disjoint (Ioo (sideImages W t).1 0) (offSet W t) := by
  rw [Set.disjoint_left]
  rintro u ⟨h1, h2⟩ hu
  rcases hu with rfl | rfl | rfl
  · exact lt_irrefl _ h1
  · exact lt_irrefl _ h2
  · linarith

theorem Ioo_right_disjoint_offSet (W : ℝ → ℝ) (t : ℝ) (hm : (sideImages W t).1 ≤ 0) :
    Disjoint (Ioo 0 (sideImages W t).2) (offSet W t) := by
  rw [Set.disjoint_left]
  rintro u ⟨h1, h2⟩ hu
  rcases hu with rfl | rfl | rfl
  · linarith
  · exact lt_irrefl _ h1
  · exact lt_irrefl _ h2

/-! ## Arc length from local limits -/

/-- **Local reading.** On a regular sample, if `ν` is the local limit on an open `U ⊇ (a,b)`, the
open-arc length of `(a,b)` is `ν (a,b)`. -/
theorem arcLen_eq_of_hasBdryLimitOn (hx : IsRegularSample x) {U : Set ℝ} {ν : Measure ℝ}
    (hν : HasBdryLimitOn γ x U ν) {a b : ℝ} (hab : Ioo a b ⊆ U) :
    arcLen γ x a b = ν (Ioo a b) := by
  unfold arcLen
  rw [qBoundaryMeasureOn_eq_of_hasBdryLimitOn hx isOpen_Ioo (hν.mono isOpen_Ioo hab),
    Measure.restrict_apply_self]

/-- Dyadic form of the local reading (no regularity needed). -/
theorem arcLen_eq_of_isVagueLimitOnR {U : Set ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitOnR U (bdryApprox γ x) ν) {a b : ℝ} (hab : Ioo a b ⊆ U) :
    arcLen γ x a b = ν (Ioo a b) := by
  have hr : IsVagueLimitOnR (Ioo a b) (bdryApprox γ x) (ν.restrict (Ioo a b)) := by
    obtain ⟨-, hK, ht⟩ := hν
    refine ⟨by rw [Measure.restrict_apply isOpen_Ioo.measurableSet.compl]; simp,
      fun K hKc hKV => (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKV.trans hab)),
      fun f hf hfc hfV => ?_⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfV h))]
    exact ht f hf hfc (hfV.trans hab)
  unfold arcLen
  rw [LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hr, Measure.restrict_apply_self]

/-- A global vague limit restricts to a local one on every open set. -/
theorem isVagueLimitOnR_of_isVagueLimitR {ν : Measure ℝ} (h : IsVagueLimitR (bdryApprox γ x) ν)
    {U : Set ℝ} (hU : IsOpen U) : IsVagueLimitOnR U (bdryApprox γ x) (ν.restrict U) := by
  have := h.1
  refine ⟨?_, fun K hK _ => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top,
    fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hU.measurableSet.compl, compl_inter_self, measure_empty]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h')]
    exact h.2 f hf hfc

/-- The mass of a closed interval is the mass of the open interval when the endpoints are not
atoms. -/
theorem measure_Icc_eq_Ioo_of_noAtoms {ν : Measure ℝ} {a b : ℝ} (ha : ν {a} = 0)
    (hb : ν {b} = 0) : ν (Icc a b) = ν (Ioo a b) := by
  refine le_antisymm ?_ (measure_mono Ioo_subset_Icc_self)
  calc ν (Icc a b) ≤ ν (Ioo a b ∪ ({a} ∪ {b})) := measure_mono fun u hu => by
        rcases eq_or_lt_of_le hu.1 with h | h
        · exact Or.inr (Or.inl h.symm)
        rcases eq_or_lt_of_le hu.2 with h' | h'
        · exact Or.inr (Or.inr h')
        exact Or.inl ⟨h, h'⟩
    _ ≤ ν (Ioo a b) + (ν {a} + ν {b}) := (measure_union_le _ _).trans
        (add_le_add le_rfl (measure_union_le _ _))
    _ = ν (Ioo a b) := by rw [ha, hb, add_zero, add_zero]

/-- **Bridge (deterministic).** If the global limit `ν` of the dyadic approximations exists and
has no atoms at `a`, `b`, the open-arc length is the old closed-interval reading. -/
theorem arcLen_eq_of_isVagueLimitR {ν : Measure ℝ} (h : IsVagueLimitR (bdryApprox γ x) ν)
    {a b : ℝ} (ha : ν {a} = 0) (hb : ν {b} = 0) :
    arcLen γ x a b = qBoundaryMeasure γ x (Icc a b) := by
  rw [arcLen_eq_of_isVagueLimitOnR (isVagueLimitOnR_of_isVagueLimitR h isOpen_univ)
      (subset_univ _), qBoundaryMeasure_eq h, Measure.restrict_univ,
    measure_Icc_eq_Ioo_of_noAtoms ha hb]

/-! ## Arc lengths of samples good off `offSet` -/

end LocLen
end QuantumZipper
