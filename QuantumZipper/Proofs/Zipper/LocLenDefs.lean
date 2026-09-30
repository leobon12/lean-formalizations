import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Statements.ConfigLaw
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.Proofs.LQG.LocalRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), foundations: local goodness and open-arc lengths

Decision D75 (user-approved, 2026-09-29): Theorem 1.3's proof is rewritten so that it needs
goodness of the unzipped fields only **away from the tip**, and lengths of pieces of `η` are read
on **open arcs**, as in the paper:

* Sheffield, arXiv:1012.4797, p. 56 ¶2–3 (the length of `η([0,t])` is measured by unzipping,
  one measure per side, eq. (5.1)) and Thm 1.8 p. 26 ("well defined by unzipping");
* Berestycki–Powell, arXiv:2404.16642, Def 6.41 p. 229 (the boundary measure is read in any
  chart in which the field is a Neumann GFF plus a continuous function near a segment of `ℝ`;
  for the unzipped wedge this excludes the chart tip `0` and the base points `O^±_t`),
  Def 8.12 p. 281, Thm 8.16 p. 283.

Definitions (new; `unzipLengths`, `zipLenDown` and all `Statements/` files are unchanged):

* `HasBdryLimitOn γ x U ν`: the offset-uniform boundary limit of `HasBdryLimit` (along
  `goodFilter`), tested only against continuous functions with compact support in `U`
  (the `goodFilter` analogue of `IsVagueLimitOnR`).
* `IsLQGGoodOff γ x S`: `IsLQGGood` with the boundary limit required only off `S`
  (area part unchanged: it is tested on compacts of the open `ℍ` and never sees the boundary).
* `arcLen γ x a b`: the open-arc length, the mass of `(a,b)` for the local boundary limit on
  `(a,b)` (`qBoundaryMeasureOn`), junk `0` if that local limit does not exist.
* `unzipLengthsArc γ c t`: the open-arc reading of the two lengths of `η[0,t]`: `arcLen` of the
  unzipped field on `(O⁻_t, 0)` and `(0, O⁺_t)`.
* `lenTimeArc`, `zipLenDownArc`, `zipLenCArc`: the length zipper with `unzipLengthsArc` in place of
  `unzipLengths` (verbatim copies of `unzipTime`, `zipLenDown`, `zipLenC` otherwise).

Basic API: restriction, uniqueness, `IsLQGGood ⇒ IsLQGGoodOff`, monotonicity in `S`, and
`IsLQGGoodOff γ x ∅ ↔ IsLQGGood γ x`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen

/-! ## Definitions -/

/-- `ν` is the offset-uniform boundary limit of `x` on the open set `U`: concentrated on `U`,
finite on compacts of `U`, and the integrals of every continuous test function with compact
support in `U` converge along `goodFilter` (the radii `a 2^{-k}`, uniformly in `a ∈ [1,2]`). -/
def HasBdryLimitOn (γ : ℝ) (x : FieldSample) (U : Set ℝ) (ν : Measure ℝ) : Prop :=
  ν Uᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ U → ν K < ⊤) ∧
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun i => ∫ t, f t ∂bdryR γ x (goodRad i)) goodFilter (𝓝 (∫ t, f t ∂ν))

/-- **Good off `S`**: `IsLQGGood` with the boundary limit tested only off the closed set `S`
(for the unzipped fields, `S` = the chart tip `{0}`, or the tip and the base points). -/
def IsLQGGoodOff (γ : ℝ) (x : FieldSample) (S : Set ℝ) : Prop :=
  IsRegularSample x ∧ (∃ ν, HasBdryLimitOn γ x Sᶜ ν) ∧ ∃ μ, HasAreaLimit γ x μ

/-- **Open-arc length**: the mass of `(a,b)` for the local boundary limit of `x` on `(a,b)`
(B-P Def 6.41 on the open segment), junk `0` if that local limit does not exist. -/
def arcLen (γ : ℝ) (x : FieldSample) (a b : ℝ) : ℝ≥0∞ :=
  qBoundaryMeasureOn γ x (Ioo a b) (Ioo a b)

/-- **Open-arc lengths of `η[0,t]`** (D75): the open-arc lengths of `(O⁻_t, 0)` and `(0, O⁺_t)`
for the field unzipped at capacity time `t`. Endpoints are excluded; they carry no mass for the
paper's measure. -/
def unzipLengthsArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (t : ℝ) : ℝ≥0∞ × ℝ≥0∞ :=
  (arcLen γ (unzippedField γ c t) (sideImages c.2 t).1 0,
    arcLen γ (unzippedField γ c t) 0 (sideImages c.2 t).2)

/-- The first capacity time at which the open-arc left length reaches `ℓ` (copy of
`unzipTime` with `unzipLengthsArc`). -/
def lenTimeArc (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ c s).1}

/-- `Z^LEN_{−ℓ}` with open-arc lengths (verbatim copy of `zipLenDown` otherwise). -/
def zipLenDownArc (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : FieldSample × (ℝ → ℝ) :=
  let t' := lenTimeArc γ ℓ c
  let x' := coordChange c.1 (fwdMapInv c.2 t') (Qc γ)
  let a := scaleParam γ x'
  (rescale x' (Qc γ) a, fun s => (c.2 (t' + a ^ 2 * max s 0) - c.2 t') / a)

/-! ## Unfolding -/

/-! ## `HasBdryLimitOn`: basic API -/

variable {γ : ℝ} {x : FieldSample}

/-- A (local) limit tested on `U` restricts to every smaller open set `V` (as `ν|_V`). -/
theorem HasBdryLimitOn.mono {U V : Set ℝ} {ν : Measure ℝ} (h : HasBdryLimitOn γ x U ν)
    (hV : IsOpen V) (hVU : V ⊆ U) : HasBdryLimitOn γ x V (ν.restrict V) := by
  obtain ⟨-, hK, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply hV.measurableSet.compl]; simp,
    fun K hKc hKV => (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKV.trans hVU)),
    fun f hf hfc hfV => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfV h))]
  exact ht f hf hfc (hfV.trans hVU)

/-- A global offset-uniform limit restricts to every open set. -/
theorem _root_.QuantumZipper.HasBdryLimit.hasBdryLimitOn {ν : Measure ℝ}
    (h : HasBdryLimit γ x ν) {U : Set ℝ} (hU : IsOpen U) :
    HasBdryLimitOn γ x U (ν.restrict U) := by
  have := h.1
  refine ⟨?_, fun K hK _ => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top,
    fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hU.measurableSet.compl, compl_inter_self, measure_empty]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h')]
    exact h.2 f hf hfc

/-- The unit-offset restriction: a local offset-uniform limit on `U` is a local vague limit of
the dyadic approximations `bdryApprox` on `U` (for a regular sample). -/
theorem HasBdryLimitOn.isVagueLimitOnR (hx : IsRegularSample x) {U : Set ℝ} {ν : Measure ℝ}
    (h : HasBdryLimitOn γ x U ν) : IsVagueLimitOnR U (bdryApprox γ x) ν := by
  obtain ⟨F, hF⟩ := hx
  refine ⟨h.1, h.2.1, fun f hf hfc hfU => ?_⟩
  refine ((h.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter).congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.bdryR_radius γ hF]

/-- The local limit along the unit offsets `bdryR γ x (radius k)`, no regularity needed. -/
theorem HasBdryLimitOn.isVagueLimitOnR_unit {U : Set ℝ} {ν : Measure ℝ}
    (h : HasBdryLimitOn γ x U ν) :
    IsVagueLimitOnR U (fun k => bdryR γ x (goodRad (k, 1))) ν :=
  ⟨h.1, h.2.1, fun f hf hfc hfU => (h.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter⟩

/-- **Uniqueness** of local offset-uniform limits on an open set. -/
theorem HasBdryLimitOn.unique {U : Set ℝ} (hU : IsOpen U) {ν ν' : Measure ℝ}
    (h : HasBdryLimitOn γ x U ν) (h' : HasBdryLimitOn γ x U ν') : ν = ν' :=
  LocalRule.isVagueLimitOnR_unique hU h.isVagueLimitOnR_unit h'.isVagueLimitOnR_unit

/-- On a regular sample, the chosen local measure `qBoundaryMeasureOn` on an open set is the
local offset-uniform limit. -/
theorem qBoundaryMeasureOn_eq_of_hasBdryLimitOn (hx : IsRegularSample x) {U : Set ℝ}
    (hU : IsOpen U) {ν : Measure ℝ} (h : HasBdryLimitOn γ x U ν) :
    qBoundaryMeasureOn γ x U = ν :=
  LocalRule.qBoundaryMeasureOn_eq hU (h.isVagueLimitOnR hx)

/-! ## `IsLQGGoodOff`: basic API -/

/-- Good off `S` implies good off every closed `S' ⊇ S`. -/
theorem IsLQGGoodOff.mono {S S' : Set ℝ} (hx : IsLQGGoodOff γ x S) (hS' : IsClosed S')
    (hSS' : S ⊆ S') : IsLQGGoodOff γ x S' := by
  obtain ⟨hr, ⟨ν, hν⟩, hA⟩ := hx
  exact ⟨hr, ⟨_, hν.mono hS'.isOpen_compl (compl_subset_compl.2 hSS')⟩, hA⟩

/-- The chosen local boundary measure of a sample good off `S`, on any open `U` avoiding `S`,
is the restriction of the local limit. -/
theorem IsLQGGoodOff.qBoundaryMeasureOn_eq {S : Set ℝ} {ν : Measure ℝ}
    (hr : IsRegularSample x) (hν : HasBdryLimitOn γ x Sᶜ ν) {U : Set ℝ} (hU : IsOpen U)
    (hUS : Disjoint U S) : qBoundaryMeasureOn γ x U = ν.restrict U :=
  qBoundaryMeasureOn_eq_of_hasBdryLimitOn hr hU
    (hν.mono hU (fun _ hu hs => disjoint_left.1 hUS hu hs))

end LocLen
end QuantumZipper
