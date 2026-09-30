import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Section5.Prop16NodeCMaskLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T6 (R18-AREAREAD), part 1: the area read from the masked data

Sheffield, arXiv:1012.4797, p. 17: "both `h` and `η` are determined by the pair" of surfaces cut
out by `η`; in particular the quantum area of the pieces is a function of the field **off the
curve** (the curve carries no area, p. 48). Here:

* `readOffField d`: the field sample read from masked data `d` (`E6.FullData`), using only the
  circle coordinates that stay off the curve `curveSel d.2` (a measurable function of `d`,
  `measurable_readOffField`);
* `areaOfData γ d`: the local quantum area of `readOffField d` on `ℍ ∖ curve` (`qAreaMeasureOn`,
  A17: a vague limit tested only on functions supported in `ℍ ∖ curve`; it is concentrated on
  `ℍ ∖ curve`, i.e. extended by `0` on the curve);
* `areaOfData_offData`: for a configuration whose field has a global area limit `μ` on `ℍ`,
  `areaOfData γ (offData x) = μ|_{ℍ ∖ curve}`; with zero area of the curve it is `μ`
  (`areaOfData_offData_eq`).

The locality step is the circle-agreement rule of the local area measure
(`Prop16Asm.qAreaMeasureOn_eq_of_circAgree`) plus uniqueness of local vague limits. Own elementary
bookkeeping (no published proof is needed: this is the measurability/locality content of
"determined by the pair").
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm CoordsFull

/-- The index `i` reads the folded circle `μ`, and that circle stays off the curve of `d`. -/
def OffIdx (d : E6.FullData) (μ : Measure ℂ) (i : ℕ) : Prop :=
  foldedCircle (fullIndex i).1 (fullIndex i).2 = μ ∧
    CircleOff (D74.curveSel d.2) (fullIndex i).1 (fullIndex i).2

open Classical in
/-- The field sample read from masked data: at a folded circle staying off the curve, the first
recorded coordinate of that circle; junk `0` elsewhere. -/
def readOffField (d : E6.FullData) : FieldSample := fun μ =>
  if h : ∃ i, OffIdx d μ i then d.1.1 (Nat.find h) else 0

/-- The complement of the curve read from the data, in `ℍ`. -/
def offSet (d : E6.FullData) : Set ℂ := H \ D74.curveSel d.2

/-- **The area read from the masked data**: the local quantum area measure of the field read
off the curve, on `ℍ ∖ curve` (concentrated there, so extended by `0` on the curve). -/
def areaOfData (γ : ℝ) (d : E6.FullData) : Measure ℂ :=
  qAreaMeasureOn γ (readOffField d) (offSet d)

theorem isOpen_offSet (d : E6.FullData) : IsOpen (offSet d) :=
  isOpen_H.sdiff isClosed_closure

/-! ## Measurability of the read field -/

open Classical in
theorem measurable_dite_find {α : Type*} [MeasurableSpace α] {p : ℕ → α → Prop}
    (hp : ∀ i, MeasurableSet {a | p i a}) {g : ℕ → α → ℝ} (hg : ∀ i, Measurable (g i)) :
    Measurable fun a => if h : ∃ i, p i a then g (Nat.find h) a else 0 := by
  have hE : MeasurableSet {a | ∃ i, p i a} := by
    rw [setOf_exists]; exact MeasurableSet.iUnion hp
  set N : α → ℕ := fun a => if h : ∃ i, p i a then Nat.find h else 0 with hNdef
  have hN : Measurable N := by
    refine measurable_to_countable' fun i => ?_
    have e : N ⁻¹' {i} = ({a | p i a} ∩ ⋂ j, ⋂ (_ : j < i), {a | ¬ p j a}) ∪
        ({a | ∃ i, p i a}ᶜ ∩ {_a | i = 0}) := by
      ext a
      simp only [mem_preimage, mem_singleton_iff, hNdef, mem_union, mem_inter_iff, mem_setOf_eq,
        mem_iInter, mem_compl_iff]
      by_cases h : ∃ i, p i a
      · rw [dif_pos h, Nat.find_eq_iff]
        simp only [h, not_true_eq_false, false_and, or_false]
      · rw [dif_neg h]
        simp only [h, not_false_eq_true, true_and]
        constructor
        · intro e; exact Or.inr e.symm
        · rintro (⟨hi, -⟩ | e)
          · exact absurd ⟨i, hi⟩ h
          · exact e.symm
    rw [e]
    refine ((hp i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (hp j).compl)).union (hE.compl.inter ?_)
    by_cases hi : i = 0
    · simp only [hi, setOf_true, MeasurableSet.univ]
    · simp only [hi, setOf_false, MeasurableSet.empty]
  have hG : Measurable fun a => g (N a) a := by
    intro T hT
    have e : (fun a => g (N a) a) ⁻¹' T = ⋃ i, (N ⁻¹' {i}) ∩ (g i ⁻¹' T) := by
      ext a
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, exists_eq_left']
    rw [e]
    exact MeasurableSet.iUnion fun i => (hN (measurableSet_singleton i)).inter (hg i hT)
  have e : (fun a => if h : ∃ i, p i a then g (Nat.find h) a else 0) =
      fun a => if a ∈ {a | ∃ i, p i a} then g (N a) a else 0 := by
    funext a
    by_cases h : ∃ i, p i a
    · have hm : a ∈ {a | ∃ i, p i a} := h
      rw [dif_pos h, if_pos hm, hNdef]
      simp only [dif_pos h]
    · have hm : a ∉ {a | ∃ i, p i a} := h
      rw [dif_neg h, if_neg hm]
  rw [e]
  exact Measurable.ite hE hG measurable_const

theorem measurableSet_offIdx (μ : Measure ℂ) (i : ℕ) :
    MeasurableSet {d : E6.FullData | OffIdx d μ i} := by
  by_cases h : foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [OffIdx, h, true_and]
    exact measurable_snd (D74.measurableSet_circleOff_curveSel _ _)
  · simp only [OffIdx, h, false_and, setOf_false, MeasurableSet.empty]

theorem measurable_readOffField : Measurable readOffField := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  exact measurable_dite_find (measurableSet_offIdx μ)
    (g := fun i d => d.1.1 i) fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)

/-! ## The read field agrees with the field off the curve -/

theorem curveSel_offData {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2) (h0 : x.2 0 = 0) :
    D74.curveSel (offData x).2 = curveOf x.2 :=
  D74.curveSel_eq_curveOf hc h0

theorem readOffField_offData {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2) (h0 : x.2 0 = 0)
    {i : ℕ} (hi : CircleOff (curveOf x.2) (fullIndex i).1 (fullIndex i).2) :
    readOffField (offData x) (foldedCircle (fullIndex i).1 (fullIndex i).2) =
      x.1 (foldedCircle (fullIndex i).1 (fullIndex i).2) := by
  classical
  have hk := curveSel_offData hc h0
  have hex : ∃ j, OffIdx (offData x) (foldedCircle (fullIndex i).1 (fullIndex i).2) j :=
    ⟨i, rfl, by rw [hk]; exact hi⟩
  unfold readOffField
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  rw [hk] at h2
  rw [show (offData x).1.1 (Nat.find hex) = coordsFull x.1 (Nat.find hex) from if_pos h2]
  simp only [coordsFull]
  rw [h1]

/-- A folded circle whose closed disc (in `ℍ̄`) misses the closed set `K` stays off `K`. -/
theorem circleOff_of_disjoint {K : Set ℂ} (hK : IsClosed K) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ}
    (hr : 0 ≤ r) (hdis : Disjoint (closedBall d r ∩ Hbar) K) : CircleOff K d r := by
  obtain ⟨δ, hδ, hdd⟩ := hdis.exists_cthickenings
    ((isCompact_closedBall d r).inter_right isClosed_Hbar) hK
  refine ⟨δ, hδ, fun w hw hwK => ?_⟩
  set p := foldH w with hpdef
  have hp : p ∈ Hbar := CircleFubini.foldH_mem_Hbar' w
  have hdist : dist p d ≤ dist w d := by
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖p - d‖ = ‖foldH w - foldH d‖ := by rw [CircleFubini.foldH_of_mem' hd]
      _ ≤ ‖w - d‖ := RegSample.norm_foldH_sub_le w d
  have hlt : dist p d < r + δ := by
    have := (abs_lt.1 hw).2
    linarith
  have hmem : p ∈ cthickening δ (closedBall d r ∩ Hbar) := by
    by_cases hle : dist p d ≤ r
    · exact self_subset_cthickening _ ⟨mem_closedBall.2 hle, hp⟩
    · push Not at hle
      have hpos : 0 < ‖p - d‖ := by rw [← dist_eq_norm]; linarith
      set t : ℝ := r / ‖p - d‖ with htdef
      have ht0 : 0 ≤ t := div_nonneg hr hpos.le
      have ht1 : t ≤ 1 := by
        rw [htdef, div_le_one hpos, ← dist_eq_norm]; exact hle.le
      set q : ℂ := d + (t : ℂ) * (p - d) with hqdef
      have hnq : ‖(t : ℂ) * (p - d)‖ = r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, htdef,
          div_mul_cancel₀ _ hpos.ne']
      have hq : q ∈ closedBall d r ∩ Hbar := by
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall, dist_eq_norm, hqdef, add_sub_cancel_left, hnq]
        · show 0 ≤ q.im
          have hdi : 0 ≤ d.im := hd
          have hpi : 0 ≤ p.im := hp
          simp only [hqdef, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, add_zero, Complex.sub_im]
          nlinarith
      refine mem_cthickening_of_dist_le p q δ _ hq ?_
      have e : p - q = ((1 - t : ℝ) : ℂ) * (p - d) := by
        rw [hqdef]; push_cast; ring
      rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), sub_mul, one_mul, htdef, div_mul_cancel₀ _ hpos.ne',
        ← dist_eq_norm]
      linarith
  exact Set.disjoint_left.1 hdd hmem (self_subset_cthickening K hwK)

/-- The read field agrees with the field on every dyadic folded circle inside `ℍ ∖ curve`. -/
theorem circAgree_readOffField {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) :
    Prop16Area.G.CircAgree (H \ curveOf x.2) (readOffField (offData x)) x.1 := by
  intro n k z hz hW
  obtain ⟨i, hi⟩ := fullIndex_surj n z 1 one_pos k
  rw [← radius_eq_div] at hi
  have hoff : CircleOff (curveOf x.2) (fullIndex i).1 (fullIndex i).2 := by
    rw [hi]
    refine circleOff_of_disjoint isClosed_closure (Positivity.dyadicRoundC_mem_Hbar n hz)
      (radius_pos k).le (Set.disjoint_left.2 fun p hp hpK => (hW hp).2 hpK)
  have h := readOffField_offData hc h0 hoff
  rw [hi] at h
  exact h

/-! ## Identification with the true area -/

theorem isVagueLimitOn_restrict_R18 {U U' : Set ℂ} (hU' : IsOpen U') (hUU : U' ⊆ U)
    {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : IsVagueLimitOn U νs μ) :
    IsVagueLimitOn U' νs (μ.restrict U') := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply' hU'.measurableSet]; simp, fun K hKc hKU =>
    (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKU.trans hUU)), fun f hf hfc hfU => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h')]
  exact ht f hf hfc (hfU.trans hUU)

/-- **Locality of the read area**: if the field of `x` has the global area limit `μ` on `ℍ`,
the area read from the masked data of `x` is `μ` restricted to `ℍ ∖ curve`. -/
theorem areaOfData_offData {γ : ℝ} {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x.1) μ) :
    areaOfData γ (offData x) = μ.restrict (H \ curveOf x.2) := by
  have hUo : IsOpen (H \ curveOf x.2) := isOpen_H.sdiff isClosed_closure
  unfold areaOfData offSet
  rw [curveSel_offData hc h0, Prop16Asm.qAreaMeasureOn_eq_of_circAgree hUo
    (circAgree_readOffField hc h0) hUo sdiff_subset subset_rfl]
  exact LocalRule.qAreaMeasureOn_eq hUo (isVagueLimitOn_restrict_R18 hUo sdiff_subset hμ)

/-- With zero area of the curve, the area read from the masked data is the true area. -/
theorem areaOfData_offData_eq {γ : ℝ} {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x.1) μ)
    (hnull : μ (curveOf x.2) = 0) : areaOfData γ (offData x) = μ := by
  rw [areaOfData_offData hc h0 hμ]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) (measure_union_null hμ.1 hnull)
  by_cases hzH : z ∈ H
  · by_contra hc
    exact hz ⟨hzH, fun h => hc (Or.inr h)⟩
  · exact Or.inl hzH

end R18
end QuantumZipper
