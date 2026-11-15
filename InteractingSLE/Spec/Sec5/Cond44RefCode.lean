/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Cond44RefSide

/-!
# §4.2, Theorem 1.2 under (4.4): the hitting code read from the counterflow is measurable

Packet PROVE-SEC5-N. For a countable family of points `f x : ℚ → ℂ` depending measurably on a parameter `x`
(in the application: the counterflow line at rational times, read from its driving history), the conditions of
`Cond44RefSide.lean` on `K = closure (range (f x))` are measurable in `x`:

* `measurableSet_leftReach`: the left reach set (`LeftReach`) at a fixed point. The component of `ℍ \ K` is described
  by polygonal reachability with rational vertices (`Theorem15D5.mem_connectedComponentIn_iff_exists_reach`), and
  `ℍ \ K` is the complement of the closure of `f x` together with the rational points of the closed lower half-plane
  (`H_diff_closure_eq`), so `Theorem15D5.measurableSet_reach` applies;
* `measurable_lbCode`: the hitting code read from `K`.
-/

set_option autoImplicit false

open Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Cond44Ref

open WangWu hiding ratPt exists_ratPt_dist_lt
open Theorem15D5

/-! ### The closed lower half-plane as a closure of rational points -/

/-- The rational points `a − |b| i` of the closed lower half-plane. -/
def lowPt (w : ℚ × ℚ) : ℂ := ratPt (w.1, -|w.2|)

theorem closure_range_lowPt : closure (range lowPt) = {z : ℂ | z.im ≤ 0} := by
  have hcl : IsClosed {z : ℂ | z.im ≤ 0} := isClosed_le Complex.continuous_im continuous_const
  refine subset_antisymm (closure_minimal ?_ hcl) fun z hz => ?_
  · rintro _ ⟨w, rfl⟩
    show ((-|(w.2 : ℚ)| : ℚ) : ℝ) ≤ 0
    push_cast
    exact neg_nonpos.2 (abs_nonneg _)
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨w, hw⟩ := exists_ratPt_dist_lt z hε
    refine ⟨lowPt w, ⟨w, rfl⟩, ?_⟩
    rw [dist_comm]
    refine lt_of_le_of_lt ?_ hw
    have hz' : z.im ≤ 0 := hz
    rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
    apply Real.sqrt_le_sqrt
    have hre : (lowPt w).re = (ratPt w).re := rfl
    have him1 : (lowPt w).im = -|((w.2 : ℚ) : ℝ)| := by
      show (((-|w.2| : ℚ)) : ℝ) = _
      push_cast; rfl
    have him2 : (ratPt w).im = ((w.2 : ℚ) : ℝ) := rfl
    rw [hre, him1, him2]
    have : (-|((w.2 : ℚ) : ℝ)| - z.im) ^ 2 ≤ (((w.2 : ℚ) : ℝ) - z.im) ^ 2 := by
      rcases le_or_gt 0 ((w.2 : ℚ) : ℝ) with hb | hb
      · rw [abs_of_nonneg hb]; nlinarith
      · rw [abs_of_neg hb, neg_neg]
    linarith

/-- `ℍ \ closure S` is the complement of the closure of `S` together with the closed lower half-plane. -/
theorem H_diff_closure_eq (g : ℚ → ℂ) : H \ closure (range g) = (closure (range (Sum.elim g lowPt)))ᶜ := by
  rw [Set.Sum.elim_range, closure_union, closure_range_lowPt]
  ext z
  simp only [Set.mem_sdiff, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ### Measurability -/

variable {X : Type*} [MeasurableSpace X]

/-- **The left reach set is measurable in the family.** -/
theorem measurableSet_leftReach {f : X → ℚ → ℂ} (hf : ∀ q, Measurable fun x => f x q) (z : ℂ) :
    MeasurableSet {x | LeftReach (closure (range (f x))) z} := by
  have h1 : MeasurableSet {x | z ∉ closure (range (f x))} :=
    (measurableSet_mem_closure_range hf measurable_const).compl
  have h2 : ∀ a r : ℚ, MeasurableSet {x | Disjoint (halfDisc a r) (closure (range (f x)))} := by
    intro a r
    have e : {x | Disjoint (halfDisc a r) (closure (range (f x)))} = ⋂ q, {x | f x q ∉ halfDisc a r} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h q hq
        exact disjoint_left.1 h hq (subset_closure (mem_range_self q))
      · intro h
        refine Disjoint.closure_right ?_ (isOpen_halfDisc a r)
        exact disjoint_right.2 (by rintro _ ⟨q, rfl⟩; exact h q)
    rw [e]
    exact MeasurableSet.iInter fun q => (hf q) (isOpen_halfDisc a r).measurableSet.compl
  have h3 : ∀ w : ℚ × ℚ,
      MeasurableSet {x | z ∈ connectedComponentIn (H \ closure (range (f x))) (ratPt w)} := by
    intro w
    have e : {x | z ∈ connectedComponentIn (H \ closure (range (f x))) (ratPt w)} =
        ⋃ k : ℕ, {x | Reach (closure (range (Sum.elim (f x) lowPt)))ᶜ (ratPt w) k z} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      rw [H_diff_closure_eq, mem_connectedComponentIn_iff_exists_reach isClosed_closure.isOpen_compl]
    rw [e]
    refine MeasurableSet.iUnion fun k => measurableSet_reach (f := fun x => Sum.elim (f x) lowPt) ?_
      measurable_const k measurable_const
    rintro (q | v)
    · exact hf q
    · exact measurable_const
  have e : {x | LeftReach (closure (range (f x))) z} =
      {x | z ∈ H} ∩ {x | z ∉ closure (range (f x))} ∩ ⋃ a : ℚ, ⋃ r : ℚ, ⋃ w : ℚ × ℚ,
        ({x | a < 0 ∧ 0 < r ∧ ratPt w ∈ halfDisc a r} ∩
          {x | Disjoint (halfDisc a r) (closure (range (f x)))} ∩
          {x | z ∈ connectedComponentIn (H \ closure (range (f x))) (ratPt w)}) := by
    ext x
    simp only [LeftReach, mem_inter_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hzH, hzK, a, r, w, ha, hr, hd, hw, hc⟩
      exact ⟨⟨hzH, hzK⟩, a, r, w, ⟨⟨ha, hr, hw⟩, hd⟩, hc⟩
    · rintro ⟨⟨hzH, hzK⟩, a, r, w, ⟨⟨ha, hr, hw⟩, hd⟩, hc⟩
      exact ⟨hzH, hzK, a, r, w, ha, hr, hd, hw, hc⟩
  rw [e]
  exact ((MeasurableSet.const _).inter h1).inter (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun r =>
    MeasurableSet.iUnion fun w => ((MeasurableSet.const _).inter (h2 a r)).inter (h3 w))

/-- **The hitting code read from the counterflow set is measurable in the family.** -/
theorem measurable_lbCode {f : X → ℚ → ℂ} (hf : ∀ q, Measurable fun x => f x q) :
    Measurable fun x => lbCode (closure (range (f x))) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hm : ∀ z, Measurable fun x => LeftReach (closure (range (f x))) z :=
    fun z => measurableSet_setOfPred.1 (measurableSet_leftReach hf z)
  have hS : Measurable fun x => LBHit (closure (range (f x))) i := by
    unfold LBHit
    exact measurable_const.or ((Measurable.exists fun p => measurable_const.and (hm _)).and
      (Measurable.exists fun p => Measurable.exists fun ρ => measurable_const.and (measurable_const.and
        (Measurable.forall fun q => measurable_const.imp (hm _).not))))
  unfold lbCode
  exact Measurable.ite (measurableSet_setOfPred.2 hS) measurable_const measurable_const

end InteractingSLE.Sec5.Cond44Ref
