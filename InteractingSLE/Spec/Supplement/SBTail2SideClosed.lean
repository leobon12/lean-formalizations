/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Cond44RefCode
import InteractingSLE.WangWu.Prop420Ext

/-!
# Countable side membership retaining the real boundary of a closed set

Packet PROVE-T14-SBTAIL2. Unlike a half-plane hitting code, the full-ball
avoidance condition below retains real connectors and other real contacts.
Polygonal reachability and its measurability are reused from Theorem15D5.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Side

open Theorem15D5
open Sec5.Cond44Ref (isOpen_halfDisc isPreconnected_halfDisc
  ofReal_mem_closure_halfDisc exists_ratPt_mem lowPt closure_range_lowPt)

/-- For a closed set, a side is reached through a rational half-disc whose
full ball misses the set. The full ball also certifies the excluded real point. -/
theorem mem_sideOf_iff_ballReach {I : Set ℝ} (hI : IsOpen I) {A : Set ℂ}
    (hA : IsClosed A) {z : ℂ} :
    z ∈ WangWu.sideOf I A ↔ ∃ (x r : ℚ) (w : ℚ × ℚ) (k : ℕ),
      (x : ℝ) ∈ I ∧ 0 < r ∧ Disjoint (ball ((x : ℝ) : ℂ) (r : ℝ)) A ∧
      ratPt w ∈ Sec5.Cond44Ref.halfDisc x r ∧ Reach (H \ A) (ratPt w) k z := by
  constructor
  · rintro ⟨hz, x, hxI, hxA, hxcl⟩
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 hA.isOpen_compl _ hxA
    obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 hI _ hxI
    let m := min ε δ
    have hm : 0 < m := lt_min hε hδ
    obtain ⟨x', hx'1, hx'2⟩ := exists_rat_btwn (show x - m / 3 < x + m / 3 by linarith)
    obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn (show m / 3 < 2 * m / 3 by linarith)
    have hdx : dist ((x' : ℝ) : ℂ) (x : ℂ) < m / 3 := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have hx'I : (x' : ℝ) ∈ I := hδI (by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have := min_le_right ε δ
      constructor <;> linarith)
    have hxB : (x : ℂ) ∈ ball ((x' : ℝ) : ℂ) (r' : ℝ) := by
      rw [mem_ball, dist_comm]
      linarith
    have hBA : ball ((x' : ℝ) : ℂ) (r' : ℝ) ⊆ Aᶜ := by
      intro y hy
      apply hεA
      rw [mem_ball] at hy ⊢
      have := min_le_left ε δ
      calc dist y (x : ℂ) ≤ dist y ((x' : ℝ) : ℂ) + dist ((x' : ℝ) : ℂ) (x : ℂ) :=
          dist_triangle _ _ _
        _ < r' + m / 3 := add_lt_add hy hdx
        _ ≤ ε := by linarith
    obtain ⟨c, hcB, hcC⟩ := (_root_.mem_closure_iff.1 hxcl) _ isOpen_ball hxB
    have hcD : c ∈ Sec5.Cond44Ref.halfDisc x' r' := ⟨hcB, (connectedComponentIn_subset _ _ hcC).1⟩
    have hDC : Sec5.Cond44Ref.halfDisc x' r' ⊆ connectedComponentIn (H \ A) z := by
      have hsub := (isPreconnected_halfDisc x' r').subset_connectedComponentIn hcD
        (fun y hy => show y ∈ H \ A from ⟨hy.2, hBA hy.1⟩)
      rwa [← connectedComponentIn_eq hcC] at hsub
    obtain ⟨w, hw⟩ := exists_ratPt_mem (isOpen_halfDisc x' r') hcD
    have hzw : z ∈ connectedComponentIn (H \ A) (ratPt w) := by
      rw [← connectedComponentIn_eq (hDC hw)]
      exact mem_connectedComponentIn hz
    obtain ⟨k, hk⟩ := (mem_connectedComponentIn_iff_exists_reach
      (QuantumZipper.isOpen_H.sdiff hA)).1 hzw
    exact ⟨x', r', w, k, hx'I, by exact_mod_cast (show (0 : ℝ) < r' by linarith),
      disjoint_left.2 (fun y hy h => hBA hy h), hw, hk⟩
  · rintro ⟨x, r, w, k, hxI, hr, hd, hw, hR⟩
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hxA : ((x : ℝ) : ℂ) ∉ A :=
      fun h => disjoint_left.1 hd (mem_ball_self hr') h
    have hD : Sec5.Cond44Ref.halfDisc x r ⊆ connectedComponentIn (H \ A) (ratPt w) :=
      (isPreconnected_halfDisc x r).subset_connectedComponentIn hw
        (fun y hy => ⟨hy.2, fun h => disjoint_left.1 hd hy.1 h⟩)
    refine ⟨hR.mem, (x : ℝ), hxI, hxA, ?_⟩
    rw [← connectedComponentIn_eq hR.mem_connectedComponentIn]
    exact closure_mono hD (ofReal_mem_closure_halfDisc x r hr)

/-- A countable full-plane code for membership in the side of a closed set. -/
def SideCode {ι : Type*} (I : Set ℝ) (f : ι → ℂ) (z : ℂ) : Prop :=
  ∃ (x r : ℚ) (w : ℚ × ℚ) (k : ℕ), (x : ℝ) ∈ I ∧ 0 < r ∧
    (∀ q, f q ∉ ball ((x : ℝ) : ℂ) (r : ℝ)) ∧ ratPt w ∈ Sec5.Cond44Ref.halfDisc x r ∧
    Reach (closure (range (Sum.elim f lowPt)))ᶜ (ratPt w) k z

theorem sideCode_iff {ι : Type*} {I : Set ℝ} (hI : IsOpen I) (f : ι → ℂ) (z : ℂ) :
    SideCode I f z ↔ z ∈ WangWu.sideOf I (closure (range f)) := by
  rw [mem_sideOf_iff_ballReach hI isClosed_closure]
  unfold SideCode
  have hH : (closure (range (Sum.elim f lowPt)))ᶜ = H \ closure (range f) := by
    rw [Set.Sum.elim_range, closure_union, closure_range_lowPt]
    ext y
    simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le, Set.mem_sdiff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hH]
  refine exists_congr fun x => exists_congr fun r => exists_congr fun w => exists_congr fun k => ?_
  have hd : (∀ q, f q ∉ ball ((x : ℝ) : ℂ) (r : ℝ)) ↔
      Disjoint (ball ((x : ℝ) : ℂ) (r : ℝ)) (closure (range f)) := by
    constructor
    · intro h
      exact Disjoint.closure_right (disjoint_right.2 (by rintro _ ⟨q, rfl⟩; exact h q)) isOpen_ball
    · intro h q hq
      exact disjoint_left.1 h hq (subset_closure (mem_range_self q))
  rw [hd]

theorem measurableSet_sideCode {ι X : Type*} [Countable ι] [MeasurableSpace X] (I : Set ℝ)
    {f : X → ι → ℂ} (hf : ∀ q, Measurable fun x => f x q) {z : X → ℂ}
    (hz : Measurable z) : MeasurableSet {x | SideCode I (f x) (z x)} := by
  have hg : ∀ i, Measurable fun x => Sum.elim (f x) lowPt i := by
    rintro (q | p)
    · exact hf q
    · exact measurable_const
  refine measurableSet_setOfPred.2 (Measurable.exists fun x₀ => Measurable.exists fun r =>
    Measurable.exists fun w => Measurable.exists fun k => ?_)
  exact measurable_const.and (measurable_const.and ((Measurable.forall fun q =>
    (measurableSet_setOfPred.1 (hf q isOpen_ball.measurableSet)).not).and
      (measurable_const.and (measurableSet_setOfPred.1
        (measurableSet_reach hg measurable_const k hz)))))

/-- A measurable dense point family for the full physical set suffices for
joint side measurability. The equality is required only almost everywhere. -/
theorem exists_measurable_side_version_of_dense_code {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → Set ℂ} {f : Ω → ι → ℂ}
    (hf : ∀ q, Measurable fun ω => f ω q)
    (hcode : ∀ᵐ ω ∂P, A ω = closure (range (f ω))) {I : Set ℝ} (hI : IsOpen I) :
    ∃ S : Ω → Set ℂ, MeasurableSet {p : Ω × ℂ | p.2 ∈ S p.1} ∧
      ∀ᵐ ω ∂P, WangWu.sideOf I (A ω) = S ω := by
  refine ⟨fun ω => {z | SideCode I (f ω) z},
    measurableSet_sideCode I (fun q => (hf q).comp measurable_fst) measurable_snd, ?_⟩
  filter_upwards [hcode] with ω hω
  rw [hω]
  ext z
  exact (sideCode_iff hI (f ω) z).symm

end InteractingSLE.Theorem14.SB.Side
