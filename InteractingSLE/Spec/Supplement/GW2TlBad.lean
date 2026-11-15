/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdnLife
import InteractingSLE.Spec.Supplement.GW2TkLife
import InteractingSLE.Spec.Restart.FlowCodeWord

/-!
# N4 item 1 in launch coordinates, part 1: the distance to a launch word's bad set

Packet PROVE-GW2-RELDET (decision D20, option (A)). The candidate's death is its first entrance into the closed bad set
of its LAUNCH word (`GW2Rd.ae_candidate_life_badEntrance`). The death gauge reads the distance of the launch trace to
that set, for a word read off the history. Here the distance, as a Borel function of the word and the point.

* `badPreB κ b θ`, `badPre κ θ w`: the real points `y ≠ 0` beyond which the outward cumulative weight of the flow line
  from `0` at angle `θ` is `≤ −2`; their closure is PROVE-GW2-SDE's `GW2Sdn.badSet κ b θ 0` (D10's set);
* **`closure_badSet_flowLine`**: the closure of NOJUMP's bad set of the flow-line word (`SB.Vr.badSet`, the set of
  `ae_candidate_life_badEntrance`) is `GW2Sdn.badSetC κ b θ 0`;
* `badDist κ θ w z`: the distance from `z` to that set, truncated at `1` (and `1` if the set is empty);
  `badDist_nonneg`, `badDist_le_one`, **`continuous_badDist`**, **`badDist_eq_zero_iff`**;
* **`measurable_badDist`**, `measurable_badDist_comp`: jointly Borel in the word and the point (the bad set of a word
  has no isolated points, so rational points suffice: `exists_rat_mem_badPre`, `infEDist_badSetC`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rd

open PiecewiseConstantBoundaryData (leftLim rightLim)
open Restart (BoundaryWord)

/-! ### The bad set of boundary data -/

/-- The real points `y ≠ 0` beyond which the outward cumulative weight of the flow line from `0` at angle `θ` is
`≤ −2` (D10's set before the closure). -/
def badPreB (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) : Set ℝ :=
  {y | 0 < y ∧ Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ) ≤ -2} ∪
    {y | y < 0 ∧ Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ) ≤ -2}

theorem badSet_eq_closure (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) : GW2Sdn.badSet κ b θ 0 = closure (badPreB κ b θ) := rfl

theorem mem_badSetC_iff {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {z : ℂ} :
    z ∈ GW2Sdn.badSetC κ b θ 0 ↔ z.im = 0 ∧ z.re ∈ closure (badPreB κ b θ) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Complex.ofReal_im y, by rw [Complex.ofReal_re]; exact hy⟩
  · rintro ⟨him, hre⟩
    exact ⟨z.re, hre, Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im, him])⟩

section Flow

variable {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ)

include hκ hb in
theorem wR_eq_cumWeightRight {y : ℝ} (hy : 0 < y) :
    SB.Vq.wR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) y =
      Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ) := by
  have h := SB.Vr.cumWeightRight_rightLim_flowLine hκ hb 0 θ hy
  rw [add_zero] at h
  exact h.symm

include hκ hb in
theorem wL_eq_cumWeightLeft {y : ℝ} (hy : y < 0) :
    SB.Vq.wL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) y =
      Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ) := by
  have h := SB.Vr.cumWeightLeft_leftLim_flowLine hκ hb 0 θ hy
  rw [add_zero] at h
  exact h.symm

/-- Just right of `0` the right cumulative weight is its value at `0`. -/
theorem eventually_wR_eq {n : ℕ} (xR ρR : Fin n → ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), SB.Vq.wR xR ρR t = SB.Vq.wR xR ρR 0 := by
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, (xR j ≤ t ↔ xR j ≤ 0) := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : xR j ≤ 0
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact ⟨fun _ => hj, fun _ => hj.trans ht.le⟩
    · filter_upwards [Ioo_mem_nhdsGT (lt_of_not_ge hj)] with t ht
      exact ⟨fun h => absurd (h.trans_lt ht.2) (lt_irrefl _), fun h => absurd h hj⟩
  filter_upwards [hall] with t ht
  unfold SB.Vq.wR
  exact Finset.sum_congr (Finset.filter_congr fun j _ => ht j) fun _ _ => rfl

/-- Just left of `0` the left cumulative weight is its value at `0`. -/
theorem eventually_wL_eq {n : ℕ} (xL ρL : Fin n → ℝ) :
    ∀ᶠ t in 𝓝[<] (0 : ℝ), SB.Vq.wL xL ρL t = SB.Vq.wL xL ρL 0 := by
  have hall : ∀ᶠ t in 𝓝[<] (0 : ℝ), ∀ i, (t ≤ xL i ↔ 0 ≤ xL i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : 0 ≤ xL i
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
      exact ⟨fun _ => hi, fun _ => ht.le.trans hi⟩
    · filter_upwards [Ioo_mem_nhdsLT (lt_of_not_ge hi)] with t ht
      exact ⟨fun h => absurd (ht.1.trans_le h) (lt_irrefl _), fun h => absurd h hi⟩
  filter_upwards [hall] with t ht
  unfold SB.Vq.wL
  exact Finset.sum_congr (Finset.filter_congr fun i _ => ht i) fun _ _ => rfl

theorem zero_mem_closure_of_eventually {S : Set ℝ} {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 0)
    (h : ∀ᶠ t in l, t ∈ S) : (0 : ℝ) ∈ closure S :=
  mem_closure_iff_frequently.2 (h.frequently.filter_mono hl)

include hκ hb in
/-- **NOJUMP's bad set of the flow-line word lies in D10's closed set.** -/
theorem badSet_subset_badSetC :
    SB.Vr.badSet (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) ⊆
      GW2Sdn.badSetC κ b θ 0 := by
  intro z hz
  obtain ⟨him, hcase⟩ := hz
  refine mem_badSetC_iff.2 ⟨him, ?_⟩
  rcases hcase with ⟨hy0, hy⟩ | ⟨hy0, hy⟩
  · rcases eq_or_lt_of_le hy0 with h0 | hpos
    · have hy' : SB.Vq.wR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) 0 ≤ -2 := by
        have h := hy
        rwa [← h0] at h
      rw [← h0]
      refine zero_mem_closure_of_eventually (l := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds ?_
      filter_upwards [eventually_wR_eq (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ), self_mem_nhdsWithin]
        with t ht (htpos : 0 < t)
      refine Or.inl ⟨htpos, ?_⟩
      rw [← wR_eq_cumWeightRight hκ hb θ htpos, ht]
      exact hy'
    · exact subset_closure (Or.inl ⟨hpos, by rw [← wR_eq_cumWeightRight hκ hb θ hpos]; exact hy⟩)
  · rcases eq_or_lt_of_le hy0 with h0 | hneg
    · have hy' : SB.Vq.wL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) 0 ≤ -2 := by
        have h := hy
        rwa [h0] at h
      rw [h0]
      refine zero_mem_closure_of_eventually (l := 𝓝[<] (0 : ℝ)) nhdsWithin_le_nhds ?_
      filter_upwards [eventually_wL_eq (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ), self_mem_nhdsWithin]
        with t ht (htneg : t < 0)
      refine Or.inr ⟨htneg, ?_⟩
      rw [← wL_eq_cumWeightLeft hκ hb θ htneg, ht]
      exact hy'
    · exact subset_closure (Or.inr ⟨hneg, by rw [← wL_eq_cumWeightLeft hκ hb θ hneg]; exact hy⟩)

include hκ hb in
/-- **The closure of NOJUMP's bad set of the flow-line word is D10's set** `GW2Sdn.badSetC κ b θ 0`. -/
theorem closure_badSet_flowLine :
    closure (SB.Vr.badSet (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ)) = GW2Sdn.badSetC κ b θ 0 := by
  refine le_antisymm (closure_minimal (badSet_subset_badSetC hκ hb θ) (GW2Sdn.isClosed_badSetC κ b θ 0)) ?_
  have hsub : (fun y : ℝ => (y : ℂ)) '' badPreB κ b θ ⊆
      SB.Vr.badSet (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨Complex.ofReal_im y, ?_⟩
    rw [Complex.ofReal_re]
    rcases hy with ⟨hpos, hy⟩ | ⟨hneg, hy⟩
    · exact Or.inl ⟨hpos.le, by rw [wR_eq_cumWeightRight hκ hb θ hpos]; exact hy⟩
    · exact Or.inr ⟨hneg.le, by rw [wL_eq_cumWeightLeft hκ hb θ hneg]; exact hy⟩
  calc GW2Sdn.badSetC κ b θ 0 = (fun y : ℝ => (y : ℂ)) '' closure (badPreB κ b θ) := rfl
    _ ⊆ closure ((fun y : ℝ => (y : ℂ)) '' badPreB κ b θ) :=
      image_closure_subset_closure_image Complex.continuous_ofReal
    _ ⊆ _ := closure_mono hsub

end Flow

/-! ### The truncated distance -/

/-- **The distance to a word's bad set**, truncated at `1` (`1` when the set is empty). -/
def badDist (κ θ : ℝ) (w : BoundaryWord) (z : ℂ) : ℝ :=
  (min 1 (Metric.infEDist z (GW2Sdn.badSetC κ w.fn θ 0))).toReal

variable {κ θ : ℝ}

theorem min_one_ne_top (e : ℝ≥0∞) : min 1 e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)

theorem badDist_nonneg (w : BoundaryWord) (z : ℂ) : 0 ≤ badDist κ θ w z := ENNReal.toReal_nonneg

theorem badDist_le_one (w : BoundaryWord) (z : ℂ) : badDist κ θ w z ≤ 1 := by
  unfold badDist
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (min_le_left 1 (Metric.infEDist z (GW2Sdn.badSetC κ w.fn θ 0)))
  rwa [ENNReal.toReal_one] at h

/-- **The distance is continuous in the point.** -/
theorem continuous_badDist (w : BoundaryWord) : Continuous fun z => badDist κ θ w z :=
  ENNReal.continuousOn_toReal.comp_continuous (continuous_const.min Metric.continuous_infEDist)
    fun _ => min_one_ne_top _

/-- **The distance vanishes exactly on the bad set.** -/
theorem badDist_eq_zero_iff (w : BoundaryWord) (z : ℂ) :
    badDist κ θ w z = 0 ↔ z ∈ GW2Sdn.badSetC κ w.fn θ 0 := by
  unfold badDist
  rw [ENNReal.toReal_eq_zero_iff]
  have hcl : closure (GW2Sdn.badSetC κ w.fn θ 0) = GW2Sdn.badSetC κ w.fn θ 0 :=
    (GW2Sdn.isClosed_badSetC κ w.fn θ 0).closure_eq
  constructor
  · rintro (h | h)
    · have h' : Metric.infEDist z (GW2Sdn.badSetC κ w.fn θ 0) = 0 := by
        rcases min_eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 one_ne_zero
        · exact h1
      rw [← hcl]
      exact Metric.mem_closure_iff_infEDist_zero.2 h'
    · exact absurd h (min_one_ne_top _)
  · intro hz
    left
    rw [Metric.infEDist_zero_of_mem hz]
    exact min_eq_right zero_le_one

theorem badDist_pos_iff (w : BoundaryWord) (z : ℂ) :
    0 < badDist κ θ w z ↔ z ∉ GW2Sdn.badSetC κ w.fn θ 0 := by
  rw [← badDist_eq_zero_iff w z]
  exact ⟨fun h he => absurd he h.ne', fun h => lt_of_le_of_ne (badDist_nonneg w z) (Ne.symm h)⟩

/-! ### Borel measurability -/

/-- The bad points of a word before the closure. -/
abbrev badPre (κ θ : ℝ) (w : BoundaryWord) : Set ℝ := badPreB κ w.fn θ

/-- **A word's bad set has no isolated points**: rational bad points approximate every bad point. -/
theorem exists_rat_mem_badPre {w : BoundaryWord} {y : ℝ} (hy : y ∈ badPre κ θ w) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, (q : ℝ) ∈ badPre κ θ w ∧ dist (q : ℝ) y < ε := by
  rcases hy with ⟨hpos, hy⟩ | ⟨hneg, hy⟩
  · obtain ⟨b, hyb, hb⟩ := w.exists_gt_bound y
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hyb (show y < y + ε by linarith))
    have hidx : w.indexLE q = w.indexLE y := by
      unfold BoundaryWord.indexLE
      have e : ((Finset.range w.1).filter fun i => w.2.1 i ≤ (q : ℝ)) =
          (Finset.range w.1).filter fun i => w.2.1 i ≤ y := by
        refine Finset.filter_congr fun i hi => ⟨fun h => ?_, fun h => h.trans hq1.le⟩
        by_contra hne
        have := hb i (Finset.mem_range.1 hi) (lt_of_not_ge hne)
        linarith [min_le_left b (y + ε)]
      rw [e]
    have hlim : rightLim w.fn q = rightLim w.fn y := by
      rw [BoundaryWord.rightLim_fn, BoundaryWord.rightLim_fn, hidx]
    refine ⟨q, Or.inl ⟨hpos.trans hq1, by rw [hlim]; exact hy⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_right b (y + ε)]
  · obtain ⟨a, hay, ha⟩ := w.exists_lt_bound y
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hay (show y - ε < y by linarith))
    have hidx : w.index q = w.index y := by
      unfold BoundaryWord.index
      have e : ((Finset.range w.1).filter fun i => w.2.1 i < (q : ℝ)) =
          (Finset.range w.1).filter fun i => w.2.1 i < y := by
        refine Finset.filter_congr fun i hi => ⟨fun h => h.trans hq2, fun h => ?_⟩
        exact (ha i (Finset.mem_range.1 hi) h).trans_lt ((le_max_left a (y - ε)).trans_lt hq1)
      rw [e]
    have hlim : leftLim w.fn q = leftLim w.fn y := by
      rw [BoundaryWord.leftLim_fn, BoundaryWord.leftLim_fn, hidx]
    refine ⟨q, Or.inr ⟨hq2.trans hneg, by rw [hlim]; exact hy⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right a (y - ε)]

open scoped Classical in
/-- **The distance to the bad set through rational bad points.** -/
theorem infEDist_badSetC (w : BoundaryWord) (z : ℂ) :
    Metric.infEDist z (GW2Sdn.badSetC κ w.fn θ 0) =
      ⨅ q : ℚ, if (q : ℝ) ∈ badPre κ θ w then edist z ((q : ℝ) : ℂ) else ⊤ := by
  have himg : GW2Sdn.badSetC κ w.fn θ 0 = closure ((fun y : ℝ => (y : ℂ)) '' badPre κ θ w) :=
    (Complex.isometry_ofReal.isClosedEmbedding.closure_image_eq _).symm
  rw [himg, Metric.infEDist_closure]
  refine le_antisymm (le_iInf fun q => ?_) (Metric.le_infEDist.2 ?_)
  · split_ifs with hq
    · exact Metric.infEDist_le_edist_of_mem ⟨(q : ℝ), hq, rfl⟩
    · exact le_top
  · rintro _ ⟨y, hy, rfl⟩
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨q, hq, hqy⟩ := exists_rat_mem_badPre hy (NNReal.coe_pos.2 hε)
    refine (iInf_le _ q).trans ?_
    simp only [hq, ↓reduceIte]
    calc edist z ((q : ℝ) : ℂ) ≤ edist z (y : ℂ) + edist (y : ℂ) ((q : ℝ) : ℂ) := edist_triangle _ _ _
      _ ≤ edist z (y : ℂ) + ε := by
        gcongr
        rw [edist_dist, Complex.isometry_ofReal.dist_eq, dist_comm]
        exact (ENNReal.ofReal_le_ofReal hqy.le).trans (by rw [ENNReal.ofReal_coe_nnreal])

theorem measurable_cumWeightRight_rightLim (κ θ y : ℝ) :
    Measurable fun w : BoundaryWord => Sec4.cumWeightRight κ (rightLim w.fn y + θ * chiC κ) := by
  have hR : Measurable fun w : BoundaryWord => rightLim w.fn y :=
    BoundaryWord.measurable_rightLim.comp (measurable_id.prodMk measurable_const)
  unfold Sec4.cumWeightRight
  exact ((hR.add_const _).div_const _).sub_const _

theorem measurable_cumWeightLeft_leftLim (κ θ y : ℝ) :
    Measurable fun w : BoundaryWord => Sec4.cumWeightLeft κ (leftLim w.fn y + θ * chiC κ) := by
  have hL : Measurable fun w : BoundaryWord => leftLim w.fn y :=
    BoundaryWord.measurable_leftLim.comp (measurable_id.prodMk measurable_const)
  unfold Sec4.cumWeightLeft
  exact ((hL.add_const _).neg.div_const _).sub_const _

theorem setOf_mem_badPre (κ θ y : ℝ) : {w : BoundaryWord | y ∈ badPre κ θ w} =
    ({_w : BoundaryWord | 0 < y} ∩ {w | Sec4.cumWeightRight κ (rightLim w.fn y + θ * chiC κ) ≤ -2}) ∪
      ({_w : BoundaryWord | y < 0} ∩ {w | Sec4.cumWeightLeft κ (leftLim w.fn y + θ * chiC κ) ≤ -2}) := by
  ext w
  simp only [badPre, badPreB, mem_union, mem_ofPred_eq, mem_inter_iff]

theorem measurableSet_mem_badPre (κ θ y : ℝ) : MeasurableSet {w : BoundaryWord | y ∈ badPre κ θ w} := by
  rw [setOf_mem_badPre]
  exact ((MeasurableSet.const _).inter
    (measurableSet_le (measurable_cumWeightRight_rightLim κ θ y) measurable_const)).union
    ((MeasurableSet.const _).inter (measurableSet_le (measurable_cumWeightLeft_leftLim κ θ y) measurable_const))

open scoped Classical in
/-- **The distance to a word's bad set is Borel in the word and the point.** -/
theorem measurable_badDist (κ θ : ℝ) : Measurable fun p : BoundaryWord × ℂ => badDist κ θ p.1 p.2 := by
  have e : (fun p : BoundaryWord × ℂ => badDist κ θ p.1 p.2) = fun p =>
      (min 1 (⨅ q : ℚ, if (q : ℝ) ∈ badPre κ θ p.1 then edist p.2 ((q : ℝ) : ℂ) else ⊤)).toReal := by
    funext p
    simp only [badDist, infEDist_badSetC]
  rw [e]
  refine ENNReal.measurable_toReal.comp (measurable_const.min (Measurable.iInf fun q => ?_))
  refine Measurable.ite ((measurableSet_mem_badPre κ θ (q : ℝ)).preimage measurable_fst) ?_ measurable_const
  exact (continuous_id.edist continuous_const).measurable.comp measurable_snd

/-- The distance at a measurable word and point is measurable. -/
theorem measurable_badDist_comp (κ θ : ℝ) {α : Type*} [MeasurableSpace α] {w : α → BoundaryWord} {z : α → ℂ}
    (hw : Measurable w) (hz : Measurable z) : Measurable fun a => badDist κ θ (w a) (z a) :=
  Measurable.comp (g := fun p : BoundaryWord × ℂ => badDist κ θ p.1 p.2) (f := fun a => (w a, z a))
    (measurable_badDist κ θ) (Measurable.prodMk hw hz)

end InteractingSLE.Theorem14.GW2Rd
