/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7Carrier
import InteractingSLE.Spec.Supplement.GB7aFlow
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# Measurable events for re-integrating GB7a through the G7 kernel

Packet PROVE-G7GB7A. The reduction of `Theorem15D5.G7GB7aFirstHitStatement` (`G7FirstHit.lean`) applies Lemma GB7a
(`Supp8.GB7aFlowStatement`) to the conditional flow line of the G7 carrier under its kernel `K c` and integrates the
result back to the original probability space. Only measurable events can be integrated back
(`Restart.ae_mem_of_compProd_eq`), and the GB7a event depends on the datum `c` as well as on the canonical path, so
it is integrated as a product event `A ×ˢ V`:

* `goodInterval κ θ a b`: the data whose word has no jump position in `[a, b]` and whose angle-`θ` outward cumulative
  weight on `[a, b]` is at least `κ/2 − 2` (with `[a, b]` on one side of `0`); measurable (`measurableSet_goodInterval`,
  through `measurable_boundaryWord_fn`);
* `VisitsStrip Γ U a b`: the path visits the closed strip `{im ≤ 0, a ≤ re ≤ b}` on `[0, U]`; measurable on a space
  of continuous paths (`measurableSet_exists_le_mem`: "visits a closed set" is a countable condition at rational
  times, by compactness);
* `ae_not_mem_prod_of_compProd_eq`: integrating a product event `A ×ˢ V` with `K c V = 0` for almost every `c ∈ A`.

## Main results

* `measurable_boundaryWord_index`, `measurable_boundaryWord_fn`, `measurableSet_goodInterval`;
* `measurableSet_exists_le_mem`, `measurableSet_visitsStrip`, `measurableSet_forall_im_nonneg`;
* `ae_not_mem_prod_of_compProd_eq`;
* `ae_im_nonneg_of_isFlowLine` (a flow line lies in `ℍ̄`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### The datum: measurability of the boundary function at a point -/

/-- The index of a point in a word (the number of jump positions strictly left of it) is measurable in the word. -/
theorem measurable_boundaryWord_index (y : ℝ) : Measurable fun c : BoundaryWord => c.index y := by
  have h : ∀ n : ℕ, Measurable fun c : BoundaryWord =>
      ((Finset.range n).filter fun i => c.2.1 i < y).card := by
    intro n
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.ite (measurableSet_lt ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
      measurable_const) measurable_const measurable_const
  have hF : Measurable fun p : BoundaryWord × ℕ => ((Finset.range p.2).filter fun i => p.1.2.1 i < y).card :=
    measurable_from_prod_countable_left fun n => h n
  exact hF.comp (measurable_id.prodMk measurable_fst)

/-- The boundary function of a word at a fixed point is measurable in the word. -/
theorem measurable_boundaryWord_fn (y : ℝ) : Measurable fun c : BoundaryWord => c.fn y := by
  have hG : Measurable fun p : BoundaryWord × ℕ => p.1.2.2 p.2 :=
    measurable_from_prod_countable_left fun n => (measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)
  exact hG.comp (measurable_id.prodMk (measurable_boundaryWord_index y))

/-- The data whose word has no jump position in `[a, b]` and whose angle-`θ` outward cumulative weight there is at
least `κ/2 − 2`, with `[a, b]` right of `0` (weight `cumWeightRight`) or left of `0` (weight `cumWeightLeft`). -/
def goodInterval (κ θ a b : ℝ) : Set BoundaryWord :=
  {c | (∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i) ∧
    ((0 < a ∧ κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn a + θ * QuantumZipper.chiC κ)) ∨
      (b < 0 ∧ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn a + θ * QuantumZipper.chiC κ)))}

theorem measurableSet_goodInterval (κ θ a b : ℝ) : MeasurableSet (goodInterval κ θ a b) := by
  have hpos : MeasurableSet {c : BoundaryWord | ∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i} := by
    have : {c : BoundaryWord | ∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i} =
        ⋂ i : ℕ, ({c : BoundaryWord | c.1 ≤ i} ∪ ({c | c.2.1 i < a} ∪ {c | b < c.2.1 i})) := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter, mem_union]
      refine ⟨fun h i => ?_, fun h i hi => ?_⟩
      · by_cases hi : i < c.1
        · exact Or.inr (h i hi)
        · exact Or.inl (not_lt.1 hi)
      · rcases h i with h' | h'
        · exact absurd hi (not_lt.2 h')
        · exact h'
    rw [this]
    have hi : ∀ i : ℕ, Measurable fun c : BoundaryWord => c.2.1 i :=
      fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
    exact MeasurableSet.iInter fun i => (measurable_fst (measurableSet_Iic (a := i))).union
      ((measurableSet_lt (hi i) measurable_const).union (measurableSet_lt measurable_const (hi i)))
  have hR : Measurable fun c : BoundaryWord =>
      Sec4.cumWeightRight κ (c.fn a + θ * QuantumZipper.chiC κ) := by
    unfold Sec4.cumWeightRight
    exact (((measurable_boundaryWord_fn a).add_const _).div_const _).sub_const _
  have hL : Measurable fun c : BoundaryWord =>
      Sec4.cumWeightLeft κ (c.fn a + θ * QuantumZipper.chiC κ) := by
    unfold Sec4.cumWeightLeft
    exact (((measurable_boundaryWord_fn a).add_const _).neg.div_const _).sub_const _
  have : goodInterval κ θ a b = {c : BoundaryWord | ∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i} ∩
      (({_c : BoundaryWord | 0 < a} ∩ {c | κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn a + θ * QuantumZipper.chiC κ)}) ∪
        ({_c : BoundaryWord | b < 0} ∩
          {c | κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn a + θ * QuantumZipper.chiC κ)})) := by
    ext c
    simp [goodInterval]
  rw [this]
  exact hpos.inter (((MeasurableSet.const _).inter (measurableSet_le measurable_const hR)).union
    ((MeasurableSet.const _).inter (measurableSet_le measurable_const hL)))

/-- On a good interval the word has no jump, and its boundary function is the one at the left end. -/
theorem goodInterval_notMem_jumps {κ θ a b : ℝ} {c : BoundaryWord} (hc : c ∈ goodInterval κ θ a b) {y : ℝ}
    (hy : y ∈ Icc a b) : y ∉ c.jumps := by
  intro hyJ
  obtain ⟨i, hi, rfl⟩ := BoundaryWord.mem_jumps.1 hyJ
  rcases hc.1 i hi with h | h
  · exact absurd hy.1 (not_le.2 h)
  · exact absurd hy.2 (not_le.2 h)

/-- A word with no jump position in `[a, b]` has the same boundary value on all of `[a, b]`. -/
theorem fn_eq_of_positions {a b : ℝ} {c : BoundaryWord} (hpos : ∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i)
    {y : ℝ} (hy : y ∈ Icc a b) : c.fn y = c.fn a := by
  have hidx : c.index y = c.index a := by
    unfold BoundaryWord.index
    refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
    rcases hpos i (Finset.mem_range.1 hi) with h | h
    · exact iff_of_true (h.trans_le hy.1) h
    · exact iff_of_false (fun h' => absurd (h'.trans_le hy.2) (not_lt.2 h.le))
        (fun h' => absurd (h'.trans_le (hy.1.trans hy.2)) (not_lt.2 h.le))
  unfold BoundaryWord.fn
  rw [hidx]

theorem goodInterval_fn_eq {κ θ a b : ℝ} {c : BoundaryWord} (hc : c ∈ goodInterval κ θ a b) {y : ℝ}
    (hy : y ∈ Icc a b) : c.fn y = c.fn a :=
  fn_eq_of_positions hc.1 hy

/-! ### Paths: visiting a closed set -/

section Paths

variable {S : Type*} [MeasurableSpace S] {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}

/-- **Visiting a closed set is measurable** for measurable continuous paths with a measurable closed available
interval: the path visits `F` on `[0, U]` iff for some `N` and every `m` some rational time in `[0, min(N, U)]` is
`1/(m+1)`-close to `F` (compactness of `[0, N] ∩ [0, U]`). -/
theorem measurableSet_exists_le_mem (hU : Measurable U) (hΓ : ∀ t, Measurable fun s => Γ s t)
    (hc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) {F : Set ℂ} (hF : IsClosed F) :
    MeasurableSet {s | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s ∧ Γ s t ∈ F} := by
  rcases F.eq_empty_or_nonempty with hF0 | hFne
  · have : {s | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s ∧ Γ s t ∈ F} = ∅ := by
      ext s; simp [hF0]
    rw [this]; exact MeasurableSet.empty
  have heq : {s | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s ∧ Γ s t ∈ F} =
      ⋃ N : ℕ, ⋂ m : ℕ, ⋃ q : ℚ, ({_s : S | ((q : ℝ).toNNReal : ℝ) ≤ N} ∩
        ({s | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U s} ∩
          {s | infDist (Γ s (q : ℝ).toNNReal) F < 1 / ((m : ℝ) + 1)})) := by
    ext s
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff]
    constructor
    · rintro ⟨t, htU, htF⟩
      obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
      refine ⟨N, fun m => ?_⟩
      have hcw := (hc s) t htU
      rw [Metric.continuousWithinAt_iff] at hcw
      obtain ⟨ε, hε, hδ⟩ := hcw (1 / ((m : ℝ) + 1)) (by positivity)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) - ε < t by linarith)
      have hqt : (q : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hq2.le
      refine ⟨q, ?_, ?_, ?_⟩
      · exact (NNReal.coe_le_coe.2 hqt).trans hN
      · exact (ENNReal.coe_le_coe.2 hqt).trans htU
      · have hmem : (q : ℝ).toNNReal ∈ {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ U s} :=
          (ENNReal.coe_le_coe.2 hqt).trans htU
        have hdist : dist (q : ℝ).toNNReal t < ε := by
          rw [NNReal.dist_eq, abs_lt]
          have h0 : (0 : ℝ) ≤ ((q : ℝ).toNNReal : ℝ) := NNReal.coe_nonneg _
          have h1 : (q : ℝ) ≤ ((q : ℝ).toNNReal : ℝ) := Real.le_coe_toNNReal _
          have h2 : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) ≤ t := NNReal.coe_le_coe.2 hqt
          constructor <;> linarith
        exact (infDist_le_dist_of_mem htF).trans_lt (hδ hmem hdist)
    · rintro ⟨N, hN⟩
      choose q hqN hqU hqF using hN
      set C : Set ℝ≥0 := Icc 0 (N : ℝ≥0) ∩ {t | (t : ℝ≥0∞) ≤ U s} with hC
      have hCc : IsCompact C := isCompact_Icc.inter_right
        (isClosed_le (ENNReal.continuous_coe) continuous_const)
      have hqC : ∀ m, (q m : ℝ).toNNReal ∈ C := fun m =>
        ⟨⟨zero_le, by exact_mod_cast hqN m⟩, hqU m⟩
      have hg : ContinuousOn (fun t => infDist (Γ s t) F) C :=
        (continuous_infDist_pt F).comp_continuousOn ((hc s).mono inter_subset_right)
      obtain ⟨t₀, ht₀C, hmin⟩ := hCc.exists_isMinOn ⟨_, hqC 0⟩ hg
      have hle : ∀ m : ℕ, infDist (Γ s t₀) F < 1 / ((m : ℝ) + 1) := fun m =>
        (hmin (hqC m)).trans_lt (hqF m)
      have hz : infDist (Γ s t₀) F = 0 := by
        refine le_antisymm (le_of_not_gt fun hpos => ?_) infDist_nonneg
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
        exact absurd (hle m) (not_lt.2 hm.le)
      refine ⟨t₀, ht₀C.2, ?_⟩
      rw [← hF.closure_eq, mem_closure_iff_infDist_zero hFne]
      exact hz
  rw [heq]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
  refine (MeasurableSet.const _).inter ((measurableSet_le measurable_const hU).inter ?_)
  exact measurableSet_lt ((continuous_infDist_pt F).measurable.comp (hΓ _)) measurable_const

/-- The path visits the closed strip `{im ≤ 0, a ≤ re ≤ b}` on `[0, U]`. -/
def VisitsStrip (γ : ℝ≥0 → ℂ) (V : ℝ≥0∞) (a b : ℝ) : Prop :=
  ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ∧ γ t ∈ {z : ℂ | z.im ≤ 0 ∧ a ≤ z.re ∧ z.re ≤ b}

theorem isClosed_strip (a b : ℝ) : IsClosed {z : ℂ | z.im ≤ 0 ∧ a ≤ z.re ∧ z.re ≤ b} :=
  (isClosed_le Complex.continuous_im continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))

theorem measurableSet_visitsStrip (hU : Measurable U) (hΓ : ∀ t, Measurable fun s => Γ s t)
    (hc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) (a b : ℝ) :
    MeasurableSet {s | VisitsStrip (Γ s) (U s) a b} :=
  measurableSet_exists_le_mem hU hΓ hc (isClosed_strip a b)

/-- The path stays in `ℍ̄` on `[0, U]` (a measurable event). -/
theorem measurableSet_forall_im_nonneg (hU : Measurable U) (hΓ : ∀ t, Measurable fun s => Γ s t)
    (hc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) :
    MeasurableSet {s | ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s → 0 ≤ (Γ s t).im} := by
  have heq : {s | ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s → 0 ≤ (Γ s t).im} =
      (⋃ n : ℕ, {s | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s ∧ Γ s t ∈ {z : ℂ | z.im ≤ -(1 / ((n : ℝ) + 1))}})ᶜ := by
    ext s
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists, not_and]
    constructor
    · intro h n t ht hz
      have := h t ht
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro h t ht
      refine le_of_not_gt fun hlt => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hlt)
      exact h n t ht (show (Γ s t).im ≤ -(1 / ((n : ℝ) + 1)) by linarith)
  rw [heq]
  exact (MeasurableSet.iUnion fun n => measurableSet_exists_le_mem hU hΓ hc
    (isClosed_le Complex.continuous_im continuous_const)).compl

end Paths

/-! ### Integrating a product event through the kernel -/

/-- **Integrating a product event.** If `K` is the conditional law of `X` given `β` on `M` and `K c V = 0` for
almost every datum `c ∈ A` (`A`, `V` measurable), then almost surely on `M`, not both `β ∈ A` and `X ∈ V`. -/
theorem ae_not_mem_prod_of_compProd_eq {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {A : Set C} {V : Set S} (hA : MeasurableSet A) (hV : MeasurableSet V)
    (hK : ∀ᵐ c ∂(P.restrict M).map β, c ∈ A → K c V = 0) :
    ∀ᵐ ω ∂P, ω ∈ M → ¬ (β ω ∈ A ∧ X ω ∈ V) := by
  have hzero : (P.restrict M) ((fun ω => (β ω, X ω)) ⁻¹' (A ×ˢ V)) = 0 := by
    rw [← Measure.map_apply (hβ.prodMk hX) (hA.prod hV), hlaw, Measure.compProd_apply_prod hA hV]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    exact (ae_restrict_iff' hA).2 hK
  rw [← ae_restrict_iff' hM]
  refine ae_iff.2 ?_
  have hset : {ω | ¬¬(β ω ∈ A ∧ X ω ∈ V)} = (fun ω => (β ω, X ω)) ⁻¹' (A ×ˢ V) := by
    ext ω; simp
  rw [hset]
  exact hzero

/-! ### A flow line lies in the closed half-plane -/

/-- A flow line lies almost surely in `ℍ̄` on its closed available interval. -/
theorem ae_im_nonneg_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → 0 ≤ (η ω t).im := by
  obtain ⟨_, _, W, _, _, _, -, hcoup, htr⟩ := hη
  filter_upwards [htr, hcoup.1.2.2.2.2] with ω hω hpath t ht
  have h0 := Sec7.IsGeneratingTrace.mem_Hbar hω hpath.2.2.2.1 hpath.1 ht
  have him : (η ω t - x).im = (η ω t).im := by simp
  rw [← him]
  exact h0

end Supp7

end InteractingSLE
