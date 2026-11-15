/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux64
import InteractingSLE.Spec.Sec7.Lemma76Reflect
import InteractingSLE.Spec.Supplement.G7FirstHit

/-!
# Lemma 7.6 from the restart kernel at the disjoint pair

Packet PROVE-LEMMA76C. Specification §7.2, proof of Lemma 7.6 (pp. 267–270). The proof restarts the second path at
the disjoint retained pair in the chart of the joint unbounded component `D` (at the active tip, Aux. 59), where the
conditional field is a GFF whose boundary word carries the canonical heights (nested comparison, Aux. 60), and the
continuation is its angle-`θ₂` flow line (Aux. 61; Theorem 2.4's converse). A forbidden first exit (through the right
side of the first prefix) is, by the first-exit prime-end lemma, a visit of the chart path to the image of that side,
of height `λ − θ₁χ` (Aux. 64), or to its junction with the real boundary (Aux. 66): admissible points
(`IsAdmissibleRight`, `isAdmissibleRight_side`, `isAdmissibleRight_junction`). Almost surely the chart flow line
visits no admissible point (`ae_avoid_admissible`). This file proves the probabilistic assembly:

* `Lemma76KernelStatement` (named input, **not proved**): the restart kernel at the deterministic stops in the carrier
  form of Lemma G7 (`Supp7.G7RetainedPairStatement`), together with the pathwise reduction "a forbidden exit is a
  visit of the chart path to an admissible right point of the datum";
* measurable product events covering the visits of admissible points: `Supp7.goodInterval` × `VisitsStrip` (interval
  points, as in `G7FirstHit`) and `goodJunction` × `visitPointSet` (jump points);
* **`lemma76RightStatement_of_kernel`** and **`lemma76Statement_of_kernel`** (with the reflection,
  `lemma76Statement_of_right`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec7

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open Restart

/-! ### Visiting a point -/

section Paths

variable {S : Type*} [MeasurableSpace S] {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}

/-- The pairs `(y, s)` such that the path `Γ s` visits the real point `y` on `[0, U s]`. -/
def visitPointSet (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) : Set (ℝ × S) :=
  {p | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ U p.2 ∧ Γ p.2 t = (p.1 : ℂ)}

/-- **Visiting a point is measurable** in the point and the path (compactness of `[0, N] ∩ [0, U]`, rational times). -/
theorem measurableSet_visitPointSet (hU : Measurable U) (hΓ : ∀ t, Measurable fun s => Γ s t)
    (hc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) : MeasurableSet (visitPointSet Γ U) := by
  have heq : visitPointSet Γ U =
      ⋃ N : ℕ, ⋂ m : ℕ, ⋃ q : ℚ, ({_p : ℝ × S | ((q : ℝ).toNNReal : ℝ) ≤ N} ∩
        ({p : ℝ × S | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U p.2} ∩
          {p : ℝ × S | dist (Γ p.2 (q : ℝ).toNNReal) (p.1 : ℂ) < 1 / ((m : ℝ) + 1)})) := by
    ext ⟨y, s⟩
    simp only [visitPointSet, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff]
    constructor
    · rintro ⟨t, htU, hty⟩
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
        rw [← hty]
        exact hδ hmem hdist
    · rintro ⟨N, hN⟩
      choose q hqN hqU hqF using hN
      set C : Set ℝ≥0 := Icc 0 (N : ℝ≥0) ∩ {t | (t : ℝ≥0∞) ≤ U s} with hC
      have hCc : IsCompact C := isCompact_Icc.inter_right
        (isClosed_le (ENNReal.continuous_coe) continuous_const)
      have hqC : ∀ m, (q m : ℝ).toNNReal ∈ C := fun m =>
        ⟨⟨zero_le, by exact_mod_cast hqN m⟩, hqU m⟩
      have hg : ContinuousOn (fun t => dist (Γ s t) (y : ℂ)) C :=
        (continuous_id.dist continuous_const).comp_continuousOn ((hc s).mono inter_subset_right)
      obtain ⟨t₀, ht₀C, hmin⟩ := hCc.exists_isMinOn ⟨_, hqC 0⟩ hg
      have hle : ∀ m : ℕ, dist (Γ s t₀) (y : ℂ) < 1 / ((m : ℝ) + 1) := fun m =>
        (hmin (hqC m)).trans_lt (hqF m)
      have hz : dist (Γ s t₀) (y : ℂ) = 0 := by
        refine le_antisymm (le_of_not_gt fun hpos => ?_) dist_nonneg
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
        exact absurd (hle m) (not_lt.2 hm.le)
      exact ⟨t₀, ht₀C.2, dist_eq_zero.1 hz⟩
  rw [heq]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
  refine (MeasurableSet.const _).inter ((measurableSet_le measurable_const (hU.comp measurable_snd)).inter ?_)
  exact measurableSet_lt (((hΓ _).comp measurable_snd).dist (Complex.measurable_ofReal.comp measurable_fst))
    measurable_const

end Paths

/-! ### Jump points of a word -/

/-- The words with a jump position `c.2.1 i > 0` (index `i < c.1`), no position in `(c.2.1 i, b]`, and junction weight
`cumWeightRight κ (c(b) + θχ) > κ/2 − 4` (then `c(b)` is the right limit at the jump). -/
def goodJunction (κ θ : ℝ) (i : ℕ) (b : ℝ) : Set BoundaryWord :=
  {c | i < c.1 ∧ 0 < c.2.1 i ∧ c.2.1 i < b ∧ (∀ j < c.1, c.2.1 j ≤ c.2.1 i ∨ b < c.2.1 j) ∧
    κ / 2 - 4 < Sec4.cumWeightRight κ (c.fn b + θ * chiC κ)}

theorem measurableSet_goodJunction (κ θ : ℝ) (i : ℕ) (b : ℝ) : MeasurableSet (goodJunction κ θ i b) := by
  have hpos : Measurable fun c : BoundaryWord => c.2.1 i :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hcard : Measurable fun c : BoundaryWord => c.1 := measurable_fst
  have h1 : MeasurableSet {c : BoundaryWord | i < c.1} := hcard (measurableSet_Ioi (a := i))
  have h4 : MeasurableSet {c : BoundaryWord | ∀ j < c.1, c.2.1 j ≤ c.2.1 i ∨ b < c.2.1 j} := by
    have : {c : BoundaryWord | ∀ j < c.1, c.2.1 j ≤ c.2.1 i ∨ b < c.2.1 j} =
        ⋂ j : ℕ, ({c : BoundaryWord | c.1 ≤ j} ∪ ({c | c.2.1 j ≤ c.2.1 i} ∪ {c | b < c.2.1 j})) := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter, mem_union]
      refine ⟨fun h j => ?_, fun h j hj => ?_⟩
      · by_cases hj : j < c.1
        · exact Or.inr (h j hj)
        · exact Or.inl (not_lt.1 hj)
      · rcases h j with h' | h'
        · exact absurd hj (not_lt.2 h')
        · exact h'
    rw [this]
    have hposj : ∀ j : ℕ, Measurable fun c : BoundaryWord => c.2.1 j := fun j =>
      (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    refine MeasurableSet.iInter fun j => (hcard (measurableSet_Iic (a := j))).union
      ((measurableSet_le (hposj j) hpos).union (measurableSet_lt measurable_const (hposj j)))
  exact h1.inter ((measurableSet_lt measurable_const hpos).inter ((measurableSet_lt hpos measurable_const).inter
    (h4.inter (measurableSet_lt measurable_const
      (((Supp7.measurable_boundaryWord_fn b).add_const _).div_const _ |>.sub_const _)))))

theorem fn_eq_of_goodJunction {κ θ : ℝ} {i : ℕ} {b : ℝ} {c : BoundaryWord} (hc : c ∈ goodJunction κ θ i b)
    {y : ℝ} (hy : y ∈ Ioc (c.2.1 i) b) : c.fn y = c.fn b := by
  obtain ⟨-, -, -, hpos, -⟩ := hc
  have hidx : c.index y = c.index b := by
    unfold BoundaryWord.index
    refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
    rcases hpos j (Finset.mem_range.1 hj) with h | h
    · exact iff_of_true (h.trans_lt hy.1) (h.trans_lt (hy.1.trans_le hy.2))
    · exact iff_of_false (fun h' => absurd (h'.trans_le hy.2) (not_lt.2 h.le)) (fun h' => absurd h' (not_lt.2 h.le))
  unfold BoundaryWord.fn
  rw [hidx]

theorem fn_eq_of_positions_Ioc {i : ℕ} {b : ℝ} {c : BoundaryWord} (hpos : ∀ j < c.1, c.2.1 j ≤ c.2.1 i ∨ b < c.2.1 j)
    {y : ℝ} (hy : y ∈ Ioc (c.2.1 i) b) : c.fn y = c.fn b := by
  have hidx : c.index y = c.index b := by
    unfold BoundaryWord.index
    refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
    rcases hpos j (Finset.mem_range.1 hj) with h | h
    · exact iff_of_true (h.trans_lt hy.1) (h.trans_lt (hy.1.trans_le hy.2))
    · exact iff_of_false (fun h' => absurd (h'.trans_le hy.2) (not_lt.2 h.le)) (fun h' => absurd h' (not_lt.2 h.le))
  unfold BoundaryWord.fn
  rw [hidx]

theorem rightLim_fn_of_positions {i : ℕ} {b : ℝ} {c : BoundaryWord} (hib : c.2.1 i < b)
    (hpos : ∀ j < c.1, c.2.1 j ≤ c.2.1 i ∨ b < c.2.1 j) : rightLim c.fn (c.2.1 i) = c.fn b :=
  Sec4.rightLim_eq_of_forall hib fun _ ht => fn_eq_of_positions_Ioc hpos ⟨ht.1, ht.2.le⟩

theorem rightLim_fn_of_goodJunction {κ θ : ℝ} {i : ℕ} {b : ℝ} {c : BoundaryWord} (hc : c ∈ goodJunction κ θ i b) :
    rightLim c.fn (c.2.1 i) = c.fn b :=
  rightLim_fn_of_positions hc.2.2.1 hc.2.2.2.1

/-- **G12 under one conditional law**: for a datum in `goodJunction`, the conditional angle-`θ` flow line from `0`
almost surely does not visit the jump `c.2.1 i`. -/
theorem measure_visitPoint_eq_zero {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {S : Type} [MeasurableSpace S]
    {Q : Measure S} [IsProbabilityMeasure Q] {H : S → LQGMetric.DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ}
    {U : S → ℝ≥0∞} {c : BoundaryWord} (hgff : IsGFFWithBoundaryData Q H c.fn c.jumps)
    (hfl : IsFlowLine κ c.fn c.jumps 0 θ Q H Γ U) {i : ℕ} {b : ℝ} (hc : c ∈ goodJunction κ θ i b) :
    Q {s | (c.2.1 i, s) ∈ visitPointSet Γ U} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  have hG := (Supp7.g12FlowStatement κ hκ hκ4 c.fn c.jumps (BoundaryWord.isPiecewiseConstantBoundaryData c) 0 θ
    (c.2.1 i) Q H hgff Γ U hfl).1 hc.2.1
  rw [rightLim_fn_of_goodJunction hc] at hG
  filter_upwards [hG hc.2.2.2.2] with s hs
  rintro ⟨t, htU, hty⟩
  exact hs t htU hty

/-! ### Integrating an event through the kernel -/

/-- **Integrating a measurable event of `(datum, restart point)`** whose sections are null for almost every datum. -/
theorem ae_not_mem_of_compProd_eq {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {E : Set (C × S)} (hE : MeasurableSet E) (hK : ∀ᵐ c ∂(P.restrict M).map β, K c (Prod.mk c ⁻¹' E) = 0) :
    ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∉ E := by
  have hzero : (P.restrict M) ((fun ω => (β ω, X ω)) ⁻¹' E) = 0 := by
    rw [← Measure.map_apply (hβ.prodMk hX) hE, hlaw, Measure.compProd_apply hE]
    exact lintegral_eq_zero_of_ae_eq_zero hK
  rw [← ae_restrict_iff' hM]
  refine ae_iff.2 ?_
  have hset : {ω | ¬(β ω, X ω) ∉ E} = (fun ω => (β ω, X ω)) ⁻¹' E := by
    ext ω; simp
  rw [hset]
  exact hzero

/-! ### The named input and the assembly -/

/-- **Named input: the restart kernel of Lemma 7.6 at the disjoint pair, with the first-exit reduction**
(specification pp. 267–270). Setting of `Lemma76Statement` (`x₂ < x₁`, `θ₁ < θ₂ + π`, the deterministic stops
`r ∧ ζ₁`, `t ∧ ζ₂`). In the carrier form of Lemma G7 (`Supp7.G7RetainedPairStatement`): a canonical space `S` with
measurable coordinates (chart field `H`, chart path `Γ` continuous on its closed available interval, lifetime `U`), a
measurable event `M`, datum `β`, restart variable `X` and Markov kernel `K` with
* `K` the conditional law of `X` given `β` on `M`;
* for almost every datum `c`, under `K c`: `H` is a GFF with datum `c`, and `Γ` (lifetime `U`) its angle-`θ₂` flow
  line from `0` (the continuation of the second path in the chart of the joint unbounded component at its active tip:
  retained conditional law, canonical germs and seed, Aux. 59, 61; p. 268);
* almost surely, if the barrier fails (a forbidden first exit through the right side of the first prefix), then
  `ω ∈ M` and the chart path visits an admissible right point of the datum (the first-exit prime-end lemma and the
  heights of the exposed right side `λ − θ₁χ` and of its junction, Aux. 60 and the nested comparison, p. 269–270; these
  points are admissible by `isAdmissibleRight_side`, `isAdmissibleRight_junction`).

**Not proved in Lean.** -/
def Lemma76KernelStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ r t : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ : S → ℝ≥0 → ℂ)
      (U : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord) (X : Ω → S) (K : Kernel BoundaryWord S),
      Measurable H ∧ Measurable U ∧ (∀ s : ℝ≥0, Measurable fun x => Γ x s) ∧
      (∀ x, ContinuousOn (Γ x) {s | (s : ℝ≥0∞) ≤ U x}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β,
        IsGFFWithBoundaryData (K c) H c.fn c.jumps ∧ IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) H Γ U) ∧
      ∀ᵐ ω ∂P, ¬ FirstExitBarrier (η₁ ω) (truncAt (ζ₁ ω) r) (η₂ ω) (ζ₂ ω) (truncAt (ζ₂ ω) t) (lowerArc x₂ x₁) →
        ω ∈ M ∧ ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ U (X ω) ∧ ∃ y : ℝ, 0 < y ∧ Γ (X ω) s = y ∧
          IsAdmissibleRight κ θ₂ (β ω).fn (β ω).jumps y

/-- An admissible interval point lies in a rational window of `goodInterval` visited by the path. -/
theorem exists_goodInterval_of_admissible {κ θ : ℝ} {c : BoundaryWord} {y : ℝ} (hy0 : 0 < y) (hyJ : y ∉ c.jumps)
    (hw : κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn y + θ * chiC κ)) :
    ∃ q : ℚ × ℚ, c ∈ Supp7.goodInterval κ θ q.1 q.2 ∧ y ∈ Icc (q.1 : ℝ) q.2 := by
  obtain ⟨q₁, q₂, hyq, hqJ, hx1, -⟩ := Supp8.exists_rat_Ioo_avoid c.jumps hyJ hy0.ne
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hyq.1
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hyq.2
  have hpos : ∀ i < c.1, c.2.1 i < a ∨ b < c.2.1 i := by
    intro i hi
    by_contra hcon
    push Not at hcon
    exact hqJ (c.2.1 i) ⟨ha1.trans_le hcon.1, hcon.2.trans_lt hb2⟩ (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩)
  have hya : y ∈ Icc (a : ℝ) b := ⟨ha2.le, hb1.le⟩
  refine ⟨(a, b), ⟨hpos, Or.inl ⟨(hx1 hy0).trans_lt ha1, ?_⟩⟩, hya⟩
  rw [← Supp7.fn_eq_of_positions hpos hya]
  exact hw

/-- An admissible jump point is a `goodJunction` jump. -/
theorem exists_goodJunction_of_admissible {κ θ : ℝ} {c : BoundaryWord} {y : ℝ} (hy0 : 0 < y) (hyJ : y ∈ c.jumps)
    (hw : κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim c.fn y + θ * chiC κ)) :
    ∃ q : ℕ × ℚ, c ∈ goodJunction κ θ q.1 q.2 ∧ c.2.1 q.1 = y := by
  obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hyJ
  have hyJ' : y ∉ c.jumps.erase y := Finset.notMem_erase y _
  obtain ⟨q₁, q₂, hyq, hqJ, -, -⟩ := Supp8.exists_rat_Ioo_avoid (c.jumps.erase y) hyJ' hy0.ne
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hyq.2
  have hpos : ∀ j < c.1, c.2.1 j ≤ c.2.1 i ∨ (b : ℝ) < c.2.1 j := by
    intro j hj
    by_contra hcon
    push Not at hcon
    rw [hiy] at hcon
    refine hqJ (c.2.1 j) ⟨hyq.1.trans hcon.1, hcon.2.trans_lt hb2⟩ ?_
    exact Finset.mem_erase.2 ⟨hcon.1.ne', BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩⟩
  have hib : c.2.1 i < b := hiy ▸ hb1
  refine ⟨(i, b), ⟨hi, hiy ▸ hy0, hib, hpos, ?_⟩, hiy⟩
  rw [← rightLim_fn_of_positions hib hpos, hiy]
  exact hw

/-- **The first half of Lemma 7.6 from the restart kernel**: Aux. 64 and 66 at every admissible point
(`ae_avoid_admissible`, from GB7a and G12) under each conditional law, integrated back through the kernel. -/
theorem lemma76RightStatement_of_kernel (hK76 : Lemma76KernelStatement.{u}) : Lemma76RightStatement.{u} := by
  intro κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t
  obtain ⟨S, _, H, Γ, U, M, β, X, K, -, hU, hΓ, hc, hM, hβ, hX, hKm, hlaw, hker, hpath⟩ :=
    hK76 κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t
  -- interval points: GB7a under each conditional law
  have hI : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ M → ¬ (β ω ∈ Supp7.goodInterval κ θ₂ q.1 q.2 ∧
      X ω ∈ {s | Supp7.VisitsStrip (Γ s) (U s) q.1 q.2}) := fun q =>
    Supp7.ae_not_mem_prod_of_compProd_eq hM hβ hX hlaw (Supp7.measurableSet_goodInterval _ _ _ _)
      (Supp7.measurableSet_visitsStrip hU hΓ hc _ _) (by
        filter_upwards [hker] with c hc' hcA
        exact Supp7.measure_visitsStrip_eq_zero Supp8.gb7aFlowStatement hκ hκ4 hc'.1 hc'.2 hcA)
  -- jump points: G12 under each conditional law
  have hJ : ∀ q : ℕ × ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∉
      {p : BoundaryWord × S | p.1 ∈ goodJunction κ θ₂ q.1 q.2 ∧ (p.1.2.1 q.1, p.2) ∈ visitPointSet Γ U} := by
    intro q
    have hmeas : Measurable fun p : BoundaryWord × S => (p.1.2.1 q.1, p.2) :=
      (((measurable_pi_apply q.1).comp (measurable_fst.comp measurable_snd)).comp measurable_fst).prodMk
        measurable_snd
    refine ae_not_mem_of_compProd_eq hM hβ hX hlaw
      (((measurableSet_goodJunction _ _ _ _).preimage measurable_fst).inter
        ((measurableSet_visitPointSet hU hΓ hc).preimage hmeas)) ?_
    filter_upwards [hker] with c hc'
    by_cases hcA : c ∈ goodJunction κ θ₂ q.1 q.2
    · refine measure_mono_null (fun s hs => hs.2) (measure_visitPoint_eq_zero hκ hκ4 hc'.1 hc'.2 hcA)
    · have : Prod.mk c ⁻¹' {p : BoundaryWord × S | p.1 ∈ goodJunction κ θ₂ q.1 q.2 ∧
          (p.1.2.1 q.1, p.2) ∈ visitPointSet Γ U} = ∅ := by
        ext s; simp [hcA]
      rw [this, measure_empty]
  filter_upwards [hpath, ae_all_iff.2 hI, ae_all_iff.2 hJ] with ω hp hIω hJω
  by_contra hbar
  obtain ⟨hωM, s, hsU, y, hy0, hΓy, hadm⟩ := hp hbar
  rcases hadm with ⟨hyJ, hw⟩ | ⟨hyJ, hw⟩
  · obtain ⟨q, hcA, hyq⟩ := exists_goodInterval_of_admissible hy0 hyJ hw
    refine hIω q hωM ⟨hcA, s, hsU, ?_⟩
    rw [hΓy]
    simp only [mem_ofPred_eq, Complex.ofReal_im, le_refl, Complex.ofReal_re, true_and]
    exact hyq
  · obtain ⟨q, hcA, hqy⟩ := exists_goodJunction_of_admissible hy0 hyJ hw
    refine hJω q hωM ⟨hcA, s, hsU, ?_⟩
    rw [hΓy, hqy]

/-- **Lemma 7.6 (`Lemma76Statement`, both halves) from the restart kernel at the disjoint pair**: the first half by
`lemma76RightStatement_of_kernel`, the swapped half by reflection (`lemma76Statement_of_right`). -/
theorem lemma76Statement_of_kernel (hK76 : Lemma76KernelStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_right (lemma76RightStatement_of_kernel hK76)

end Sec7

end InteractingSLE
