import SupercriticalLFPPAS.Det.LSCConvergence
import SupercriticalLFPPAS.Local.Basic
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.MovingSetDist
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.FellBase
import SupercriticalLQGUniqueness.B2.LscTop.Limits

/-!
# Lemma 3.1 for lower semicontinuous metrics, and its probabilistic half (packet P32)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 3.1 (l. 226–244); planning audit
`planning/audits/SB1-sections-1-3.md` §2.8 and A11.

For metrics the neighbourhood infimum `f^{[η]}(p) = inf_{|q - p| < η} f(q)` of the paper (maximum
product distance) is the host `movingOpenSetDist f η u v` (infimum over `B_η(u) × B_η(v)`). The
event of Lemma 3.1 for a pair `(S, T)` of metrics is `NearCompare S T K M η ν`: for `p ∈ K` with
`T(p) ≤ M`, `S^{[η]}(p) ≤ T(p) + ν`.

* `nearCompare_eventually`: the deterministic Lemma 3.1 (from the landed
  `d1_lsc_convergence_neighborhoods`), in this `ℝ≥0∞`-valued form.
* `measurableSet_nearCompare`: for compact `K` the event is a Borel set of pairs of metrics. Its
  complement is a countable union of projections, along the compact factor `K`, of closed sets
  (joint lower semicontinuity of evaluation and joint upper semicontinuity of `movingOpenSetDist`).
  This replaces the sketch of Remark 3.3 for Lemma 3.1 (SB1 item 24).
* `nearCompare_subseq` (subsequence form) and `nearCompare_tendsto_measure` (the event has
  probability tending to one) for convergence in probability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (movingOpenSetDist
  movingOpenSetDist_joint_usc jointEval_lsc)

namespace SupercriticalLFPPAS.Local

/-- The event of Lemma 3.1 for the pair `(S, T)`: for every `p ∈ K` with `T(p) ≤ M`, the infimum
of `S` over the maximum-product `η`-ball around `p` is at most `T(p) + ν`. -/
def NearCompare (S T : LSCMetric) (K : Set (ℂ × ℂ)) (M η ν : ℝ) : Prop :=
  ∀ p ∈ K, T p ≤ ENNReal.ofReal M → movingOpenSetDist S η p.1 p.2 ≤ T p + ENNReal.ofReal ν

/-- The paper's neighbourhood infimum of the `EReal`-valued function of a metric is the
`ℝ≥0∞`-valued moving open-ball set distance. -/
theorem coe_movingOpenSetDist_eq_d1Near (S : LSCMetric) (η : ℝ) (p : ℂ × ℂ) :
    ((movingOpenSetDist S η p.1 p.2 : ℝ≥0∞) : EReal) = d1Near S.toLSCFun.1 η p := by
  have hball : ∀ q : ℂ × ℂ, q ∈ ball p.1 η ×ˢ ball p.2 η ↔ dist q p < η := by
    intro q
    rw [Prod.dist_eq, max_lt_iff, mem_prod, mem_ball, mem_ball]
  apply le_antisymm
  · refine le_iInf₂ fun q hq => ?_
    rw [LSCMetric.toLSCFun_apply, EReal.coe_ennreal_le_coe_ennreal_iff]
    exact iInf₂_le q ((hball q).2 hq)
  · have h0 : (0 : EReal) ≤ d1Near S.toLSCFun.1 η p := by
      refine le_iInf₂ fun q _ => ?_
      rw [LSCMetric.toLSCFun_apply]
      exact EReal.coe_ennreal_nonneg _
    rw [← EReal.coe_toENNReal h0, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun q hq => ?_
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal h0,
      ← LSCMetric.toLSCFun_apply]
    exact d1Near_le_of_dist _ ((hball q).1 hq)

/-- **Lemma 3.1, deterministic part**, for lower semicontinuous metrics: if `G n → D` in the
lower semicontinuous topology, then for each compact `K`, `M < ∞` and `η, ν > 0`, eventually
both `NearCompare (G n) D` and `NearCompare D (G n)` hold. -/
theorem nearCompare_eventually {G : ℕ → LSCMetric} {D : LSCMetric}
    (hconv : LSCTendsto (fun n => (G n).toLSCFun.1) D.toLSCFun.1)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (M : ℝ) {η ν : ℝ} (hη : 0 < η) (hν : 0 < ν) :
    ∀ᶠ n in atTop, NearCompare (G n) D K M η ν ∧ NearCompare D (G n) K M η ν := by
  have hd := d1_lsc_convergence_neighborhoods (fun n => (G n).toLSCFun.1) D.toLSCFun.1
    (fun n => (G n).toLSCFun.2) D.toLSCFun.2
    (fun n p => by rw [LSCMetric.toLSCFun_apply]; exact EReal.coe_ennreal_nonneg _)
    (fun p => by rw [LSCMetric.toLSCFun_apply]; exact EReal.coe_ennreal_nonneg _)
    hconv K hK (max M 0) η ν hη hν
  have hM : ∀ x : ℝ≥0∞, x ≤ ENNReal.ofReal M → ((x : EReal) ≤ ((max M 0 : ℝ) : EReal)) := by
    intro x hx
    have h1 : ((x : EReal)) ≤ ((ENNReal.ofReal M : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.2 hx
    rwa [EReal.coe_ennreal_ofReal] at h1
  have hν' : ((ν : ℝ) : EReal) = ((ENNReal.ofReal ν : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hν.le]
  filter_upwards [hd] with n hn
  refine ⟨fun p hp hDp => ?_, fun p hp hGp => ?_⟩
  · have h := (hn p hp).1 (by rw [LSCMetric.toLSCFun_apply]; exact hM _ hDp)
    rw [← coe_movingOpenSetDist_eq_d1Near, LSCMetric.toLSCFun_apply, hν',
      ← EReal.coe_ennreal_add, EReal.coe_ennreal_le_coe_ennreal_iff] at h
    exact h
  · have h := (hn p hp).2 (by rw [LSCMetric.toLSCFun_apply]; exact hM _ hGp)
    rw [← coe_movingOpenSetDist_eq_d1Near, LSCMetric.toLSCFun_apply, hν',
      ← EReal.coe_ennreal_add, EReal.coe_ennreal_le_coe_ennreal_iff] at h
    exact h

/-! ### Measurability of the event of Lemma 3.1 -/

/-- For `A` upper and `B` lower semicontinuous, `{B + c ≤ A}` is closed. -/
theorem isClosed_setOf_add_le {X : Type*} [TopologicalSpace X] {A B : X → ℝ≥0∞}
    (hA : UpperSemicontinuous A) (hB : LowerSemicontinuous B) (c : ℝ≥0∞) :
    IsClosed {x | B x + c ≤ A x} := by
  have hAc : ∀ s : ℝ≥0∞, IsClosed {x | s ≤ A x} := by
    intro s
    have h := (hA.isOpen_preimage s).isClosed_compl
    convert h using 1
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_preimage, mem_Iio, not_lt]
  have hBc : ∀ s : ℝ≥0∞, IsClosed {x | B x ≤ s} := fun s => hB.isClosed_preimage s
  have heq : {x | B x + c ≤ A x} = {x | c ≤ A x} ∩
      ⋂ t : ℚ, ({x | B x ≤ ENNReal.ofReal t} ∪ {x | ENNReal.ofReal t + c ≤ A x}) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union]
    constructor
    · intro hx
      refine ⟨le_trans le_add_self hx, fun t => ?_⟩
      by_cases ht : B x ≤ ENNReal.ofReal t
      · exact Or.inl ht
      · exact Or.inr (le_trans (add_le_add_left (not_le.1 ht).le c) hx)
    · rintro ⟨hcA, ht⟩
      by_contra hlt
      rw [not_le] at hlt
      have hAtop : A x ≠ ⊤ := ne_top_of_lt hlt
      have hctop : c ≠ ⊤ := ne_top_of_le_ne_top hAtop hcA
      have hsub : A x - c < B x := (ENNReal.sub_lt_iff_lt_right hctop hcA).2 hlt
      obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hsub
      have hq : ENNReal.ofReal (q : ℝ) = ((q : ℝ).toNNReal : ℝ≥0∞) := rfl
      rcases ht q with h1 | h1
      · rw [hq] at h1
        exact (not_le.2 hq2) h1
      · rw [hq] at h1
        have h2 : A x < ((q : ℝ).toNNReal : ℝ≥0∞) + c := by
          have := (ENNReal.sub_lt_iff_lt_right hctop hcA).1 hq1
          exact this
        exact (not_le.2 h2) h1
  rw [heq]
  exact (hAc c).inter (isClosed_iInter fun t => (hBc _).union (hAc _))

private theorem secondCountable_lscMetric : SecondCountableTopology LSCMetric :=
  LSCMetric.isInducing_toLSCFun.secondCountableTopology

attribute [local instance] secondCountable_lscMetric B2.LscTop.borelSpace_LSCMetric

/-- **Measurability of the event of Lemma 3.1**: for compact `K`, the set of pairs `(S, T)`
satisfying `NearCompare S T K M η ν` is measurable. -/
theorem measurableSet_nearCompare {K : Set (ℂ × ℂ)} (hK : IsCompact K) (M η ν : ℝ) :
    MeasurableSet {q : LSCMetric × LSCMetric | NearCompare q.1 q.2 K M η ν} := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- the closed sets upstairs
  let Z : ℕ → Set ((LSCMetric × LSCMetric) × K) := fun n =>
    {z | z.1.2 (z.2 : ℂ × ℂ) ≤ ENNReal.ofReal M} ∩
      {z | z.1.2 (z.2 : ℂ × ℂ) + (ENNReal.ofReal ν + (n : ℝ≥0∞)⁻¹) ≤
        movingOpenSetDist z.1.1 η (z.2 : ℂ × ℂ).1 (z.2 : ℂ × ℂ).2}
  have hev : LowerSemicontinuous fun z : (LSCMetric × LSCMetric) × K => z.1.2 (z.2 : ℂ × ℂ) := by
    have hc : Continuous fun z : (LSCMetric × LSCMetric) × K => (z.1.2, (z.2 : ℂ × ℂ)) :=
      (continuous_snd.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    have h := jointEval_lsc.comp hc
    exact h
  have hus : UpperSemicontinuous fun z : (LSCMetric × LSCMetric) × K =>
      movingOpenSetDist z.1.1 η (z.2 : ℂ × ℂ).1 (z.2 : ℂ × ℂ).2 := by
    have hc : Continuous fun z : (LSCMetric × LSCMetric) × K => (z.1.1, (z.2 : ℂ × ℂ)) :=
      (continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    have h := (movingOpenSetDist_joint_usc η).comp hc
    exact h
  have hZ : ∀ n, IsClosed (Z n) := fun n =>
    (hev.isClosed_preimage _).inter (isClosed_setOf_add_le hus hev _)
  have hcompl : {q : LSCMetric × LSCMetric | NearCompare q.1 q.2 K M η ν}ᶜ =
      ⋃ n : ℕ, Prod.fst '' Z n := by
    ext q
    constructor
    · intro hq
      simp only [mem_compl_iff, mem_ofPred_eq, NearCompare, not_forall, not_le] at hq
      obtain ⟨p, hp, hTp, hlt⟩ := hq
      have hpos : movingOpenSetDist q.1 η p.1 p.2 - (q.2 p + ENNReal.ofReal ν) ≠ 0 :=
        (tsub_pos_of_lt hlt).ne'
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos
      refine mem_iUnion.2 ⟨n, ((q.1, q.2), ⟨p, hp⟩), ⟨hTp, ?_⟩, rfl⟩
      show q.2 p + (ENNReal.ofReal ν + (n : ℝ≥0∞)⁻¹) ≤ movingOpenSetDist q.1 η p.1 p.2
      rw [← add_assoc]
      calc q.2 p + ENNReal.ofReal ν + (n : ℝ≥0∞)⁻¹
          ≤ q.2 p + ENNReal.ofReal ν +
              (movingOpenSetDist q.1 η p.1 p.2 - (q.2 p + ENNReal.ofReal ν)) := by
            gcongr
        _ = movingOpenSetDist q.1 η p.1 p.2 := add_tsub_cancel_of_le hlt.le
    · intro hq
      obtain ⟨n, ⟨⟨S, T⟩, ⟨p, hp⟩⟩, ⟨hT, hle⟩, hEq⟩ := mem_iUnion.1 hq
      subst hEq
      simp only [mem_compl_iff, mem_ofPred_eq, NearCompare, not_forall, not_le]
      refine ⟨p, hp, hT, ?_⟩
      have hfin : T p + ENNReal.ofReal ν ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT,
          ENNReal.ofReal_ne_top⟩
      have hinv : (n : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
      calc T p + ENNReal.ofReal ν < T p + ENNReal.ofReal ν + (n : ℝ≥0∞)⁻¹ :=
            ENNReal.lt_add_right hfin hinv
        _ = T p + (ENNReal.ofReal ν + (n : ℝ≥0∞)⁻¹) := add_assoc _ _ _
        _ ≤ _ := hle
  have hU : MeasurableSet (⋃ n : ℕ, Prod.fst '' Z n) :=
    MeasurableSet.iUnion fun n => (isClosedMap_fst_of_compactSpace _ (hZ n)).measurableSet
  rw [← compl_compl {q : LSCMetric × LSCMetric | NearCompare q.1 q.2 K M η ν}, hcompl]
  exact hU.compl

/-! ### The probabilistic half of Lemma 3.1 -/

/-- **Lemma 3.1, subsequence form** (SB1 A11): if `G ε → D` in probability for the lower
semicontinuous topology, then every sequence `ε_n → 0` has a subsequence along which, almost
surely, the two inequalities of Lemma 3.1 eventually hold. -/
theorem nearCompare_subseq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : Set.Ioi (0 : ℝ) → Ω → LSCMetric} {D : Ω → LSCMetric}
    (hconv : LSCTendstoInProbability P (fun ε ω => (G ε ω).toLSCFun.1)
      (fun ω => (D ω).toLSCFun.1))
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (M : ℝ) {η ν : ℝ} (hη : 0 < η) (hν : 0 < ν)
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      NearCompare (G (ε (φ k)) ω) (D ω) K M η ν ∧ NearCompare (D ω) (G (ε (φ k)) ω) K M η ν := by
  obtain ⟨φ, hφ, hae⟩ := hconv ε hε
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with ω hω
  exact nearCompare_eventually hω hK M hη hν

/-- **Lemma 3.1, in probability**: for a.e.-measurable random metrics with `G ε → D` in
probability, the events of Lemma 3.1 have probability tending to one as `ε → 0`. -/
theorem nearCompare_tendsto_measure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {G : Set.Ioi (0 : ℝ) → Ω → LSCMetric} {D : Ω → LSCMetric}
    (hG : ∀ ε, AEMeasurable (G ε) P) (hD : AEMeasurable D P)
    (hconv : LSCTendstoInProbability P (fun ε ω => (G ε ω).toLSCFun.1)
      (fun ω => (D ω).toLSCFun.1))
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (M : ℝ) {η ν : ℝ} (hη : 0 < η) (hν : 0 < ν) :
    Tendsto (fun ε => P {ω | ¬ (NearCompare (G ε ω) (D ω) K M η ν ∧
        NearCompare (D ω) (G ε ω) K M η ν)}) (comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hmeas : ∀ ε, NullMeasurableSet {ω | NearCompare (G ε ω) (D ω) K M η ν ∧
      NearCompare (D ω) (G ε ω) K M η ν} P := by
    intro ε
    have h1 : NullMeasurableSet {ω | NearCompare (G ε ω) (D ω) K M η ν} P :=
      ((hG ε).prodMk hD).nullMeasurable (measurableSet_nearCompare hK M η ν)
    have h2 : NullMeasurableSet {ω | NearCompare (D ω) (G ε ω) K M η ν} P :=
      (hD.prodMk (hG ε)).nullMeasurable (measurableSet_nearCompare hK M η ν)
    exact h1.inter h2
  have h := tendsto_measure_compl_of_subseq hmeas fun ε hε =>
    nearCompare_subseq hconv hK M hη hν ε hε
  simpa only [compl_ofPred] using h

end SupercriticalLFPPAS.Local
