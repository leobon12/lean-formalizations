import QuantumZipper.Proofs.Zipper.D3PlusLSCCInd
import QuantumZipper.Proofs.Zipper.D3PlusN2TmZScale

/-!
# D3⁺(ii) spread, part 1: a.e.-measurability of the hitting time `Tc`

Task LSCC-SPREAD. This file makes the pushforwards `P.map (fun ω => ZoomRadial.Tc …)` in
`LSCCSpreadHitStmt` (`D3PlusLSCCSpread.lean`) genuine measures (at this pin `Measure.map` of a
non-a.e.-measurable function is `0`).

* `measurable_Tc_of_cont`: for a path family with continuous sections and measurable evaluations,
  the first hitting time `Tc` of `0` by `Xc` is measurable. Own elementary argument: on `[0,m]`
  a continuous function is positive iff it dominates some rational `1/(k+1)` at the rational
  points (`pos_Icc_iff_rat`), and it comes within `1/(k+1)` of `0` iff the same holds at a
  rational point (`exists_le_zero_iff_rat`); hence `{Tc ≤ m}` is the union of a countable
  intersection and a countable union of such events (`Real.sInf_empty` handles the empty
  hitting set, `IsClosed.csInf_mem` the nonempty one). This makes the pushforwards
  `P.map (Tc …)` in the spread statements non-junk.
* `aemeasurable_Tc_zRadB`: specialisation to the radial Brownian motion `zRadB X r` of a free
  field, through the good version of `WedgeRes.exists_good_version`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The level shift -/

/-! ## Own elementary lemmas on continuous functions on `[0, m]` -/

/-- Rationals are dense in `[0, m]` (`m ≥ 0`), with an explicit distance bound. -/
theorem exists_rat_mem_Icc_close {m t ε : ℝ} (hm : 0 ≤ m) (ht : t ∈ Icc 0 m) (hε : 0 < ε) :
    ∃ q : ℚ, (q : ℝ) ∈ Icc 0 m ∧ |(q : ℝ) - t| < ε := by
  rcases eq_or_lt_of_le hm with h0 | hm0
  · have ht0 : t = 0 := le_antisymm (h0 ▸ ht.2) ht.1
    exact ⟨0, by simp [← h0], by rw [ht0]; simpa using hε⟩
  · have hlt : max 0 (t - ε) < min m (t + ε) :=
      max_lt (lt_min hm0 (by linarith [ht.1, hε]))
        (lt_min (by linarith [ht.2, hε]) (by linarith [hε]))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact ⟨q, ⟨(le_max_left 0 (t - ε)).trans hq1.le,
      hq2.le.trans (min_le_left m (t + ε))⟩, by
        rw [abs_lt]
        exact ⟨by linarith [hq1, le_max_right 0 (t - ε)],
          by linarith [hq2, min_le_right m (t + ε)]⟩⟩

/-- **Own elementary lemma.** A continuous function on `Icc 0 m` (`m ≥ 0`) is everywhere positive
iff it dominates some rational `1/(k+1)` at every rational point of `Icc 0 m` (compactness gives a
positive minimum; conversely a uniform lower bound at the rationals extends to all points by
continuity and density). -/
theorem pos_Icc_iff_rat {f : ℝ → ℝ} (hf : Continuous f) {m : ℝ} (hm : 0 ≤ m) :
    (∀ t ∈ Icc 0 m, 0 < f t) ↔
      ∃ k : ℕ, ∀ q : ℚ, (q : ℝ) ∈ Icc 0 m → 1 / ((k : ℝ) + 1) < f q := by
  constructor
  · intro h
    obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, left_mem_Icc.2 hm⟩ hf.continuousOn
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (h t0 ht0)
    exact ⟨k, fun q hq => hk.trans_le (hmin hq)⟩
  · rintro ⟨k, hk⟩ t ht
    choose q hqI hqd using fun n : ℕ =>
      exists_rat_mem_Icc_close hm ht (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    have htend : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝 t) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => (hqd n).le) ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hfq : Tendsto (fun n : ℕ => f (q n : ℝ)) atTop (𝓝 (f t)) :=
      hf.continuousAt.tendsto.comp htend
    have hlow : 1 / ((k : ℝ) + 1) ≤ f t := ge_of_tendsto' hfq fun n => (hk (q n) (hqI n)).le
    linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]

/-- **Own elementary lemma.** A continuous function on `Icc 0 m` (`m ≥ 0`) takes a value `≤ 0`
iff it comes within `1/(k+1)` of `0` at some rational point of `Icc 0 m`. -/
theorem exists_le_zero_iff_rat {f : ℝ → ℝ} (hf : Continuous f) {m : ℝ} (hm : 0 ≤ m) :
    (∃ t ∈ Icc 0 m, f t ≤ 0) ↔
      ∀ k : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc 0 m ∧ f q ≤ 1 / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨t, ht, hft⟩ k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hf.continuousAt _ hε
    obtain ⟨q, hqI, hqd⟩ := exists_rat_mem_Icc_close hm ht (lt_min hδ one_pos)
    refine ⟨q, hqI, ?_⟩
    have hdist := hδ' (x := (q : ℝ)) (by
      rw [Real.dist_eq]
      exact hqd.trans_le (min_le_left δ 1))
    rw [Real.dist_eq, abs_lt] at hdist
    linarith [hdist.1]
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := (pos_Icc_iff_rat hf hm).1 hcon
    obtain ⟨q, hqI, hqle⟩ := h k
    exact absurd (hk q hqI) (not_lt.2 hqle)

/-! ## Measurability of the hitting time `Tc` -/

/-- `Xc` is continuous in the time variable. -/
theorem continuous_Xc {Ω : Type*} {b : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t : ℝ≥0 => b t ω)
    (ω : Ω) (α Q c : ℝ) : Continuous fun t : ℝ => ZoomRadial.Xc α Q c b ω t := by
  have h1 : Continuous fun t : ℝ => b t.toNNReal ω := (hc ω).comp continuous_real_toNNReal
  simp only [ZoomRadial.Xc]
  fun_prop

/-- `Xc` is measurable in `ω` at a fixed time. -/
theorem measurable_Xc {Ω : Type*} [MeasurableSpace Ω] {b : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t : ℝ, Measurable fun ω => b t.toNNReal ω) (α Q c : ℝ) (t : ℝ) :
    Measurable fun ω => ZoomRadial.Xc α Q c b ω t := by
  have h1 : Measurable fun ω => b t.toNNReal ω := hm t
  simp only [ZoomRadial.Xc]
  fun_prop

/-- `Tc` depends on the path only through its values. -/
theorem Tc_congr {Ω : Type*} {α Q c : ℝ} {b b' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : ∀ t : ℝ≥0, b t ω = b' t ω) :
    ZoomRadial.Tc α Q c b ω = ZoomRadial.Tc α Q c b' ω := by
  have hpath : ∀ t : ℝ, ZoomRadial.Xc α Q c b ω t = ZoomRadial.Xc α Q c b' ω t := by
    intro t
    simp only [ZoomRadial.Xc, h t.toNNReal]
  simp only [ZoomRadial.Tc, hpath]

/-- **Own elementary argument.** For a path family with continuous sections and measurable
evaluations, the first hitting time `Tc α Q c b` of `0` by `Xc` is measurable. -/
theorem measurable_Tc_of_cont {Ω : Type*} [MeasurableSpace Ω] {b : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => b t ω)
    (hm : ∀ t : ℝ, Measurable fun ω => b t.toNNReal ω) (α Q c : ℝ) :
    Measurable fun ω => ZoomRadial.Tc α Q c b ω := by
  refine measurable_of_Iic fun m => ?_
  change MeasurableSet {ω | ZoomRadial.Tc α Q c b ω ≤ m}
  rcases lt_or_ge m 0 with hm0 | hm0
  · have hE : {ω | ZoomRadial.Tc α Q c b ω ≤ m} = ∅ := by
      ext ω; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hm0 (ZoomRadial.Tc_nonneg α Q c b ω)
    rw [hE]; exact MeasurableSet.empty
  · let U : Set Ω := {ω | ∀ k : ℕ, ∃ q : ℚ,
        (q : ℝ) ∈ Icc 0 m ∧ ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)}
    let W : Set Ω := ⋂ n : ℕ, {ω | ∃ k : ℕ, ∀ q : ℚ,
        (q : ℝ) ∈ Icc 0 (n : ℝ) → 1 / ((k : ℝ) + 1) < ZoomRadial.Xc α Q c b ω (q : ℝ)}
    have hE : {ω | ZoomRadial.Tc α Q c b ω ≤ m} = U ∪ W := by
      ext ω
      simp only [U, W, mem_setOf_eq, mem_union, mem_iInter]
      constructor
      · intro hTm
        by_cases hne : ({t : ℝ | 0 ≤ t ∧ ZoomRadial.Xc α Q c b ω t ≤ 0} : Set ℝ).Nonempty
        · left
          have hcl : IsClosed {t : ℝ | 0 ≤ t ∧ ZoomRadial.Xc α Q c b ω t ≤ 0} :=
            isClosed_Ici.inter (isClosed_le (continuous_Xc hc ω α Q c) continuous_const)
          have hmem : ZoomRadial.Tc α Q c b ω ∈ {t : ℝ | 0 ≤ t ∧
              ZoomRadial.Xc α Q c b ω t ≤ 0} :=
            hcl.csInf_mem hne ⟨0, fun t ht => ht.1⟩
          exact (exists_le_zero_iff_rat (continuous_Xc hc ω α Q c) hm0).1
            ⟨ZoomRadial.Tc α Q c b ω, ⟨hmem.1, hTm⟩, hmem.2⟩
        · right
          intro n
          refine (pos_Icc_iff_rat (continuous_Xc hc ω α Q c) (Nat.cast_nonneg n)).1
            fun t ht => ?_
          by_contra hlt
          exact hne ⟨t, ht.1, le_of_not_gt hlt⟩
      · rintro (hU | hW)
        · obtain ⟨t, ht, hle⟩ :=
            (exists_le_zero_iff_rat (continuous_Xc hc ω α Q c) hm0).2 hU
          show ZoomRadial.Tc α Q c b ω ≤ m
          rw [ZoomRadial.Tc]
          have hbdd : BddBelow {t : ℝ | 0 ≤ t ∧ ZoomRadial.Xc α Q c b ω t ≤ 0} :=
            ⟨0, fun s hs => hs.1⟩
          exact (csInf_le hbdd (show t ∈ {t : ℝ | 0 ≤ t ∧
            ZoomRadial.Xc α Q c b ω t ≤ 0} from ⟨ht.1, hle⟩)).trans ht.2
        · have hS : {t : ℝ | 0 ≤ t ∧ ZoomRadial.Xc α Q c b ω t ≤ 0} = ∅ := by
            refine eq_empty_iff_forall_notMem.2 fun s hs => ?_
            obtain ⟨k, hk⟩ := hW ⌈s⌉₊
            have hk' := (pos_Icc_iff_rat (continuous_Xc hc ω α Q c)
              (Nat.cast_nonneg (⌈s⌉₊ : ℕ))).2 ⟨k, hk⟩
            exact absurd (hk' s ⟨hs.1, Nat.le_ceil s⟩) (not_lt.2 hs.2)
          show ZoomRadial.Tc α Q c b ω ≤ m
          rw [ZoomRadial.Tc, hS, Real.sInf_empty]
          exact hm0
    have hUm : MeasurableSet U := by
      dsimp only [U]
      rw [show {ω : Ω | ∀ k : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc 0 m ∧
            ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)} =
          ⋂ k : ℕ, {ω : Ω | ∃ q : ℚ, (q : ℝ) ∈ Icc 0 m ∧
            ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)} from by
        ext ω; simp only [mem_ofPred_eq, mem_iInter]]
      refine MeasurableSet.iInter fun k => ?_
      have hset : {ω : Ω | ∃ q : ℚ, (q : ℝ) ∈ Icc 0 m ∧
            ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)} =
          ⋃ q : ℚ, {ω : Ω | (q : ℝ) ∈ Icc 0 m ∧
            ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion]
      rw [hset]
      refine MeasurableSet.iUnion fun q => ?_
      by_cases h : (q : ℝ) ∈ Icc 0 m
      · simpa [h] using
          (measurableSet_le (measurable_Xc hm α Q c (q : ℝ)) measurable_const :
            MeasurableSet {ω : Ω |
              ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)})
      · have hz : {ω : Ω | (q : ℝ) ∈ Icc 0 m ∧
            ZoomRadial.Xc α Q c b ω (q : ℝ) ≤ 1 / ((k : ℝ) + 1)} = ∅ := by
          ext ω; simp [h]
        rw [hz]; exact MeasurableSet.empty
    have hWm : MeasurableSet W := by
      dsimp only [W]
      refine MeasurableSet.iInter fun n => ?_
      have hset : {ω : Ω | ∃ k : ℕ, ∀ q : ℚ, (q : ℝ) ∈ Icc 0 (n : ℝ) →
            1 / ((k : ℝ) + 1) < ZoomRadial.Xc α Q c b ω (q : ℝ)} =
          ⋃ k : ℕ, ⋂ q : ℚ, {ω : Ω | (q : ℝ) ∈ Icc 0 (n : ℝ) →
            1 / ((k : ℝ) + 1) < ZoomRadial.Xc α Q c b ω (q : ℝ)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
      rw [hset]
      refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun q => ?_
      by_cases h : (q : ℝ) ∈ Icc 0 (n : ℝ)
      · simpa [h] using
          (measurableSet_lt measurable_const (measurable_Xc hm α Q c (q : ℝ)) :
            MeasurableSet {ω : Ω |
              1 / ((k : ℝ) + 1) < ZoomRadial.Xc α Q c b ω (q : ℝ)})
      · have hz : {ω : Ω | (q : ℝ) ∈ Icc 0 (n : ℝ) →
            1 / ((k : ℝ) + 1) < ZoomRadial.Xc α Q c b ω (q : ℝ)} = Set.univ := by
          ext ω; simp [h]
        rw [hz]; exact MeasurableSet.univ
    rw [hE]; exact hUm.union hWm

/-- `Tc` along the radial Brownian motion `zRadB X r` of a free field is a.e.-measurable. -/
theorem aemeasurable_Tc_zRadB {γ α r L : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (hr : 0 < r) :
    AEMeasurable (fun ω => ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω) P := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := WedgeRes.exists_good_version (isBrownianReal_zRadB hX hr)
  have hmeas : Measurable fun ω =>
      ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) B' ω :=
    measurable_Tc_of_cont hB'c (fun t => hB'm.of_uncurry_left) α (Qc γ) (n2Lev γ α L r)
  refine ⟨_, hmeas, ?_⟩
  filter_upwards [hB'eq] with ω hω
  exact (Tc_congr fun t => hω t).symm

end D3Plus
end QuantumZipper
