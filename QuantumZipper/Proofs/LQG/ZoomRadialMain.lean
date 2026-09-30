import QuantumZipper.Proofs.LQG.ZoomRadialBasic

/-!
# The wedge path is high only with small probability (TASKS.md R6, `tendsto_prob_wedge_high`)

For an `α`-wedge radial process `A` (`IsWedgeProcess α Q A P`) the probability that the backward
half of the wedge path is `≥ c` somewhere on the window `[−S, 0]` tends to `0` as `c → ∞`:

`Tendsto (fun c => P {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω}) atTop (𝓝 0)`.

Mathematically this is elementary: on `t < 0` the wedge path is
`A (−u) = Υ (u + lastZero Υ)` with `Υ s = √2 b' s + (Q − α) s`, a continuous function of `u`; a
continuous function is bounded on the compact window `[0, S]`, so the events decrease (in `c`) to
the empty set. The content of the formalization is the *measurability* of the event: the real
quantifier `∃ u ∈ [0, S]` is reduced to rationals, which is legitimate on the set where the path
is continuous (here: for every `ω`, since we use the good version of `b'`), and the resulting
sequence of measurable sets is decreasing with empty intersection, so its probability tends to
`0` (`tendsto_measure_iInter_atTop`).

Source: Sheffield (arXiv:1012.4797) §1.6 and the proof of Prop. 1.6 (the wedge path is bounded on
compact windows); own elementary proof for the measure-theoretic passage.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A continuous path vanishing at `0` vanishes at its last zero
(own elementary proof; identical statement to `WedgeGood.apply_lastZero`). -/
theorem apply_lastZero_self {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) :
    f (lastZero f) = 0 := by
  unfold lastZero
  set Z : Set ℝ := {s | 0 ≤ s ∧ f s = 0} with hZ
  by_cases hb : BddAbove Z
  · have hZc : IsClosed Z :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hf continuous_const)
    exact (hZc.csSup_mem ⟨0, le_rfl, h0⟩ hb).2
  · rw [Real.sSup_of_not_bddAbove hb]; exact h0

/-- **Rationalization.** A continuous function with `f u ≥ c` at a point `u ∈ [0, S]` (`S ≥ 0`)
satisfies `f q ≥ c − 1` at some rational point `q ∈ [0, S]`. -/
theorem exists_rat_Icc_le_sub_one {f : ℝ → ℝ} (hf : Continuous f) {S c u : ℝ} (hS : 0 ≤ S)
    (hu : u ∈ Set.Icc 0 S) (hcu : c ≤ f u) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Icc 0 S ∧ c - 1 ≤ f (q : ℝ) := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · refine ⟨0, by simpa only [Rat.cast_zero, ← h0] using hu, ?_⟩
    have : c ≤ f 0 := by rw [← h0] at hcu; exact hcu
    simp only [Rat.cast_zero]; linarith
  · obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1
      (hf.continuousAt.eventually (Metric.ball_mem_nhds (f u) one_pos))
    set r : ℝ := min δ u / 2 with hr
    have hrpos : 0 < r := by
      rw [hr]
      have h1 : 0 < min δ u := lt_min hδpos h0
      linarith
    have hrleδ : r ≤ δ := by
      rw [hr]; linarith [min_le_left δ u]
    have hlt : max 0 (u - r) < min S (u + r) := by
      refine max_lt ?_ ?_
      · exact lt_min (h0.trans_le hu.2) (by linarith)
      · have hrle : r ≤ u / 2 := by
          rw [hr]; linarith [min_le_right δ u]
        exact lt_min (by linarith [hu.2, hrpos]) (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hqu : |(q : ℝ) - u| < δ := by
      have h1 : u - r < (q : ℝ) := lt_of_le_of_lt (le_max_right 0 (u - r)) hq1
      have h2 : (q : ℝ) < u + r := lt_of_lt_of_le hq2 (min_le_right S (u + r))
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    refine ⟨q, ⟨le_of_lt (lt_of_le_of_lt (le_max_left 0 (u - r)) hq1),
      le_of_lt (lt_of_lt_of_le hq2 (min_le_left S (u + r)))⟩, ?_⟩
    have hball : dist (f (q : ℝ)) (f u) < 1 :=
      hδ (by rw [Metric.mem_ball, Real.dist_eq]; exact hqu)
    rw [Real.dist_eq, abs_lt] at hball
    linarith [hball.1]

/-- **R6 step (d).** The wedge path is `≥ c` on the window `[−S, 0]` with probability tending to
`0` as `c → ∞`. -/
theorem tendsto_prob_wedge_high {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P)
    (hαQ : α < Q) (S : ℝ) :
    Tendsto (fun c => P {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω}) atTop (𝓝 0) := by
  by_cases hS : 0 ≤ S
  swap
  · have hI : Set.Icc (0 : ℝ) S = ∅ := Set.Icc_eq_empty hS
    have hzero : ∀ c, P {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} = 0 := by
      intro c
      have h : {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} = ∅ := by
        ext ω
        simp only [hI, mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
          mem_empty_iff_false]
      rw [h, measure_empty]
    simp only [hzero]
    exact tendsto_const_nhds
  obtain ⟨B, B', hB, hB', hInd, hAB⟩ := hA
  obtain ⟨Bt', hBt'm, hBt'c, hBt'B⟩ := WedgeRes.exists_good_version hB'
  -- the backward path `Υ` and the Williams path `Yh u = Υ (u + lastZero Υ)`
  set Yt : Ω → ℝ → ℝ := fun ω s => √2 * Bt' s.toNNReal ω + (Q - α) * s with hYt
  set Yh : Ω → ℝ → ℝ := fun ω u => Yt ω (u + lastZero (Yt ω)) with hYh
  have hYtc : ∀ ω, Continuous (Yt ω) := fun ω =>
    (continuous_const.mul ((hBt'c ω).comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)
  have hYtm : ∀ s, Measurable fun ω => Yt ω s := fun s =>
    (((hBt'm.comp (measurable_const.prodMk measurable_id)) :
      Measurable fun ω => Bt' s.toNNReal ω)).const_mul (√2) |>.add_const ((Q - α) * s)
  have hYtJ : Measurable fun p : Ω × ℝ => Yt p.1 p.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun r ω => Yt ω r) hYtc hYtm).comp
      measurable_swap
  have hLm : Measurable fun ω => lastZero (Yt ω) := WedgeMeas.measurable_lastZero hYtc hYtm
  have hYhc : ∀ ω, Continuous (Yh ω) := fun ω => by
    rw [hYh]; exact (hYtc ω).comp (continuous_id.add continuous_const)
  have hYhm : ∀ u : ℝ, Measurable fun ω => Yh ω u := fun u => by
    rw [hYh]
    exact hYtJ.comp (measurable_id.prodMk (measurable_const.add hLm))
  -- the null set where the good version of `b'` fails to be a genuine version, or `b` is nonzero
  set N : Set Ω := {ω | ¬ (∀ s, Bt' s ω = B' s ω)} ∪
    ({ω | Bt' 0 ω ≠ 0} ∪ {ω | B 0 ω ≠ 0}) with hN
  have hN1 : P {ω | ¬ (∀ s, Bt' s ω = B' s ω)} = 0 := ae_iff.1 hBt'B
  have hN2 : P {ω | Bt' 0 ω ≠ 0} = 0 := by
    refine ae_iff.1 ?_
    filter_upwards [hBt'B, hB'.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h1 h2
    exact (h1 0).trans h2
  have hN3 : P {ω | B 0 ω ≠ 0} = 0 := ae_iff.1 hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hNnull : P N = 0 := by
    rw [hN]
    refine le_antisymm ?_ zero_le
    calc P ({ω | ¬ (∀ s, Bt' s ω = B' s ω)} ∪ ({ω | Bt' 0 ω ≠ 0} ∪ {ω | B 0 ω ≠ 0}))
        ≤ P {ω | ¬ (∀ s, Bt' s ω = B' s ω)} +
          P ({ω | Bt' 0 ω ≠ 0} ∪ {ω | B 0 ω ≠ 0}) := measure_union_le _ _
      _ = 0 := by
        rw [hN1, zero_add]
        exact le_antisymm ((measure_union_le _ _).trans (by rw [hN2, hN3, add_zero])) zero_le
  -- the rational-indexed events
  set R : Set ℚ := {q | (q : ℝ) ∈ Set.Icc 0 S} with hR
  set F : ℝ → Set Ω := fun c => ⋃ q ∈ R, {ω | c ≤ Yh ω (q : ℝ)} with hF
  have hFm : ∀ c, MeasurableSet (F c) := fun c => by
    rw [hF]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      measurableSet_le measurable_const (hYhm (q : ℝ))
  have hFanti : Antitone F := by
    intro c c' hcc' ω hω
    rw [hF] at hω ⊢
    simp only [mem_iUnion, Set.mem_setOf_eq] at hω ⊢
    obtain ⟨q, hq, hcq⟩ := hω
    exact ⟨q, hq, le_trans hcc' hcq⟩
  have hInter : (⋂ n : ℕ, F (n : ℝ)) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro ω hω
    obtain ⟨M, hM⟩ := (isCompact_Icc.image (hYhc ω)).bddAbove
    obtain ⟨n, hn⟩ : ∃ n : ℕ, M < n := exists_nat_gt M
    have hn' : ω ∈ F (n : ℝ) := mem_iInter.mp hω n
    rw [hF, hR] at hn'
    simp only [mem_iUnion, Set.mem_setOf_eq] at hn'
    obtain ⟨q, hq, hnq⟩ := hn'
    have hb := hM (show Yh ω (q : ℝ) ∈ Yh ω '' Set.Icc 0 S from ⟨(q : ℝ), hq, rfl⟩)
    exact absurd (hb.trans_lt hn) (not_lt.2 hnq)
  have hFtend : Tendsto (fun n : ℕ => P (F (n : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (s := fun n : ℕ => F (n : ℝ))
      (fun n => (hFm _).nullMeasurableSet)
      (fun a b hab => hFanti (Nat.cast_le.2 hab)) ⟨0, (measure_lt_top _ _).ne⟩
    rwa [hInter, measure_empty] at h
  -- the event is contained in the rational one, up to the null set
  have hsub : ∀ c, {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} ⊆ F (c - 1) ∪ N := by
    intro c ω hω
    by_cases hNω : ω ∈ N
    · exact Or.inr hNω
    refine Or.inl ?_
    simp only [hN, mem_union, not_or, not_not, Set.mem_setOf_eq] at hNω
    obtain ⟨hE1, hb0, hB0⟩ := hNω
    obtain ⟨u, hu, hcu⟩ := hω
    have hYh0 : Yh ω 0 = 0 := by
      show Yt ω (0 + lastZero (Yt ω)) = 0
      rw [zero_add]
      exact apply_lastZero_self (hYtc ω) (by rw [hYt]; simp [hb0])
    by_cases hu0 : u = 0
    · -- the witness is `0`: then `A 0 = √2 * B 0 = 0`, so `c ≤ 0` and `Yh 0 = 0 ≥ c - 1`
      subst hu0
      rw [neg_zero] at hcu
      have hA0 : A 0 ω = √2 * B 0 ω := by
        rw [hAB ω 0]
        simp only [wedgePath]
        rw [if_pos le_rfl, Real.toNNReal_zero, mul_zero, add_zero]
      have hc0 : c ≤ 0 := by
        rw [hA0, hB0, mul_zero] at hcu
        exact hcu
      rw [hF]
      refine mem_iUnion.2 ⟨0, mem_iUnion.2 ⟨?_, ?_⟩⟩
      · rw [hR]; simp only [Set.mem_setOf_eq, Rat.cast_zero]; exact ⟨le_rfl, hS⟩
      · simp only [Set.mem_setOf_eq, Rat.cast_zero]
        rw [hYh0]; linarith
    · -- the witness is `> 0`: the wedge path is the Williams path there
      have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hYh_eq : A (-u) ω = Yh ω u := by
        have hfun : ∀ s : ℝ, √2 * B' s.toNNReal ω - (α - Q) * s = Yt ω s := fun s => by
          rw [hYt, ← hE1 s.toNNReal]; ring
        have hL : lastZero (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Q) * s) =
            lastZero (Yt ω) := by rw [funext hfun]
        have hneg : ¬ (0 ≤ -u) := by linarith
        rw [hAB ω (-u)]
        simp only [wedgePath, if_neg hneg, neg_neg, hL, hfun, hYh]
      obtain ⟨q, hq, hcq⟩ :=
        exists_rat_Icc_le_sub_one (f := Yh ω) (hYhc ω) hS hu (hcu.trans (le_of_eq hYh_eq))
      rw [hF]
      exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨by rw [hR]; exact hq, hcq⟩⟩
  have hbound : ∀ c, P {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} ≤ P (F (c - 1)) := by
    intro c
    calc P {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω}
        ≤ P (F (c - 1) ∪ N) := measure_mono (hsub c)
      _ ≤ P (F (c - 1)) + P N := measure_union_le _ _
      _ = P (F (c - 1)) := by rw [hNnull, add_zero]
  have hlow : Tendsto (fun c : ℝ => P (F (⌊c - 1⌋₊ : ℝ))) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun c : ℝ => ⌊c - 1⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp
        (by simpa only [id_eq, sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1) tendsto_id)
    exact hFtend.comp hcomp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlow
    (Eventually.of_forall fun c => bot_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  refine (hbound c).trans (measure_mono (hFanti ?_))
  exact Nat.floor_le (by linarith : (0 : ℝ) ≤ c - 1)

end ZoomRadial
end QuantumZipper
