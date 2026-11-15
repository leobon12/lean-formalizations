/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfPk

/-!
# Visiting a closed set before a lifetime, as a countable condition

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). `visitBefore Γ T A`: some rational horizon `T' < T` such
that for every `n` a rational time `q ≤ T'` has `infDist (Γ q) A < 1/(n+1)`. For a closed nonempty `A` and a path
continuous before `T`, this is a visit of `A` at some time `< T` (`visitBefore_iff`); it is measurable when each `Γ q`
and `T` are (`measurableSet_visitBefore`, with a measurable moving point `measurableSet_visitBefore_pt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Wf

/-- **Visiting `A` before `T`, at rational times.** -/
def visitBefore (Γ : ℝ≥0 → ℂ) (T : ℝ≥0∞) (A : Set ℂ) : Prop :=
  ∃ T' : ℚ≥0, ((T' : ℝ≥0) : ℝ≥0∞) < T ∧ ∀ n : ℕ, ∃ q : ℚ≥0, q ≤ T' ∧ infDist (Γ q) A < 1 / ((n : ℝ) + 1)

/-- **For a continuous path, the rational condition is a visit.** -/
theorem visitBefore_iff {Γ : ℝ≥0 → ℂ} {T : ℝ≥0∞} (hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < T}) {A : Set ℂ}
    (hA : IsClosed A) (hAne : A.Nonempty) :
    visitBefore Γ T A ↔ ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ Γ t ∈ A := by
  constructor
  · rintro ⟨T', hT', hq⟩
    choose q hqT hqd using hq
    -- a convergent subsequence of the rational times in `[0, T']`
    have hK : IsCompact (Icc (0 : ℝ≥0) (T' : ℝ≥0)) := isCompact_Icc
    obtain ⟨s, hs, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n => ((q n : ℚ≥0) : ℝ≥0))
      fun n => ⟨zero_le, by exact_mod_cast hqT n⟩
    have hsT : (s : ℝ≥0∞) < T := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) hT'
    refine ⟨s, hsT, ?_⟩
    have hcont : ContinuousAt Γ s := hΓ.continuousAt
      (IsOpen.mem_nhds (isOpen_lt (ENNReal.continuous_coe) continuous_const) hsT)
    have hΓlim : Tendsto (fun n => Γ ((q (φ n) : ℚ≥0) : ℝ≥0)) atTop (𝓝 (Γ s)) := hcont.tendsto.comp hlim
    have hd : Tendsto (fun n => infDist (Γ ((q (φ n) : ℚ≥0) : ℝ≥0)) A) atTop (𝓝 (infDist (Γ s) A)) :=
      ((continuous_infDist_pt A).tendsto _).comp hΓlim
    have hd0 : Tendsto (fun n => infDist (Γ ((q (φ n) : ℚ≥0) : ℝ≥0)) A) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => infDist_nonneg) (fun n => (hqd (φ n)).le.trans ?_)
        ((tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop)
      simp
    have h0 : infDist (Γ s) A = 0 := tendsto_nhds_unique hd hd0
    exact (hA.mem_iff_infDist_zero hAne).2 h0
  · rintro ⟨t, htT, htA⟩
    -- a rational horizon beyond `t`
    obtain ⟨r, htr, hrT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htT
    have htr' : t < r := ENNReal.coe_lt_coe.1 htr
    obtain ⟨T', htT', hT'r⟩ := exists_rat_btwn (show (t : ℝ) < r from htr')
    have hT'0 : (0 : ℝ) ≤ T' := le_trans t.coe_nonneg htT'.le
    set T'' : ℚ≥0 := ⟨T', by exact_mod_cast hT'0⟩ with hT''
    have hT''r : ((T'' : ℝ≥0) : ℝ≥0∞) < T := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hrT
      show ((T'' : ℝ≥0) : ℝ) ≤ r
      exact hT'r.le
    refine ⟨T'', hT''r, fun n => ?_⟩
    have hcont : ContinuousAt Γ t := hΓ.continuousAt
      (IsOpen.mem_nhds (isOpen_lt (ENNReal.continuous_coe) continuous_const) htT)
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont _ hε
    -- a rational time within `δ` of `t`, in `[t, T'']`
    have htT'' : (t : ℝ) < ((T'' : ℝ≥0) : ℝ) := htT'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < min ((t : ℝ) + δ) ((T'' : ℝ≥0) : ℝ) from
      lt_min (by linarith) htT'')
    have hq0 : (0 : ℝ) ≤ q := le_trans t.coe_nonneg hq1.le
    set q' : ℚ≥0 := ⟨q, by exact_mod_cast hq0⟩ with hq'
    refine ⟨q', ?_, ?_⟩
    · have h1 : (q : ℝ) ≤ ((T'' : ℝ≥0) : ℝ) := hq2.le.trans (min_le_right _ _)
      have h2 : (q : ℝ) ≤ (T' : ℝ) := h1
      have h3 : q ≤ T' := by exact_mod_cast h2
      exact h3
    · have hdist : dist ((q' : ℚ≥0) : ℝ≥0) t < δ := by
        rw [NNReal.dist_eq]
        have h1 : (((q' : ℚ≥0) : ℝ≥0) : ℝ) = q := rfl
        rw [h1, abs_of_pos (by linarith)]
        linarith [min_le_left ((t : ℝ) + δ) ((T'' : ℝ≥0) : ℝ)]
      have h2 := hδc hdist
      calc infDist (Γ ((q' : ℚ≥0) : ℝ≥0)) A ≤ dist (Γ ((q' : ℚ≥0) : ℝ≥0)) (Γ t) + infDist (Γ t) A :=
            infDist_le_infDist_add_dist.trans_eq (add_comm _ _) |>.trans (by rw [dist_comm])
        _ = dist (Γ ((q' : ℚ≥0) : ℝ≥0)) (Γ t) := by rw [infDist_zero_of_mem htA, add_zero]
        _ < 1 / ((n : ℝ) + 1) := h2

/-- **The rational condition is measurable** for a fixed set. -/
theorem measurableSet_visitBefore {Ω : Type*} [MeasurableSpace Ω] {Γ : Ω → ℝ≥0 → ℂ}
    (hΓ : ∀ q : ℝ≥0, Measurable fun ω => Γ ω q) {T : Ω → ℝ≥0∞} (hT : Measurable T) (A : Set ℂ) :
    MeasurableSet {ω | visitBefore (Γ ω) (T ω) A} := by
  unfold visitBefore
  simp only [ofPred_exists, ofPred_and, ofPred_forall]
  refine MeasurableSet.iUnion fun T' : ℚ≥0 => (measurableSet_lt measurable_const hT).inter
    (MeasurableSet.iInter fun n : ℕ => MeasurableSet.iUnion fun q : ℚ≥0 =>
      (MeasurableSet.const _).inter ?_)
  exact measurableSet_lt ((continuous_infDist_pt A).measurable.comp (hΓ _)) measurable_const

/-- **The rational condition is measurable** for a measurable moving point. -/
theorem measurableSet_visitBefore_pt {Ω : Type*} [MeasurableSpace Ω] {Γ : Ω → ℝ≥0 → ℂ}
    (hΓ : ∀ q : ℝ≥0, Measurable fun ω => Γ ω q) {T : Ω → ℝ≥0∞} (hT : Measurable T) {x : Ω → ℂ}
    (hx : Measurable x) : MeasurableSet {ω | visitBefore (Γ ω) (T ω) {x ω}} := by
  unfold visitBefore
  simp only [ofPred_exists, ofPred_and, ofPred_forall, infDist_singleton]
  refine MeasurableSet.iUnion fun T' : ℚ≥0 => (measurableSet_lt measurable_const hT).inter
    (MeasurableSet.iInter fun n : ℕ => MeasurableSet.iUnion fun q : ℚ≥0 =>
      (MeasurableSet.const _).inter ?_)
  exact measurableSet_lt ((hΓ _).dist hx) measurable_const

end InteractingSLE.Theorem14.SB.Wf
