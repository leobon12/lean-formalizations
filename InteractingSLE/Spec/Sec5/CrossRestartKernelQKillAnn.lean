/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKillGlueAE
import InteractingSLE.Spec.Sec5.CrossCondWordAnn

/-!
# Lemma 4.7 in the chart `Q`: announcing the killing time of the counterflow's image word

Packet PROVE-CFRESTART4, item D1′ (the Lemma 4.7 mirror of GLUECOND5's `CrossCondWordAnn`). The killing time `qT` of
the image word (the capacity of the first contact of the counterflow with `G = R(K_q)`) is announced by the capacity
times `σₙ` of the last rational time `r ≤ n` up to which every ball of radius `1/(n+1)` around a rational position of
the counterflow misses `G` (on good samples; `0` elsewhere). Only the continuity of the counterflow, its start at `0`
and the closedness of `G` are used (the counterflow is not simple).

* `mem_preContact_of_ball_bound'` (deterministic, for a continuous curve from `0`);
* **`qAnn_lt_qT`**, **`monotone_qAnn`**, **`exists_le_qAnn`**, **`measurable_qAnn`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q
open CrossCond.Word49 (mem_preContact_iff_ball measurableSet_disjoint_ball)

namespace Kill47

/-- **A uniform ball bound before `τ` puts `τ` before the first contact** (a continuous curve from `0`, a closed
`G ⊆ ℍ`). -/
theorem mem_preContact_of_ball_bound' {α : ℝ → ℂ} (hαc : ContinuousOn α (Ici 0)) (hα0 : α 0 = 0) {G : Set ℂ}
    (hGH : G ⊆ H) {τ : ℝ} (hτ : 0 ≤ τ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) < τ → Disjoint (ball (α u) c) G) : τ ∈ preContact α G := by
  refine ⟨hτ, fun u hu hαu => ?_⟩
  rcases hu.1.eq_or_lt with hu0 | hu0
  · rw [← hu0, hα0] at hαu
    exact GlueCond.zero_notMem_H (hGH hαu)
  have hcα : ContinuousWithinAt α (Icc 0 u) u := (hαc u hu.1).mono Icc_subset_Ici_self
  obtain ⟨δ, hδ, hαδ⟩ := Metric.continuousWithinAt_iff.1 hcα c hc
  obtain ⟨u', hu'1, hu'2⟩ := exists_rat_btwn (show max 0 (u - δ) < u from max_lt hu0 (by linarith))
  have hu'0 : (0 : ℝ) ≤ u' := (le_max_left _ _).trans hu'1.le
  have e1 := hαδ (x := (u' : ℝ)) ⟨hu'0, hu'2.le⟩ (by
    rw [Real.dist_eq, abs_lt]
    have := le_max_right 0 (u - δ)
    constructor <;> linarith)
  exact Set.disjoint_left.1 (hb u' hu'0 (hu'2.trans_le hu.2)) (mem_ball.2 (by rw [dist_comm]; exact e1)) hαu

theorem histLine_cont {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {p : Ω × HistorySpace 0 0} (hg : IsGood47 W VL VR ζ p) :
    ContinuousOn (histLine p.2) (Ici 0) :=
  (CfRegQ.reg_of_mem_goodCfSet hg.2.2.1.1).2.2.2.2.1

theorem histLine_zero {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {p : Ω × HistorySpace 0 0} (hg : IsGood47 W VL VR ζ p) :
    histLine p.2 0 = 0 :=
  (CfRegQ.reg_of_mem_goodCfSet hg.2.2.1.1).2.2.2.1

/-! ### The announcing times -/

section Def

variable {Ω : Type*} {nL nR : ℕ}

/-- The rational times `q ∈ [0, n]` up to which the balls of radius `1/(n+1)` around the rational positions of the
counterflow miss `G = R(K_q)`. -/
def IsAway (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
    (n : ℕ) (p : Ω × HistorySpace 0 0) (q : ℚ) : Prop :=
  ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n) ∧ ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
    Disjoint (ball (histLine p.2 u) (1 / ((n : ℝ) + 1))) (qObs W VL VR ζ s p)

open scoped Classical in
/-- The capacity of the rational time `q` when it is away, `0` otherwise. -/
def awayCap (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) (n : ℕ)
    (p : Ω × HistorySpace 0 0) (q : ℚ) : ℝ≥0 :=
  if IsAway W VL VR ζ s n p q then (capClock (qgCurve W s E p) q).toNNReal else 0

open scoped Classical in
/-- **The announcing times** of the image word. -/
def qAnn (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) (n : ℕ)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  if p ∈ E then ⨆ q : ℚ, awayCap W VL VR ζ s E n p q else 0

end Def

section Ann

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

omit mΩ in
theorem isAway_mono {n m : ℕ} (hnm : n ≤ m) {p : Ω × HistorySpace 0 0} {q : ℚ} (h : IsAway W VL VR ζ s n p q) :
    IsAway W VL VR ζ s m p q := by
  obtain ⟨⟨h0, hq⟩, hb⟩ := h
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  refine ⟨⟨h0, hq.trans hnm'⟩, fun u hu0 huq => (hb u hu0 huq).mono_left (ball_subset_ball ?_)⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

omit mΩ in
/-- On good samples, every away time is before the first contact. -/
theorem isAway_mem_gPre {p : Ω × HistorySpace 0 0} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {n : ℕ}
    {q : ℚ} (h : IsAway W VL VR ζ s n p q) : (q : ℝ) ∈ qgPre W VL VR ζ s E p := by
  rw [qgPre_of_mem hp]
  exact (mem_preContact_iff_ball (histLine_cont (hEg p hp)) (isClosed_qObs (hEg p hp)) h.1.1).2 ⟨n, h.2⟩

omit mΩ in
/-- **The supremum of the away times is before the first contact**, and bounds every away time. -/
theorem exists_away_bound {p : Ω × HistorySpace 0 0} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (n : ℕ)
    (hne : ∃ q, IsAway W VL VR ζ s n p q) :
    ∃ τ ∈ qgPre W VL VR ζ s E p, ∀ q, IsAway W VL VR ζ s n p q → (q : ℝ) ≤ τ := by
  set Q : Set ℝ := {x | ∃ q : ℚ, IsAway W VL VR ζ s n p q ∧ (q : ℝ) = x} with hQdef
  have hbdd : BddAbove Q := ⟨n, by rintro _ ⟨q, hq, rfl⟩; exact hq.1.2⟩
  obtain ⟨q₀, hq₀⟩ := hne
  have hQne : Q.Nonempty := ⟨q₀, q₀, hq₀, rfl⟩
  have hle : ∀ q, IsAway W VL VR ζ s n p q → (q : ℝ) ≤ sSup Q := fun q hq => le_csSup hbdd ⟨q, hq, rfl⟩
  refine ⟨sSup Q, ?_, hle⟩
  rw [qgPre_of_mem hp]
  refine mem_preContact_of_ball_bound' (histLine_cont (hEg p hp)) (histLine_zero (hEg p hp))
    (qObs_subset_H W VL VR ζ s p) (hq₀.1.1.trans (hle q₀ hq₀))
    (c := 1 / ((n : ℝ) + 1)) (by positivity) fun u hu0 huτ => ?_
  obtain ⟨_, ⟨q, hq, rfl⟩, huq⟩ := exists_lt_of_lt_csSup hQne huτ
  exact hq.2 u hu0 huq.le

omit mΩ in
theorem awayCap_le {p : Ω × HistorySpace 0 0} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    {n : ℕ} {τ : ℝ} (hτ : τ ∈ qgPre W VL VR ζ s E p) (hb : ∀ q, IsAway W VL VR ζ s n p q → (q : ℝ) ≤ τ) (q : ℚ) :
    awayCap W VL VR ζ s E n p q ≤ (capClock (qgCurve W s E p) τ).toNNReal := by
  classical
  unfold awayCap
  split_ifs with h
  · exact Real.toNNReal_le_toNNReal ((isKilledCurve_qgCurve hEg p).strictMonoOn_capClock.monotoneOn
      (isAway_mem_gPre hp hEg h) hτ (hb q h))
  · exact zero_le

omit mΩ in
/-- **The announcing times are before the killing time**, at every sample. -/
theorem qAnn_lt_qT (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (n : ℕ) (p : Ω × HistorySpace 0 0) :
    (qAnn W VL VR ζ s E n p : WithTop ℝ≥0) < qT W VL VR ζ s E p := by
  classical
  have hK := isKilledCurve_qgCurve (q := s) hEg p
  by_cases hp : p ∈ E
  · simp only [qAnn, hp, ↓reduceIte]
    by_cases hne : ∃ q, IsAway W VL VR ζ s n p q
    · obtain ⟨τ, hτ, hb⟩ := exists_away_bound hp hEg n hne
      exact lt_of_le_of_lt (WithTop.coe_le_coe.2 (ciSup_le fun q => awayCap_le hp hEg hτ hb q))
        (hK.lt_kcLife hτ)
    · push Not at hne
      have h0 : ∀ q, awayCap W VL VR ζ s E n p q = 0 := fun q => by simp only [awayCap, hne q, ↓reduceIte]
      simp only [h0, ciSup_const, WithTop.coe_zero]
      exact hK.zero_lt_kcLife
  · simp only [qAnn, hp, ↓reduceIte, WithTop.coe_zero]
    exact hK.zero_lt_kcLife

omit mΩ in
theorem bddAbove_awayCap (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (n : ℕ) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ E) : BddAbove (Set.range (awayCap W VL VR ζ s E n p)) := by
  classical
  by_cases hne : ∃ q, IsAway W VL VR ζ s n p q
  · obtain ⟨τ, hτ, hb⟩ := exists_away_bound hp hEg n hne
    exact ⟨_, by rintro _ ⟨q, rfl⟩; exact awayCap_le hp hEg hτ hb q⟩
  · push Not at hne
    exact ⟨0, by rintro _ ⟨q, rfl⟩; simp only [awayCap, hne q, ↓reduceIte, le_refl]⟩

omit mΩ in
/-- **The announcing times increase.** -/
theorem monotone_qAnn (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (p : Ω × HistorySpace 0 0) :
    Monotone (qAnn W VL VR ζ s E · p) := by
  classical
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases hp : p ∈ E
  · simp only [qAnn, hp, ↓reduceIte]
    refine ciSup_mono (bddAbove_awayCap hEg (n + 1) hp) fun q => ?_
    unfold awayCap
    by_cases h : IsAway W VL VR ζ s n p q
    · simp only [h, (isAway_mono (Nat.le_succ n) h), ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]
      exact zero_le
  · simp only [qAnn, hp, ↓reduceIte, le_refl]

omit mΩ in
/-- **The announcing times exhaust the killing time** on good samples. -/
theorem exists_le_qAnn (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E)
    {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) < qT W VL VR ζ s E p) : ∃ n, u ≤ qAnn W VL VR ζ s E n p := by
  classical
  have hK := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨S, hS, huS⟩ := hK.lt_kcLife_iff_exists.1 hu
  obtain ⟨S', hS', hSS'⟩ := hK.exists_gt S hS
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hSS'
  have hqP : (q : ℝ) ∈ qgPre W VL VR ζ s E p := hK.icc S' hS' ⟨(hK.nonneg S hS).trans hq1.le, hq2.le⟩
  have hqP' := hqP
  rw [qgPre_of_mem hp] at hqP'
  obtain ⟨m, hm⟩ := (mem_preContact_iff_ball (histLine_cont (hEg p hp)) (isClosed_qObs (hEg p hp))
    (hK.nonneg _ hqP)).1 hqP'
  obtain ⟨N, hN⟩ := exists_nat_ge (q : ℝ)
  refine ⟨max m N, ?_⟩
  have haway : IsAway W VL VR ζ s (max m N) p q := by
    refine ⟨⟨hK.nonneg _ hqP, hN.trans (by exact_mod_cast le_max_right m N)⟩, fun u hu0 huq =>
      (hm u hu0 huq).mono_left (ball_subset_ball ?_)⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left m N) 1)
  simp only [qAnn, hp, ↓reduceIte]
  refine le_trans ?_ (le_ciSup (bddAbove_awayCap hEg _ hp) q)
  simp only [awayCap, haway, ↓reduceIte]
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hK.capClock_nonneg hqP)]
  exact huS.le.trans (hK.strictMonoOn_capClock.monotoneOn hS hqP hq1.le)

/-- **The announcing times are measurable.** -/
theorem measurable_qAnn (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (n : ℕ) : Measurable (qAnn W VL VR ζ s E n) := by
  classical
  have hAway : ∀ q : ℚ, MeasurableSet {p | IsAway W VL VR ζ s n p q} := by
    intro q
    by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n
    · have e : {p | IsAway W VL VR ζ s n p q} = ⋂ u : ℚ, ({_p : Ω × HistorySpace 0 0 | (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q}ᶜ ∪
          {p | Disjoint (ball (histLine p.2 u) (1 / ((n : ℝ) + 1))) (qObs W VL VR ζ s p)}) := by
        ext p
        simp only [IsAway, hq, true_and, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, not_and]
        refine forall_congr' fun u => ?_
        constructor
        · intro h
          by_cases hu : (0 : ℝ) ≤ u
          · by_cases huq : (u : ℝ) ≤ q
            · exact Or.inr (h hu huq)
            · exact Or.inl fun _ => huq
          · exact Or.inl fun h' => absurd h' hu
        · rintro (h | h) hu huq
          · exact absurd huq (h hu)
          · exact h
      rw [e]
      exact MeasurableSet.iInter fun u => (MeasurableSet.const _).compl.union
        (measurableSet_disjoint_ball ((measurable_histLine u).comp measurable_snd)
          (measurable_qObs hX s) (qObs_subset_H W VL VR ζ s) _)
    · have e : {p | IsAway W VL VR ζ s n p q} = ∅ := by
        ext p
        simp only [IsAway, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hq
      rw [e]
      exact MeasurableSet.empty
  have hcap := measurable_indicator_capClock_qgCurve (q := s) hX hE hEg
  set A' : ℚ → Ω × HistorySpace 0 0 → ℝ≥0 := fun q p => if IsAway W VL VR ζ s n p q then
    (({p | (q : ℝ) ∈ qgPre W VL VR ζ s E p}.indicator fun p => capClock (qgCurve W s E p) q) p).toNNReal else 0
    with hA'
  have hA'm : ∀ q, Measurable (A' q) := fun q =>
    Measurable.ite (hAway q) (hcap q).real_toNNReal measurable_const
  have heq : qAnn W VL VR ζ s E n = fun p => if p ∈ E then ⨆ q : ℚ, A' q p else 0 := by
    funext p
    by_cases hp : p ∈ E
    · simp only [qAnn, hp, ↓reduceIte]
      refine iSup_congr fun q => ?_
      by_cases h : IsAway W VL VR ζ s n p q
      · simp only [awayCap, hA', h, ↓reduceIte,
          indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ qgPre W VL VR ζ s E p} from isAway_mem_gPre hp hEg h)]
      · simp only [awayCap, hA', h, ↓reduceIte]
    · simp only [qAnn, hp, ↓reduceIte]
  rw [heq]
  exact Measurable.ite hE (Measurable.iSup hA'm) measurable_const

end Ann

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
