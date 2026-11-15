/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondWordMeas

/-!
# The image word of the flow line given the counterflow prefix: announcing the killing time

Packet PROVE-GLUECOND5, G4 for Proposition 4.9's direction at general `κ` (the general-`κ` form of WangWu's
`ReverseContactMartAnn`, PROVE-WW-B17). The killing time `imgT` of the image word (the capacity of the first contact of
the flow line with `G = R(K′_s)`) is announced by the capacity times `σₙ` of the last rational time `q ≤ n` up to which
every ball of radius `1/(n+1)` around a rational position of the flow line misses `G`:
`σₙ = sup {σ(q) : q ∈ ℚ ∩ [0, n], ball(η(u), 1/(n+1)) ∩ G = ∅ for all rational u ∈ [0, q]}` on good samples (`0`
elsewhere). Unlike the κ = 4 version, `G` is the filled hull of a non-simple curve; only its closedness is used.

* `mem_preContact_of_ball_bound` (deterministic): balls of a fixed radius around the rational positions before `τ`
  missing a closed `G ⊆ ℍ` put `τ` before the first contact;
* **`imgAnn_lt_imgT`**, **`monotone_imgAnn`**, **`exists_le_imgAnn`**, **`measurable_imgAnn`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q
open Sec7.Lemma71C Sec7.Lemma71E Restart

namespace Word49

/-- **A uniform ball bound before `τ` puts `τ` before the first contact.** If the balls of radius `c > 0` around the
rational positions of the proper arc `α` at times in `[0, τ)` miss the closed `G ⊆ ℍ`, then `τ` is before the first
contact of `α` with `G`. -/
theorem mem_preContact_of_ball_bound {α : ℝ → ℂ} (hα : IsProperArc α) {G : Set ℂ} (hGH : G ⊆ H) {τ : ℝ}
    (hτ : 0 ≤ τ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) < τ → Disjoint (ball (α u) c) G) : τ ∈ preContact α G := by
  refine ⟨hτ, fun u hu hαu => ?_⟩
  rcases hu.1.eq_or_lt with hu0 | hu0
  · rw [← hu0, hα.zero] at hαu
    exact GlueCond.zero_notMem_H (hGH hαu)
  have hcα : ContinuousWithinAt α (Icc 0 u) u := (hα.cont u hu.1).mono Icc_subset_Ici_self
  obtain ⟨δ, hδ, hαδ⟩ := Metric.continuousWithinAt_iff.1 hcα c hc
  obtain ⟨u', hu'1, hu'2⟩ := exists_rat_btwn (show max 0 (u - δ) < u from max_lt hu0 (by linarith))
  have hu'0 : (0 : ℝ) ≤ u' := (le_max_left _ _).trans hu'1.le
  have e1 := hαδ (x := (u' : ℝ)) ⟨hu'0, hu'2.le⟩ (by
    rw [Real.dist_eq, abs_lt]
    have := le_max_right 0 (u - δ)
    constructor <;> linarith)
  exact Set.disjoint_left.1 (hb u' hu'0 (hu'2.trans_le hu.2)) (mem_ball.2 (by rw [dist_comm]; exact e1)) hαu

/-! ### The announcing times -/

section Def

variable {Ω : Type*}

/-- The rational times `q ∈ [0, n]` up to which the balls of radius `1/(n+1)` around the rational positions of the
flow line miss `G = R(K′_s)`. -/
def IsAway (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (p : Ω × HistorySpace 0 0) (q : ℚ) : Prop :=
  ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n) ∧ ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
    Disjoint (ball (seedLine ζ W p.1 u) (1 / ((n : ℝ) + 1))) (cfHullQ s p.2)

open scoped Classical in
/-- The capacity of the rational time `q` when it is away, `0` otherwise. -/
def awayCap (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (n : ℕ)
    (p : Ω × HistorySpace 0 0) (q : ℚ) : ℝ≥0 :=
  if IsAway s ζ W n p q then (capClock (gCurve s ζ W E p) q).toNNReal else 0

open scoped Classical in
/-- **The announcing times** of the image word. -/
def imgAnn (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (n : ℕ)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  if p ∈ E then ⨆ q : ℚ, awayCap s ζ W E n p q else 0

end Def

section Ann

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}

omit mΩ in
theorem isAway_mono {n m : ℕ} (hnm : n ≤ m) {p : Ω × HistorySpace 0 0} {q : ℚ} (h : IsAway s ζ W n p q) :
    IsAway s ζ W m p q := by
  obtain ⟨⟨h0, hq⟩, hb⟩ := h
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  refine ⟨⟨h0, hq.trans hnm'⟩, fun u hu0 huq => (hb u hu0 huq).mono_left (ball_subset_ball ?_)⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

omit mΩ in
theorem closed_cfHullQ_of_good {p : Ω × HistorySpace 0 0} (hg : IsGood49 s ζ W p) : IsClosed (cfHullQ s p.2) := by
  rw [hg.2.2.2.2]; exact hg.2.1

omit mΩ in
/-- On good samples, every away time is before the first contact. -/
theorem isAway_mem_gPre {p : Ω × HistorySpace 0 0} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {n : ℕ}
    {q : ℚ} (h : IsAway s ζ W n p q) : (q : ℝ) ∈ gPre s ζ W E p := by
  rw [gPre_of_mem hp]
  exact (mem_preContact_iff_ball (hEg p hp).1.cont (closed_cfHullQ_of_good (hEg p hp)) h.1.1).2 ⟨n, h.2⟩

omit mΩ in
/-- **The supremum of the away times is before the first contact**, and bounds every away time. -/
theorem exists_away_bound {p : Ω × HistorySpace 0 0} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (n : ℕ)
    (hne : ∃ q, IsAway s ζ W n p q) :
    ∃ τ ∈ gPre s ζ W E p, ∀ q, IsAway s ζ W n p q → (q : ℝ) ≤ τ := by
  set Q : Set ℝ := {x | ∃ q : ℚ, IsAway s ζ W n p q ∧ (q : ℝ) = x} with hQdef
  have hbdd : BddAbove Q := ⟨n, by rintro _ ⟨q, hq, rfl⟩; exact hq.1.2⟩
  obtain ⟨q₀, hq₀⟩ := hne
  have hQne : Q.Nonempty := ⟨q₀, q₀, hq₀, rfl⟩
  have hle : ∀ q, IsAway s ζ W n p q → (q : ℝ) ≤ sSup Q := fun q hq => le_csSup hbdd ⟨q, hq, rfl⟩
  refine ⟨sSup Q, ?_, hle⟩
  rw [gPre_of_mem hp]
  refine mem_preContact_of_ball_bound (hEg p hp).1 (cfHullQ_relClosed s p.2).1 (hq₀.1.1.trans (hle q₀ hq₀))
    (c := 1 / ((n : ℝ) + 1)) (by positivity) fun u hu0 huτ => ?_
  obtain ⟨_, ⟨q, hq, rfl⟩, huq⟩ := exists_lt_of_lt_csSup hQne huτ
  exact hq.2 u hu0 huq.le

omit mΩ in
theorem awayCap_le {p : Ω × HistorySpace 0 0} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    {n : ℕ} {τ : ℝ} (hτ : τ ∈ gPre s ζ W E p) (hb : ∀ q, IsAway s ζ W n p q → (q : ℝ) ≤ τ) (q : ℚ) :
    awayCap s ζ W E n p q ≤ (capClock (gCurve s ζ W E p) τ).toNNReal := by
  classical
  unfold awayCap
  split_ifs with h
  · exact Real.toNNReal_le_toNNReal ((isKilledArc_gCurve hEg p).strictMonoOn_capClock.monotoneOn
      (isAway_mem_gPre hp hEg h) hτ (hb q h))
  · exact zero_le

omit mΩ in
/-- **The announcing times are before the killing time**, at every sample. -/
theorem imgAnn_lt_imgT (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (n : ℕ) (p : Ω × HistorySpace 0 0) :
    (imgAnn s ζ W E n p : WithTop ℝ≥0) < imgT s ζ W E p := by
  classical
  have hK := isKilledArc_gCurve hEg (s := s) (ζ := ζ) (W := W) p
  by_cases hp : p ∈ E
  · simp only [imgAnn, hp, ↓reduceIte]
    by_cases hne : ∃ q, IsAway s ζ W n p q
    · obtain ⟨τ, hτ, hb⟩ := exists_away_bound hp hEg n hne
      exact lt_of_le_of_lt (WithTop.coe_le_coe.2 (ciSup_le fun q => awayCap_le hp hEg hτ hb q))
        (hK.lt_kLife hτ)
    · push Not at hne
      have h0 : ∀ q, awayCap s ζ W E n p q = 0 := fun q => by simp only [awayCap, hne q, ↓reduceIte]
      simp only [h0, ciSup_const, WithTop.coe_zero]
      exact hK.zero_lt_kLife
  · simp only [imgAnn, hp, ↓reduceIte, WithTop.coe_zero]
    exact hK.zero_lt_kLife

omit mΩ in
theorem bddAbove_awayCap (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (n : ℕ) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ E) : BddAbove (Set.range (awayCap s ζ W E n p)) := by
  classical
  by_cases hne : ∃ q, IsAway s ζ W n p q
  · obtain ⟨τ, hτ, hb⟩ := exists_away_bound hp hEg n hne
    exact ⟨_, by rintro _ ⟨q, rfl⟩; exact awayCap_le hp hEg hτ hb q⟩
  · push Not at hne
    exact ⟨0, by rintro _ ⟨q, rfl⟩; simp only [awayCap, hne q, ↓reduceIte, le_refl]⟩

omit mΩ in
/-- **The announcing times increase.** -/
theorem monotone_imgAnn (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) :
    Monotone (imgAnn s ζ W E · p) := by
  classical
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases hp : p ∈ E
  · simp only [imgAnn, hp, ↓reduceIte]
    refine ciSup_mono (bddAbove_awayCap hEg (n + 1) hp) fun q => ?_
    unfold awayCap
    by_cases h : IsAway s ζ W n p q
    · simp only [h, (isAway_mono (Nat.le_succ n) h), ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]
      exact zero_le
  · simp only [imgAnn, hp, ↓reduceIte, le_refl]

omit mΩ in
/-- **The announcing times exhaust the killing time** on good samples. -/
theorem exists_le_imgAnn (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E)
    {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) < imgT s ζ W E p) : ∃ n, u ≤ imgAnn s ζ W E n p := by
  classical
  have hK := isKilledArc_gCurve hEg (s := s) (ζ := ζ) (W := W) p
  obtain ⟨S, hS, huS⟩ := lt_kLife_iff.1 hu
  obtain ⟨S', hS', hSS'⟩ := hK.exists_gt S hS
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hSS'
  have hqP : (q : ℝ) ∈ gPre s ζ W E p := hK.icc S' hS' ⟨(hK.nonneg S hS).trans hq1.le, hq2.le⟩
  have hqP' := hqP
  rw [gPre_of_mem hp] at hqP'
  obtain ⟨m, hm⟩ := (mem_preContact_iff_ball (hEg p hp).1.cont (closed_cfHullQ_of_good (hEg p hp))
    (hK.nonneg _ hqP)).1 hqP'
  obtain ⟨N, hN⟩ := exists_nat_ge (q : ℝ)
  refine ⟨max m N, ?_⟩
  have haway : IsAway s ζ W (max m N) p q := by
    refine ⟨⟨hK.nonneg _ hqP, hN.trans (by exact_mod_cast le_max_right m N)⟩, fun u hu0 huq =>
      (hm u hu0 huq).mono_left (ball_subset_ball ?_)⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left m N) 1)
  simp only [imgAnn, hp, ↓reduceIte]
  refine le_trans ?_ (le_ciSup (bddAbove_awayCap hEg _ hp) q)
  simp only [awayCap, haway, ↓reduceIte]
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hK.capClock_nonneg hqP)]
  exact huS.le.trans (hK.strictMonoOn_capClock.monotoneOn hS hqP hq1.le)

/-- **The announcing times are measurable.** -/
theorem measurable_imgAnn (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (n : ℕ) : Measurable (imgAnn s ζ W E n) := by
  classical
  have hAway : ∀ q : ℚ, MeasurableSet {p | IsAway s ζ W n p q} := by
    intro q
    by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n
    · have e : {p | IsAway s ζ W n p q} = ⋂ u : ℚ, ({_p : Ω × HistorySpace 0 0 | (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q}ᶜ ∪
          {p | Disjoint (ball (seedLine ζ W p.1 u) (1 / ((n : ℝ) + 1))) (cfHullQ s p.2)}) := by
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
        (measurableSet_disjoint_ball ((measurable_seedLine hW u).comp measurable_fst)
          ((measurable_cfHullQ s).comp measurable_snd) (fun p => (cfHullQ_relClosed s p.2).1) _)
    · have e : {p | IsAway s ζ W n p q} = ∅ := by
        ext p
        simp only [IsAway, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hq
      rw [e]
      exact MeasurableSet.empty
  have hcap := measurable_indicator_capClock_gCurve hW hE hEg
  set A' : ℚ → Ω × HistorySpace 0 0 → ℝ≥0 := fun q p => if IsAway s ζ W n p q then
    (({p | (q : ℝ) ∈ gPre s ζ W E p}.indicator fun p => capClock (gCurve s ζ W E p) q) p).toNNReal else 0
    with hA'
  have hA'm : ∀ q, Measurable (A' q) := fun q =>
    Measurable.ite (hAway q) (hcap q).real_toNNReal measurable_const
  have heq : imgAnn s ζ W E n = fun p => if p ∈ E then ⨆ q : ℚ, A' q p else 0 := by
    funext p
    by_cases hp : p ∈ E
    · simp only [imgAnn, hp, ↓reduceIte]
      refine iSup_congr fun q => ?_
      by_cases h : IsAway s ζ W n p q
      · simp only [awayCap, hA', h, ↓reduceIte,
          indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ gPre s ζ W E p} from isAway_mem_gPre hp hEg h)]
      · simp only [awayCap, hA', h, ↓reduceIte]
    · simp only [imgAnn, hp, ↓reduceIte]
  rw [heq]
  exact Measurable.ite hE (Measurable.iSup hA'm) measurable_const

end Ann

end Word49

end InteractingSLE.Sec5.CrossCond
