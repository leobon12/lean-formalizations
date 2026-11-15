/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartBase

/-!
# The image word of the contact step, part 7: announcing the killing time

Packet PROVE-WW-B17, step B2 of PROVE-WW-B15's plan. The killing time `imgT` of the image word (its terminal capacity)
is announced by the capacity times `σₙ` of the first approach of the forward line `α` within `1/(n+1)` of
`G = R(β((0, s]))`, capped at forward time `n`, read through rational times:

`σₙ = sup {σ(q) : q ∈ ℚ ∩ [0, n], ‖α(u) − R(β(v))‖ ≥ 1/(n+1) for all rational u ∈ [0, q], v ∈ (0, s]}`

on good samples (`0` elsewhere). This is a non-anticipating time (the capacity of a forward hitting time).

* `mem_preContact_of_bound` (deterministic): a uniform distance of the rational positions of `α` before `τ` from the
  rational positions of `R ∘ β` puts `τ` before the first contact;
* **`imgAnn_lt_imgT`**, **`monotone_imgAnn`**, **`exists_le_imgAnn`**, **`measurable_imgAnn`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C Sec7.Lemma71E Restart ImgWord LawUnique

/-- **A uniform distance before `τ` puts `τ` before the first contact.** If the rational positions of the simple
proper arc `α` at times in `[0, τ)` keep distance `≥ c > 0` from the rational positions of `R ∘ β` on `(0, s]`, then
`τ` is before the first contact of `α` with `G = R(β((0, s]))`. -/
theorem mem_preContact_of_bound {α β : ℝ → ℂ} (hα : IsProperArc α) (hβ : IsProperArc β) {s : ℚ} {τ : ℝ}
    (hτ : 0 ≤ τ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ u v : ℚ, (0 : ℝ) ≤ u → (u : ℝ) < τ → (0 : ℝ) < v → (v : ℝ) ≤ s → c ≤ ‖α u - negInv (β v)‖) :
    τ ∈ preContact α (negInv '' (β '' Ioc 0 s)) := by
  refine ⟨hτ, fun u hu hαu => ?_⟩
  obtain ⟨_, ⟨v, hv, rfl⟩, hve⟩ := hαu
  have hβv : β v ≠ 0 := ne_zero_of_mem_H (hβ.mem_H v hv.1)
  rcases hu.1.eq_or_lt with hu0 | hu0
  · rw [← hu0, hα.zero] at hve
    exact (neg_ne_zero.2 (inv_ne_zero hβv)) hve
  set ε : ℝ := c / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hcα : ContinuousWithinAt α (Icc 0 u) u := (hα.cont u hu.1).mono Icc_subset_Ici_self
  have hcβ : ContinuousWithinAt (fun v => negInv (β v)) (Ioc 0 s) v :=
    (continuousAt_negInv hβv).comp_continuousWithinAt ((hβ.cont v (le_of_lt hv.1)).mono
      fun _ hx => le_of_lt hx.1)
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1 hcα ε hε0
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 hcβ ε hε0
  obtain ⟨u', hu'1, hu'2⟩ := exists_rat_btwn (show max 0 (u - δ₁) < u from max_lt hu0 (by linarith))
  have hu'0 : (0 : ℝ) ≤ u' := (le_max_left _ _).trans hu'1.le
  obtain ⟨v', hv', hv'd⟩ := exists_rat_mem_Ioc_near (a := 0) (b := s) (by simpa using hv) hδ₂
  simp only [Rat.cast_zero] at hv'
  have e1 := h₁ (x := (u' : ℝ)) ⟨hu'0, hu'2.le⟩ (by
    rw [Real.dist_eq, abs_lt]
    have := le_max_right 0 (u - δ₁)
    constructor <;> linarith)
  have e2 := h₂ hv' (by rw [Real.dist_eq]; exact hv'd)
  have key := hb u' v' hu'0 (hu'2.trans_le hu.2) hv'.1 hv'.2
  rw [dist_eq_norm] at e1 e2
  have htri : ‖α u' - negInv (β v')‖ ≤ ‖α u' - α u‖ + ‖negInv (β v) - negInv (β v')‖ := by
    calc ‖α u' - negInv (β v')‖ = ‖(α u' - α u) + (negInv (β v) - negInv (β v'))‖ := by
          rw [← hve]; ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev (negInv (β v))] at htri
  linarith

/-! ### The announcing times -/

namespace ImgWord

variable {Ω : Type*}

/-- The rational forward times `q ∈ [0, n]` up to which the forward line stays `1/(n+1)`-away from `R ∘ β`. -/
def IsAway (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (p : Ω × HistorySpace 1 1) (q : ℚ) : Prop :=
  ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n) ∧ ∀ u v : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
    1 / ((n : ℝ) + 1) ≤ ‖seedLine ζ W p.1 u - negInv (frzLine s p.2 v)‖

open scoped Classical in
/-- The capacity of the rational time `q` when it is away, `0` otherwise. -/
def awayCap (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) (n : ℕ)
    (p : Ω × HistorySpace 1 1) (q : ℚ) : ℝ≥0 :=
  if IsAway s ζ W n p q then (capClock (gCurve s ζ W E p) q).toNNReal else 0

open scoped Classical in
/-- **The announcing times** of the image word. -/
def imgAnn (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) (n : ℕ)
    (p : Ω × HistorySpace 1 1) : ℝ≥0 :=
  if p ∈ E then ⨆ q : ℚ, awayCap s ζ W E n p q else 0

end ImgWord

section Ann

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℚ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

omit mΩ in
theorem isAway_mono {n m : ℕ} (hnm : n ≤ m) {p : Ω × HistorySpace 1 1} {q : ℚ} (h : IsAway s ζ W n p q) :
    IsAway s ζ W m p q := by
  obtain ⟨⟨h0, hq⟩, hb⟩ := h
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  refine ⟨⟨h0, hq.trans hnm'⟩, fun u v hu0 huq hv0 hvs => ?_⟩
  refine le_trans ?_ (hb u v hu0 huq hv0 hvs)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

omit mΩ in
/-- On good samples, every away time is before the first contact. -/
theorem isAway_mem_gPre (hs : 0 < s) {p : Ω × HistorySpace 1 1} (hp : p ∈ E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {n : ℕ} {q : ℚ} (h : IsAway s ζ W n p q) :
    (q : ℝ) ∈ gPre s ζ W E p := by
  obtain ⟨hG, hβ, hGc⟩ := glueG_eq hs (hEg p hp)
  rw [gPre_of_mem hp, hG]
  rw [hG] at hGc
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  exact (mem_preContact_iff_rat (hEg p hp).1 hβ hGc h.1.1 hs').2 ⟨n, h.2⟩

omit mΩ in
/-- **The supremum of the away times is before the first contact**, and bounds every away time. -/
theorem exists_away_bound (hs : 0 < s) {p : Ω × HistorySpace 1 1} (hp : p ∈ E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (n : ℕ) (hne : ∃ q, IsAway s ζ W n p q) :
    ∃ τ ∈ gPre s ζ W E p, ∀ q, IsAway s ζ W n p q → (q : ℝ) ≤ τ := by
  set Q : Set ℝ := {x | ∃ q : ℚ, IsAway s ζ W n p q ∧ (q : ℝ) = x} with hQdef
  have hbdd : BddAbove Q := ⟨n, by rintro _ ⟨q, hq, rfl⟩; exact hq.1.2⟩
  obtain ⟨q₀, hq₀⟩ := hne
  have hQne : Q.Nonempty := ⟨q₀, q₀, hq₀, rfl⟩
  have hle : ∀ q, IsAway s ζ W n p q → (q : ℝ) ≤ sSup Q := fun q hq => le_csSup hbdd ⟨q, hq, rfl⟩
  refine ⟨sSup Q, ?_, hle⟩
  obtain ⟨hG, hβ, -⟩ := glueG_eq hs (hEg p hp)
  rw [gPre_of_mem hp, hG]
  refine mem_preContact_of_bound (hEg p hp).1 hβ (hq₀.1.1.trans (hle q₀ hq₀)) (c := 1 / ((n : ℝ) + 1))
    (by positivity) fun u v hu0 huτ hv0 hvs => ?_
  obtain ⟨_, ⟨q, hq, rfl⟩, huq⟩ := exists_lt_of_lt_csSup hQne huτ
  exact hq.2 u v hu0 huq.le hv0 hvs

omit mΩ in
theorem awayCap_le (hs : 0 < s) {p : Ω × HistorySpace 1 1} (hp : p ∈ E) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    {n : ℕ} {τ : ℝ} (hτ : τ ∈ gPre s ζ W E p) (hb : ∀ q, IsAway s ζ W n p q → (q : ℝ) ≤ τ) (q : ℚ) :
    awayCap s ζ W E n p q ≤ (capClock (gCurve s ζ W E p) τ).toNNReal := by
  classical
  unfold awayCap
  split_ifs with h
  · exact Real.toNNReal_le_toNNReal ((isKilledArc_gCurve hs hEg p).strictMonoOn_capClock.monotoneOn
      (isAway_mem_gPre hs hp hEg h) hτ (hb q h))
  · exact zero_le

omit mΩ in
/-- **The announcing times are before the killing time**, at every sample. -/
theorem imgAnn_lt_imgT (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (n : ℕ) (p : Ω × HistorySpace 1 1) :
    (imgAnn s ζ W E n p : WithTop ℝ≥0) < imgT s ζ W E p := by
  classical
  have hK := isKilledArc_gCurve hs hEg (ζ := ζ) (W := W) p
  by_cases hp : p ∈ E
  · simp only [imgAnn, hp, ↓reduceIte]
    by_cases hne : ∃ q, IsAway s ζ W n p q
    · obtain ⟨τ, hτ, hb⟩ := exists_away_bound hs hp hEg n hne
      exact lt_of_le_of_lt (WithTop.coe_le_coe.2 (ciSup_le fun q => awayCap_le hs hp hEg hτ hb q))
        (hK.lt_kLife hτ)
    · push Not at hne
      have h0 : ∀ q, awayCap s ζ W E n p q = 0 := fun q => by simp only [awayCap, hne q, ↓reduceIte]
      simp only [h0, ciSup_const, WithTop.coe_zero]
      exact hK.zero_lt_kLife
  · simp only [imgAnn, hp, ↓reduceIte, WithTop.coe_zero]
    exact hK.zero_lt_kLife

omit mΩ in
theorem bddAbove_awayCap (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (n : ℕ) {p : Ω × HistorySpace 1 1}
    (hp : p ∈ E) : BddAbove (Set.range (awayCap s ζ W E n p)) := by
  classical
  by_cases hne : ∃ q, IsAway s ζ W n p q
  · obtain ⟨τ, hτ, hb⟩ := exists_away_bound hs hp hEg n hne
    exact ⟨_, by rintro _ ⟨q, rfl⟩; exact awayCap_le hs hp hEg hτ hb q⟩
  · push Not at hne
    exact ⟨0, by rintro _ ⟨q, rfl⟩; simp only [awayCap, hne q, ↓reduceIte, le_refl]⟩

omit mΩ in
/-- **The announcing times increase.** -/
theorem monotone_imgAnn (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) :
    Monotone (imgAnn s ζ W E · p) := by
  classical
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases hp : p ∈ E
  · simp only [imgAnn, hp, ↓reduceIte]
    refine ciSup_mono (bddAbove_awayCap hs hEg (n + 1) hp) fun q => ?_
    unfold awayCap
    by_cases h : IsAway s ζ W n p q
    · simp only [h, (isAway_mono (Nat.le_succ n) h), ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]
      exact zero_le
  · simp only [imgAnn, hp, ↓reduceIte, le_refl]

omit mΩ in
/-- **The announcing times exhaust the killing time** on good samples. -/
theorem exists_le_imgAnn (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {p : Ω × HistorySpace 1 1} (hp : p ∈ E)
    {u : ℝ≥0} (hu : (u : WithTop ℝ≥0) < imgT s ζ W E p) : ∃ n, u ≤ imgAnn s ζ W E n p := by
  classical
  have hK := isKilledArc_gCurve hs hEg (ζ := ζ) (W := W) p
  obtain ⟨S, hS, huS⟩ := lt_kLife_iff.1 hu
  obtain ⟨S', hS', hSS'⟩ := hK.exists_gt S hS
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hSS'
  have hqP : (q : ℝ) ∈ gPre s ζ W E p := hK.icc S' hS' ⟨(hK.nonneg S hS).trans hq1.le, hq2.le⟩
  obtain ⟨hG, hβ, hGc⟩ := glueG_eq hs (hEg p hp)
  have hqP' := hqP
  rw [gPre_of_mem hp, hG] at hqP'
  rw [hG] at hGc
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨m, hm⟩ := (mem_preContact_iff_rat (hEg p hp).1 hβ hGc (hK.nonneg _ hqP) hs').1 hqP'
  obtain ⟨N, hN⟩ := exists_nat_ge (q : ℝ)
  refine ⟨max m N, ?_⟩
  have haway : IsAway s ζ W (max m N) p q := by
    refine ⟨⟨hK.nonneg _ hqP, hN.trans (by exact_mod_cast le_max_right m N)⟩, fun u v hu0 huq hv0 hvs => ?_⟩
    refine le_trans ?_ (hm u v hu0 huq hv0 hvs)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left m N) 1)
  simp only [imgAnn, hp, ↓reduceIte]
  refine le_trans ?_ (le_ciSup (bddAbove_awayCap hs hEg _ hp) q)
  simp only [awayCap, haway, ↓reduceIte]
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hK.capClock_nonneg hqP)]
  exact huS.le.trans (hK.strictMonoOn_capClock.monotoneOn hS hqP hq1.le)

/-- **The announcing times are measurable.** -/
theorem measurable_imgAnn (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (n : ℕ) : Measurable (imgAnn s ζ W E n) := by
  classical
  have hAway : ∀ q : ℚ, MeasurableSet {p | IsAway s ζ W n p q} := by
    intro q
    by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n
    · have e : {p | IsAway s ζ W n p q} = ⋂ u : ℚ, ⋂ v : ℚ, {p : Ω × HistorySpace 1 1 | (0 : ℝ) ≤ u →
          (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
          1 / ((n : ℝ) + 1) ≤ ‖seedLine ζ W p.1 u - negInv (frzLine s p.2 v)‖} := by
        ext p
        simp only [IsAway, hq, true_and, mem_ofPred_eq, mem_iInter]
      rw [e]
      refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => ?_
      by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q ∧ (0 : ℝ) < v ∧ (v : ℝ) ≤ s
      · obtain ⟨h1, h2, h3, h4⟩ := hc
        simp only [h1, h2, h3, h4, forall_const]
        exact measurableSet_le measurable_const
          ((((measurable_seedLine hW u).comp measurable_fst).sub
            (measurable_negInv.comp ((measurable_frzLine s v).comp measurable_snd))).norm)
      · have e' : {p : Ω × HistorySpace 1 1 | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
            1 / ((n : ℝ) + 1) ≤ ‖seedLine ζ W p.1 u - negInv (frzLine s p.2 v)‖} = univ := by
          ext p
          simp only [mem_ofPred_eq, mem_univ, iff_true]
          intro h1 h2 h3 h4
          exact absurd ⟨h1, h2, h3, h4⟩ hc
        rw [e']
        exact MeasurableSet.univ
    · have e : {p | IsAway s ζ W n p q} = ∅ := by
        ext p
        simp only [IsAway, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hq
      rw [e]
      exact MeasurableSet.empty
  have hcap := measurable_indicator_capClock_gCurve hs hW hE hEg
  set A' : ℚ → Ω × HistorySpace 1 1 → ℝ≥0 := fun q p => if IsAway s ζ W n p q then
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
          indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ gPre s ζ W E p} from isAway_mem_gPre hs hp hEg h)]
      · simp only [awayCap, hA', h, ↓reduceIte]
    · simp only [imgAnn, hp, ↓reduceIte]
  rw [heq]
  exact Measurable.ite hE (Measurable.iSup hA'm) measurable_const

end Ann

end InteractingSLE.WangWu
