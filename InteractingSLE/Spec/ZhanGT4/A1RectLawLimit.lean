/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RectLawCapCont
import InteractingSLE.Spec.Sec2.RestartLaw
import InteractingSLE.Spec.ZhanGT4.A1CanonCore

/-!
# Zhan's A.1: a noise that is a stopped Brownian motion at every cap has a limit at the supremum of the caps

Packet PROVE-A1-RECTLAW. The image noise of A.1's rectangle construction is the compensated residual of the image data;
it is continuous before each cap `c n` and a Brownian motion stopped at each cap (A1-CANON's `IsStoppedBM`), but the
caps only approach the image lifetime `L = sup c n`, where the residual need not converge at every sample. This file
proves that it converges **almost surely**: with probability one, for every horizon `K` and every `ε > 0` the
oscillation of the noise after some cap `c n` and before `K` is at most `ε`.

Proof: fix `K`, `ε`, `δ`. For each `k`, A1-CANON's `isFilteredBrownianReal_capNoise` (one cap `c k`, the noise
stopped at `c k`, continued by an independent Brownian motion `β`) gives a Brownian motion `B'ₖ` on `Ω × Ω₀` with
continuous paths equal to `N` on `[0, c k]`. An oscillation `> ε` of `N` on `[c n, c k] ∩ [0, K]`, with
`c k ∧ K − c n ∧ K ≤ δ`, is an oscillation `> ε` of `B'ₖ` between two rational times at distance `≤ 2δ` below `K + 1`
(`mem_modSet_of_continuous`); the probability of that path event is the same for every Brownian motion
(`map_path_eq_wienerPath`) and tends to `0` with `δ` (uniform continuity of the continuous Brownian motion `β`). The
events increase in `k`, and the probability that `sup_k c k ∧ K − c n ∧ K > δ` tends to `0` as `n → ∞`.

Main results:

* `modSet`, `measurableSet_modSet`, `mem_modSet_of_continuous`;
* `measure_path_mem_modSet`: the probability is `wienerPath (modSet δ ε K)` for every Brownian motion;
* `tendsto_wienerPath_modSet`: it tends to `0` as `δ → 0`;
* **`ae_cauchy_of_isStoppedBM`**: the almost sure oscillation bound after the caps.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectLaw

open A1Canon

/-! ### The rational modulus event on path space -/

section Modulus

/-- **The rational modulus event**: two rational times below `K` at distance at most `δ` where the path oscillates
by more than `ε`. -/
def modSet (δ ε : ℝ) (K : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  {f | ∃ q r : ℚ, (q : ℝ).toNNReal ≤ K ∧ (r : ℝ).toNNReal ≤ K ∧
    |(((q : ℝ).toNNReal : ℝ≥0) : ℝ) - (((r : ℝ).toNNReal : ℝ≥0) : ℝ)| ≤ δ ∧
    ε < |f (q : ℝ).toNNReal - f (r : ℝ).toNNReal|}

theorem measurableSet_modSet (δ ε : ℝ) (K : ℝ≥0) : MeasurableSet (modSet δ ε K) := by
  have e : modSet δ ε K = ⋃ q : ℚ, ⋃ r : ℚ, ({_f : ℝ≥0 → ℝ | (q : ℝ).toNNReal ≤ K ∧ (r : ℝ).toNNReal ≤ K ∧
      |(((q : ℝ).toNNReal : ℝ≥0) : ℝ) - (((r : ℝ).toNNReal : ℝ≥0) : ℝ)| ≤ δ} ∩
      {f | ε < |f (q : ℝ).toNNReal - f (r : ℝ).toNNReal|}) := by
    ext f
    simp only [modSet, mem_ofPred_eq, mem_iUnion, mem_inter_iff, and_assoc]
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter ?_
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((measurable_pi_apply ((q : ℝ).toNNReal)).sub
      (measurable_pi_apply ((r : ℝ).toNNReal))))

theorem modSet_mono {δ δ' ε : ℝ} {K : ℝ≥0} (h : δ ≤ δ') : modSet δ ε K ⊆ modSet δ' ε K :=
  fun _ ⟨q, r, hq, hr, hd, he⟩ => ⟨q, r, hq, hr, hd.trans h, he⟩

/-- Rounding a rational to `ℝ≥0` moves it by at most its distance to a point of `ℝ≥0`. -/
theorem abs_toNNReal_sub_le (q : ℝ) (t : ℝ≥0) : |((q.toNNReal : ℝ≥0) : ℝ) - t| ≤ |q - t| := by
  rw [Real.coe_toNNReal']
  have h := abs_max_sub_max_le_abs q (t : ℝ) 0
  rwa [max_eq_left t.coe_nonneg] at h

/-- **A continuous path with an oscillation `> ε` between two times below `K` at distance `≤ δ` lies in the rational
modulus event** with distance `2δ` below `K + 1`. -/
theorem mem_modSet_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) {t s K : ℝ≥0} {δ ε : ℝ} (hδ : 0 < δ)
    (hts : |(t : ℝ) - s| ≤ δ) (htK : t ≤ K) (hsK : s ≤ K) (h : ε < |f t - f s|) :
    f ∈ modSet (δ + δ) ε (K + 1) := by
  have hF : Continuous fun p : ℝ≥0 × ℝ≥0 => |f p.1 - f p.2| :=
    continuous_abs.comp ((hf.comp continuous_fst).sub (hf.comp continuous_snd))
  have hU : IsOpen {p : ℝ≥0 × ℝ≥0 | ε < |f p.1 - f p.2|} := isOpen_lt continuous_const hF
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hU (t, s) h
  set η' := min η (min (δ / 2) 1) with hη'
  have hη'pos : 0 < η' := lt_min hη (lt_min (by linarith) one_pos)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) - η' < t + η' by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (s : ℝ) - η' < s + η' by linarith)
  have hqt : |(q : ℝ) - t| < η' := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have hrs : |(r : ℝ) - s| < η' := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have hqt' := (abs_toNNReal_sub_le q t).trans_lt hqt
  have hrs' := (abs_toNNReal_sub_le r s).trans_lt hrs
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'δ : η' ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη'1 : η' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q, r, ?_, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one]
    have := (abs_sub_lt_iff.1 hqt').1
    have hK : (t : ℝ) ≤ K := NNReal.coe_le_coe.2 htK
    linarith
  · rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one]
    have := (abs_sub_lt_iff.1 hrs').1
    have hK : (s : ℝ) ≤ K := NNReal.coe_le_coe.2 hsK
    linarith
  · have h1 := abs_sub_le (((q : ℝ).toNNReal : ℝ)) (t : ℝ) ((r : ℝ).toNNReal : ℝ)
    have h2 := abs_sub_le (t : ℝ) (s : ℝ) ((r : ℝ).toNNReal : ℝ)
    have h3 : |(s : ℝ) - ((r : ℝ).toNNReal : ℝ)| < η' := by rw [abs_sub_comm]; exact hrs'
    linarith
  · have hmem : ((q : ℝ).toNNReal, (r : ℝ).toNNReal) ∈ Metric.ball (t, s) η := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, NNReal.dist_eq, NNReal.dist_eq]
      exact ⟨hqt'.trans_le hη'η, hrs'.trans_le hη'η⟩
    exact hball hmem

end Modulus

/-! ### The modulus event has the same probability for every Brownian motion, and it is small -/

section Wiener

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}

/-- **The probability of the rational modulus event is the same for every Brownian motion** (its path law is
`wienerPath`). -/
theorem measure_path_mem_modSet [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P')
    (hm : ∀ s, Measurable (B s)) (δ ε : ℝ) (K : ℝ≥0) :
    P' {ω | (fun s => B s ω) ∈ modSet δ ε K} = Sec2.Restart.wienerPath (modSet δ ε K) := by
  have hmp : Measurable fun ω (s : ℝ≥0) => B s ω := measurable_pi_iff.2 hm
  rw [← Sec2.Restart.map_path_eq_wienerPath hB hmp, Measure.map_apply hmp (measurableSet_modSet δ ε K)]
  rfl

/-- **The rational modulus event has small probability for small `δ`.** Computed with any Brownian motion with
continuous paths (uniform continuity on `[0, K]`). -/
theorem tendsto_wienerPath_modSet [IsProbabilityMeasure P'] {𝓦 : Filtration ℝ≥0 mΩ'} {β : ℝ≥0 → Ω' → ℝ}
    (hβ : IsFilteredBrownianReal 𝓦 β P') (hβc : ∀ w, Continuous (β · w)) (ε : ℝ) (hε : 0 < ε) (K : ℝ≥0) :
    Tendsto (fun j : ℕ => Sec2.Restart.wienerPath (modSet (1 / ((j : ℝ) + 1)) ε K)) atTop (𝓝 0) := by
  have hm : ∀ s, Measurable (β s) := fun s => (hβ.2.1 s).mono (𝓦.le s) le_rfl
  have hmp : Measurable fun ω (s : ℝ≥0) => β s ω := measurable_pi_iff.2 hm
  set A : ℕ → Set Ω' := fun j => {w | (fun s => β s w) ∈ modSet (1 / ((j : ℝ) + 1)) ε K} with hA
  have e : (fun j : ℕ => Sec2.Restart.wienerPath (modSet (1 / ((j : ℝ) + 1)) ε K)) = P' ∘ A := by
    funext j
    exact (measure_path_mem_modSet hβ.1.toIsPreBrownianReal hm _ ε K).symm
  rw [e]
  have hAm : ∀ j, MeasurableSet (A j) := fun j => hmp (measurableSet_modSet _ ε K)
  have hanti : Antitone A := by
    intro i j hij w hw
    simp only [hA, mem_ofPred_eq] at hw ⊢
    refine modSet_mono ?_ hw
    gcongr
  have hempty : (⋂ j, A j) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun w hw => ?_
    have huc : UniformContinuousOn (β · w) (Icc 0 K) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (hβc w).continuousOn
    obtain ⟨η, hη, hu⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη
    obtain ⟨q, r, hq, hr, hd, he⟩ := mem_iInter.1 hw j
    have := hu _ ⟨bot_le, hq⟩ _ ⟨bot_le, hr⟩ (by rw [NNReal.dist_eq]; exact hd.trans_lt hj)
    rw [Real.dist_eq] at this
    exact (lt_asymm he this).elim
  have h := tendsto_measure_iInter_atTop (μ := P') (fun j => (hAm j).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P' _⟩
  rwa [hempty, measure_empty] at h

end Wiener

/-! ### The almost sure oscillation bound after the caps -/

section Cauchy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ}
  {c : ℕ → Ω → ℝ≥0}

/-- The noise stopped at a cap. -/
def stoppedAt (N : ℝ≥0 → Ω → ℝ) (c : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => N (min t (c ω)) ω

theorem continuous_stoppedAt {c : Ω → ℝ≥0} (hNc : ∀ ω, ContinuousOn (N · ω) (Icc 0 (c ω))) (ω : Ω) :
    Continuous (stoppedAt N c · ω) :=
  (hNc ω).comp_continuous (continuous_id.min continuous_const) fun _ => ⟨bot_le, min_le_right _ _⟩

theorem stopExp_stoppedAt (a : ℝ) (c : Ω → ℝ≥0) : stopExp a (stoppedAt N c) c = stopExp a N c := by
  funext t ω
  simp only [stopExp, stoppedAt, min_assoc, min_self]

/-- The large increments after the cap `c n` before `K`: events of the form
`{c k ∧ K − c n ∧ K > δ for some k}`. -/
def gapSet (c : ℕ → Ω → ℝ≥0) (K : ℝ≥0) (δ : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ k, δ < ((min (c k ω) K : ℝ≥0) : ℝ) - ((min (c n ω) K : ℝ≥0) : ℝ)}

theorem tendsto_measure_gapSet [IsProbabilityMeasure P] (hmono : ∀ ω, Monotone fun n => c n ω)
    (hcm : ∀ n, Measurable (c n)) (K : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P (gapSet c K δ n)) atTop (𝓝 0) := by
  have hm : ∀ n, MeasurableSet (gapSet c K δ n) := fun n => by
    have e : gapSet c K δ n = ⋃ k, {ω | δ < ((min (c k ω) K : ℝ≥0) : ℝ) - ((min (c n ω) K : ℝ≥0) : ℝ)} := by
      ext ω; simp only [gapSet, mem_ofPred_eq, mem_iUnion]
    rw [e]
    exact MeasurableSet.iUnion fun k => measurableSet_lt measurable_const
      ((measurable_coe_nnreal_real.comp ((hcm k).min measurable_const)).sub
        (measurable_coe_nnreal_real.comp ((hcm n).min measurable_const)))
  have hanti : Antitone (gapSet c K δ) := by
    intro n n' hnn' ω ⟨k, hk⟩
    refine ⟨k, lt_of_lt_of_le hk ?_⟩
    have : ((min (c n ω) K : ℝ≥0) : ℝ) ≤ ((min (c n' ω) K : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.2 (min_le_min_right _ (hmono ω hnn'))
    linarith
  have hempty : (⋂ n, gapSet c K δ n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    set m : ℕ → ℝ := fun k => ((min (c k ω) K : ℝ≥0) : ℝ) with hmdef
    have hmm : Monotone m := fun i j hij => NNReal.coe_le_coe.2 (min_le_min_right _ (hmono ω hij))
    have hbdd : BddAbove (range m) := ⟨K, by
      rintro _ ⟨k, rfl⟩; exact NNReal.coe_le_coe.2 (min_le_right _ _)⟩
    obtain ⟨M, hMt, hMle⟩ : ∃ M : ℝ, Tendsto m atTop (𝓝 M) ∧ ∀ k, m k ≤ M :=
      ⟨_, tendsto_atTop_ciSup hmm hbdd, fun k => le_ciSup hbdd k⟩
    obtain ⟨n, hn⟩ := (hMt.eventually (lt_mem_nhds (show M - δ < M by linarith))).exists
    obtain ⟨k, hk⟩ := mem_iInter.1 hω n
    have hle := hMle k
    change δ < m k - m n at hk
    linarith
  have h := tendsto_measure_iInter_atTop (μ := P) (fun n => (hm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  rwa [hempty, measure_empty] at h

/-- The oscillation events: after the cap `c n`, before `K` and before the cap `c k`, the noise moves by more than
`ε` from its value at `c n`. -/
def oscSet (N : ℝ≥0 → Ω → ℝ) (c : ℕ → Ω → ℝ≥0) (K : ℝ≥0) (ε : ℝ) (n k : ℕ) : Set Ω :=
  {ω | ∃ t : ℝ≥0, t ≤ K ∧ c n ω ≤ t ∧ t ≤ c k ω ∧ ε < |N t ω - N (c n ω) ω|}

theorem oscSet_mono (hmono : ∀ ω, Monotone fun n => c n ω) (K : ℝ≥0) (ε : ℝ) (n : ℕ) :
    Monotone (oscSet N c K ε n) := fun _ _ hkk' ω ⟨t, htK, hnt, htk, he⟩ =>
  ⟨t, htK, hnt, htk.trans (hmono ω hkk'), he⟩

variable [IsProbabilityMeasure P] {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀} {β : ℝ≥0 → Ω₀ → ℝ}

/-- **One cap**: the oscillation event before the cap `c k` with a small gap has probability at most the Wiener
probability of the rational modulus event. -/
theorem measure_oscSet_diff_le (hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0))
    (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω)))
    (hN0 : ∀ ω, N 0 ω = 0) (hbm : ∀ n, IsStoppedBM P 𝓗 N (c n))
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0)
    (K : ℝ≥0) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) (n k : ℕ) :
    P (oscSet N c K ε n k \ gapSet c K δ n) ≤ Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) := by
  -- the Brownian motion `B'ₖ` of `isFilteredBrownianReal_capNoise` for the single cap `c k`
  obtain ⟨hB, hBc, hBeq⟩ := isFilteredBrownianReal_capNoise (P := P) (𝓗 := 𝓗) (N := stoppedAt N (c k))
    (S := fun _ => c k) (fun _ a => by rw [stopExp_stoppedAt]; exact hbm k a) (fun _ => hc k)
    (continuous_stoppedAt (hNc k)) (fun ω => by simp only [stoppedAt, zero_min, hN0]) hβ hβc hβ0
  set B' := WholeField.complNoise (fun u ω => stoppedAt N (c k) (WholeField.annClock (capMax fun _ => c k) u ω) ω)
    (WholeField.annClock (capMax fun _ => c k)) β with hB'
  have hBm : ∀ s, Measurable (B' s) := fun s =>
    (hB.2.1 s).mono ((WholeField.prodFiltration 𝓗 𝓦).le s) le_rfl
  have hval : ∀ (p : Ω × Ω₀) (u : ℝ≥0), u ≤ c k p.1 → B' u p = N u p.1 := fun p u hu => by
    rw [hBeq p u 0 hu]
    simp only [stoppedAt, min_eq_left hu]
  have hsub : (oscSet N c K ε n k \ gapSet c K δ n) ×ˢ (univ : Set Ω₀) ⊆
      {p | (fun s => B' s p) ∈ modSet (δ + δ) ε (K + 1)} := by
    rintro ⟨ω, w⟩ ⟨⟨⟨t, htK, hnt, htk, he⟩, hgap⟩, -⟩
    simp only [mem_ofPred_eq]
    have hgap' : ¬ δ < ((min (c k ω) K : ℝ≥0) : ℝ) - ((min (c n ω) K : ℝ≥0) : ℝ) := fun h => hgap ⟨k, h⟩
    have hnK : c n ω ≤ K := hnt.trans htK
    have htmin : t ≤ min (c k ω) K := le_min htk htK
    have hts : |(t : ℝ) - c n ω| ≤ δ := by
      rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hnt))]
      rw [min_eq_left hnK] at hgap'
      have : (t : ℝ) ≤ ((min (c k ω) K : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 htmin
      linarith
    refine mem_modSet_of_continuous (hBc (ω, w)) hδ hts htK hnK ?_
    rw [hval (ω, w) t htk, hval (ω, w) (c n ω) (hnt.trans htk)]
    exact he
  calc P (oscSet N c K ε n k \ gapSet c K δ n)
      = (P.prod P₀) ((oscSet N c K ε n k \ gapSet c K δ n) ×ˢ (univ : Set Ω₀)) := by
        rw [Measure.prod_prod, measure_univ, mul_one]
    _ ≤ (P.prod P₀) {p | (fun s => B' s p) ∈ modSet (δ + δ) ε (K + 1)} := measure_mono hsub
    _ = Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) :=
        measure_path_mem_modSet hB.1.toIsPreBrownianReal hBm _ _ _

/-- **No oscillation after the caps, almost surely** (fixed horizon `K` and size `ε`): the event that after every cap
`c n` the noise moves by more than `ε` before `K` and before some later cap is null. -/
theorem measure_iInter_iUnion_oscSet (hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0))
    (hmono : ∀ ω, Monotone fun n => c n ω) (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω)))
    (hN0 : ∀ ω, N 0 ω = 0) (hbm : ∀ n, IsStoppedBM P 𝓗 N (c n))
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0)
    (K : ℝ≥0) {ε : ℝ} (hε : 0 < ε) : P (⋂ n, ⋃ k, oscSet N c K ε n k) = 0 := by
  have hcm : ∀ n, Measurable (c n) := fun n => measurable_of_isStoppingTime (hc n)
  -- for every gap size `δ`, the probability is at most the Wiener probability of the modulus event
  have hδ : ∀ δ : ℝ, 0 < δ →
      P (⋂ n, ⋃ k, oscSet N c K ε n k) ≤ Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) := by
    intro δ hδ
    have hn : ∀ n, P (⋂ n, ⋃ k, oscSet N c K ε n k) ≤
        Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) + P (gapSet c K δ n) := by
      intro n
      have hU : P (⋃ k, (oscSet N c K ε n k \ gapSet c K δ n)) ≤
          Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) := by
        rw [Monotone.measure_iUnion fun k k' hkk' => sdiff_subset_sdiff_left (oscSet_mono hmono K ε n hkk')]
        exact iSup_le fun k => measure_oscSet_diff_le hc hNc hN0 hbm hβ hβc hβ0 K ε hδ n k
      calc P (⋂ n, ⋃ k, oscSet N c K ε n k) ≤ P (⋃ k, oscSet N c K ε n k) := measure_mono (iInter_subset _ n)
        _ ≤ P ((⋃ k, (oscSet N c K ε n k \ gapSet c K δ n)) ∪ gapSet c K δ n) := by
          refine measure_mono fun ω hω => ?_
          by_cases hg : ω ∈ gapSet c K δ n
          · exact Or.inr hg
          · obtain ⟨k, hk⟩ := mem_iUnion.1 hω
            exact Or.inl (mem_iUnion.2 ⟨k, hk, hg⟩)
        _ ≤ P (⋃ k, (oscSet N c K ε n k \ gapSet c K δ n)) + P (gapSet c K δ n) := measure_union_le _ _
        _ ≤ _ := add_le_add_left hU _
    have ht : Tendsto (fun n => Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) + P (gapSet c K δ n)) atTop
        (𝓝 (Sec2.Restart.wienerPath (modSet (δ + δ) ε (K + 1)) + 0)) :=
      tendsto_const_nhds.add (tendsto_measure_gapSet hmono hcm K hδ)
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hn
  -- and the Wiener probability tends to zero
  have ht := tendsto_wienerPath_modSet hβ hβc ε hε (K + 1)
  have hle : ∀ j : ℕ, P (⋂ n, ⋃ k, oscSet N c K ε n k) ≤
      Sec2.Restart.wienerPath (modSet (1 / ((j : ℝ) + 1)) ε (K + 1)) := by
    intro j
    have hpos : (0 : ℝ) < 1 / (2 * ((j : ℝ) + 1)) := by positivity
    refine (hδ _ hpos).trans (measure_mono (modSet_mono (le_of_eq ?_)))
    field_simp
    ring
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

/-- **A noise that is continuous before, and a Brownian motion stopped at, each of increasing caps has, almost
surely, no oscillation after the caps**: for every horizon `K` and every `j` there is a cap `c n` after which (before
`K` and before any later cap) the noise stays within `1/(j+1)` of its value at `c n`. The independent Brownian motion
`β` (continuous, from `0`) is an auxiliary input used to complete the stopped noise to a Brownian motion. -/
theorem ae_cauchy_of_isStoppedBM (hc : ∀ n, IsStoppingTime 𝓗 fun ω => (c n ω : WithTop ℝ≥0))
    (hmono : ∀ ω, Monotone fun n => c n ω) (hNc : ∀ n ω, ContinuousOn (N · ω) (Icc 0 (c n ω)))
    (hN0 : ∀ ω, N 0 ω = 0) (hbm : ∀ n, IsStoppedBM P 𝓗 N (c n))
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0) :
    ∀ᵐ ω ∂P, ∀ K j : ℕ, ∃ n, ∀ k (t : ℝ≥0), t ≤ K → c n ω ≤ t → t ≤ c k ω →
      |N t ω - N (c n ω) ω| ≤ 1 / ((j : ℝ) + 1) := by
  rw [ae_all_iff]
  intro K
  rw [ae_all_iff]
  intro j
  have h0 := measure_iInter_iUnion_oscSet hc hmono hNc hN0 hbm hβ hβc hβ0 (K : ℝ≥0)
    (ε := 1 / ((j : ℝ) + 1)) (by positivity)
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with ω hω
  simp only [mem_iInter, mem_iUnion, not_forall, not_exists] at hω
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, fun k t htK hnt htk => ?_⟩
  by_contra hlt
  exact hn k ⟨t, htK, hnt, htk, lt_of_not_ge hlt⟩

end Cauchy

/-! ### The continuous extension through the supremum of the caps (deterministic) -/

section Extension

/-- **Uniformly close continuous functions converge to a continuous limit**: if after some index every `F n` stays
within `1/(j+1)` of `F n₀` on `[0, K]`, the pointwise limits exist and form a continuous function. -/
theorem continuous_limUnder_of_close {F : ℕ → ℝ≥0 → ℝ} (hFc : ∀ n, Continuous (F n))
    (hclose : ∀ (K j : ℕ), ∃ n₀, ∀ n, n₀ ≤ n → ∀ t : ℝ≥0, t ≤ K → |F n t - F n₀ t| ≤ 1 / ((j : ℝ) + 1)) :
    (∀ t, Tendsto (fun n => F n t) atTop (𝓝 (limUnder atTop fun n => F n t))) ∧
      Continuous fun t => limUnder atTop fun n => F n t := by
  have hUC : ∀ K : ℕ, UniformCauchySeqOn F atTop (Icc 0 (K : ℝ≥0)) := by
    intro K
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨n₀, hn₀⟩ := hclose K j
    refine ⟨n₀, fun m hm n hn t ht => ?_⟩
    rw [Real.dist_eq]
    have h1 := hn₀ m hm t ht.2
    have h2 := hn₀ n hn t ht.2
    calc |F m t - F n t| ≤ |F m t - F n₀ t| + |F n t - F n₀ t| := by
          rw [abs_sub_comm (F n t)]; exact abs_sub_le _ _ _
      _ < ε := by linarith
  have hg : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (limUnder atTop fun n => F n t)) := by
    intro t
    obtain ⟨K, hK⟩ := exists_nat_ge t
    exact ((hUC K).cauchySeq (show t ∈ Icc 0 (K : ℝ≥0) from ⟨bot_le, hK⟩)).tendsto_limUnder
  refine ⟨hg, continuous_iff_continuousAt.2 fun t => ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_gt t
  have hcon : ContinuousOn (fun t => limUnder atTop fun n => F n t) (Icc 0 (K : ℝ≥0)) :=
    ((hUC K).tendstoUniformlyOn_of_tendsto fun t _ => hg t).continuousOn
      (Frequently.of_forall fun n => (hFc n).continuousOn)
  have hmem : Icc 0 (K : ℝ≥0) ∈ 𝓝 t := by
    have e : Icc 0 (K : ℝ≥0) = Iic (K : ℝ≥0) := by
      ext x; simp only [mem_Icc, mem_Iic, zero_le, true_and]
    rw [e]
    exact Iic_mem_nhds hK
  exact hcon.continuousAt hmem

/-- The stopped functions `t ↦ f (t ∧ c n)` are uniformly close after a good cap. -/
theorem close_of_cauchy {f : ℝ≥0 → ℝ} {c : ℕ → ℝ≥0} (hmono : Monotone c)
    (hcau : ∀ K j : ℕ, ∃ n, ∀ k (t : ℝ≥0), t ≤ K → c n ≤ t → t ≤ c k → |f t - f (c n)| ≤ 1 / ((j : ℝ) + 1)) :
    ∀ (K j : ℕ), ∃ n₀, ∀ n, n₀ ≤ n → ∀ t : ℝ≥0, t ≤ K →
      |f (min t (c n)) - f (min t (c n₀))| ≤ 1 / ((j : ℝ) + 1) := by
  intro K j
  obtain ⟨n₀, hn₀⟩ := hcau K j
  refine ⟨n₀, fun n hn t htK => ?_⟩
  rcases le_or_gt t (c n₀) with h | h
  · simp only [min_eq_left h, min_eq_left (h.trans (hmono hn)), sub_self, abs_zero]
    positivity
  · simp only [min_eq_right h.le]
    exact hn₀ n (min t (c n)) ((min_le_left _ _).trans htK) (le_min h.le (hmono hn)) (min_le_right _ _)

/-- **A function continuous before each of increasing caps, with no oscillation after the caps, extends to a
continuous function on `ℝ≥0`** agreeing with it before every cap: the uniform limit of the stopped functions
`t ↦ f (t ∧ c n)` on every `[0, K]`. -/
theorem exists_continuous_extension {f : ℝ≥0 → ℝ} {c : ℕ → ℝ≥0} (hmono : Monotone c)
    (hc : ∀ n, ContinuousOn f (Icc 0 (c n)))
    (hcau : ∀ K j : ℕ, ∃ n, ∀ k (t : ℝ≥0), t ≤ K → c n ≤ t → t ≤ c k → |f t - f (c n)| ≤ 1 / ((j : ℝ) + 1)) :
    ∃ g : ℝ≥0 → ℝ, Continuous g ∧ ∀ n t, t ≤ c n → g t = f t := by
  have hFc : ∀ n, Continuous fun t => f (min t (c n)) := fun n =>
    (hc n).comp_continuous (continuous_id.min continuous_const) fun _ => ⟨bot_le, min_le_right _ _⟩
  obtain ⟨hg, hgc⟩ := continuous_limUnder_of_close hFc (close_of_cauchy hmono hcau)
  refine ⟨_, hgc, fun n t ht => ?_⟩
  have hev : ∀ᶠ m in atTop, f (min t (c m)) = f t := by
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [min_eq_left (ht.trans (hmono hm))]
  exact tendsto_nhds_unique (hg t) (tendsto_const_nhds.congr' (EventuallyEq.symm hev))

end Extension

end InteractingSLE.ZhanGT4.A1RectLaw
