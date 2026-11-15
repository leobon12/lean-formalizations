/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Repulsion

/-!
# The localized repulsion criterion up to a stopping time

Packet PROVE-GB7A2. The hitting estimate (RP3) of Aux. lemma 5 (`Sec4.Repulsion.measure_hit_le`, PROVE-SEC4-A2)
when the semimartingale decomposition and the drift inequality (RP1) hold only up to a stopping time `ρ`: under the
Cameron–Martin (Girsanov) measure of the comparison of Aux. lemma 62, the reference drift of the gap is known only
before the separation time of the marks. The proof is the same Itô argument with the localizer also killed at `ρ`.

* `stopLoc`: the localizer of `Sec4.Repulsion`, intersected with `{u ≤ ρ}`;
* `measure_hit_le_stop`: if `ℓ ≤ Y_s < a` on `A ∈ 𝓕_s`, the probability that `Y` falls below `ε'` before `ρ`
  (staying below `a`, with the dominating process below `N`) is at most `F(ℓ)/F(ε)` for `0 < ε' < ε < ℓ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology ENNReal

namespace InteractingSLE.GB7a

open LocalTime Sec4.Repulsion

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The localizer of the repulsion criterion, killed at the stopping time `ρ`. -/
def stopLoc (Y ψ : ℝ≥0 → Ω → ℝ) (A : Set Ω) (ρ : Ω → ℝ≥0) (s : ℝ≥0) (ε a N : ℝ) (u : ℝ≥0) : Set Ω :=
  if u < s then univ else
    A ∩ {ω | u ≤ ρ ω} ∩ ⋂ (q : ℚ) (_ : (s : ℝ) ≤ q ∧ (q : ℝ) ≤ u),
      {ω | ε < Y (q : ℝ).toNNReal ω ∧ Y (q : ℝ).toNNReal ω < a ∧ ψ (q : ℝ).toNNReal ω - ψ s ω ≤ N}

variable {Y ψ : ℝ≥0 → Ω → ℝ} {A : Set Ω} {ρ : Ω → ℝ≥0} {s t : ℝ≥0} {ε a N : ℝ}

lemma stopLoc_antitone : Antitone (stopLoc Y ψ A ρ s ε a N) := by
  intro u v huv ω hω
  unfold stopLoc at hω ⊢
  by_cases hu : u < s
  · simp [hu]
  · have hv : ¬ v < s := fun h => hu (lt_of_le_of_lt huv h)
    simp only [hv, hu, ite_false, mem_inter_iff, mem_iInter, Set.mem_ofPred_eq] at hω ⊢
    exact ⟨⟨hω.1.1, huv.trans hω.1.2⟩, fun q hq => hω.2 q ⟨hq.1, hq.2.trans (by exact_mod_cast huv)⟩⟩

lemma measurableSet_stopLoc {𝓕 : Filtration ℝ≥0 mΩ} (hY : ∀ u, Measurable[𝓕 u] (Y u))
    (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (hA : MeasurableSet[𝓕 s] A)
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] (stopLoc Y ψ A ρ s ε a N u) := by
  unfold stopLoc
  split_ifs with hu
  · exact MeasurableSet.univ
  · have hsu : s ≤ u := not_lt.1 hu
    have hψs : Measurable[𝓕 u] (ψ s) := (hψ s).mono (𝓕.mono hsu) le_rfl
    have hρu : MeasurableSet[𝓕 u] {ω | u ≤ ρ ω} := by
      have := (hρ.measurableSet_lt u).compl
      convert this using 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
      exact WithTop.coe_le_coe.symm
    refine ((𝓕.mono hsu _ hA).inter hρu).inter (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_)
    have hq' : (q : ℝ).toNNReal ≤ u := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hq.2
    have hYq : Measurable[𝓕 u] (Y (q : ℝ).toNNReal) := (hY _).mono (𝓕.mono hq') le_rfl
    have hψq : Measurable[𝓕 u] (ψ (q : ℝ).toNNReal) := (hψ _).mono (𝓕.mono hq') le_rfl
    exact (measurableSet_lt measurable_const hYq).inter ((measurableSet_lt hYq measurable_const).inter
      (measurableSet_le (hψq.sub hψs) measurable_const))

section Lifetime

variable {ω : Ω}

lemma lifetime_stop_eq_of_not_mem (hω : ω ∉ A) : lifetime (stopLoc Y ψ A ρ s ε a N) s t ω = s := by
  refine lifetimeOf_eq_of_not (fun u v huv h => stopLoc_antitone huv h) ?_
  simp only [stopLoc, lt_irrefl, ite_false, mem_inter_iff]
  exact fun h => hω h.1.1

lemma lifetime_stop_le (hsρ : s ≤ ρ ω) : lifetime (stopLoc Y ψ A ρ s ε a N) s t ω ≤ ρ ω := by
  refine csSup_le (insert_nonempty _ _) ?_
  rintro u (rfl | ⟨-, hu⟩)
  · exact hsρ
  · by_cases hus : u < s
    · exact hus.le.trans hsρ
    · simp only [stopLoc, hus, ite_false, mem_inter_iff, Set.mem_ofPred_eq] at hu
      exact hu.1.2

/-- At a rational time of `[s, ρ_L)` the localized conditions hold. -/
lemma cond_of_lt_lifetime_stop {q : ℚ} (hsq : (s : ℝ) ≤ q)
    (hq : (q : ℝ) < lifetime (stopLoc Y ψ A ρ s ε a N) s t ω) :
    ω ∈ A ∧ ε < Y (q : ℝ).toNNReal ω ∧ Y (q : ℝ).toNNReal ω < a ∧
      ψ (q : ℝ).toNNReal ω - ψ s ω ≤ N := by
  have hq0 : (0 : ℝ) ≤ q := s.2.trans hsq
  have hsq' : s ≤ (q : ℝ).toNNReal := by rw [Real.le_toNNReal_iff_coe_le hq0]; exact hsq
  have hlt : (q : ℝ).toNNReal < lifetime (stopLoc Y ψ A ρ s ε a N) s t ω := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq
  have hmem := of_lt_lifetimeOf (A := fun u => ω ∈ stopLoc Y ψ A ρ s ε a N u)
    (fun u v huv h => stopLoc_antitone huv h) hsq' hlt
  simp only [stopLoc, not_lt.2 hsq', ite_false, mem_inter_iff, mem_iInter, Set.mem_ofPred_eq] at hmem
  refine ⟨hmem.1.1, hmem.2 q ⟨hsq, ?_⟩⟩
  rw [Real.coe_toNNReal _ hq0]

/-- On `[s, ρ_L]` the closed localized conditions hold. -/
lemma bounds_on_lifetime_stop (hsρ : s ≤ ρ ω) (hAs : ε < Y s ω ∧ Y s ω < a) (hN : 0 ≤ N)
    (hY : ContinuousOn (Y · ω) (Icc s (ρ ω))) (hψ : ContinuousOn (ψ · ω) (Icc s (ρ ω))) :
    ∀ u ∈ Icc s (lifetime (stopLoc Y ψ A ρ s ε a N) s t ω),
      ε ≤ Y u ω ∧ Y u ω ≤ a ∧ ψ u ω - ψ s ω ≤ N := by
  set ρL := lifetime (stopLoc Y ψ A ρ s ε a N) s t ω
  have hsub : Icc s ρL ⊆ Icc s (ρ ω) := Icc_subset_Icc le_rfl (lifetime_stop_le hsρ)
  intro u hu
  refine ⟨?_, ?_, ?_⟩
  · have := le_of_le_rat (g := fun u => -Y u ω) (N := -ε) (hY.mono hsub).neg (by linarith [hAs.1])
      (fun q hsq hq => by
        have := (cond_of_lt_lifetime_stop (t := t) hsq hq).2.1
        linarith) u hu
    linarith
  · exact le_of_le_rat (hY.mono hsub) hAs.2.le
      (fun q hsq hq => (cond_of_lt_lifetime_stop (t := t) hsq hq).2.2.1.le) u hu
  · exact le_of_le_rat (g := fun u => ψ u ω - ψ s ω) ((hψ.mono hsub).sub continuousOn_const)
      (by simp [hN]) (fun q hsq hq => (cond_of_lt_lifetime_stop (t := t) hsq hq).2.2.2) u hu

/-- **The hitting configuration** before `ρ`: if `Y` falls below `ε' < ε` at a time `u ≤ ρ ≤ t` while staying
below `a`, and `ψ − ψ_s < N` on `[s, ρ]`, then `Y ≤ ε` at the lifetime of the localizer. -/
lemma le_of_hit_stop (hsρ : s ≤ ρ ω) (hρt : ρ ω ≤ t) {ε' : ℝ} (hε' : ε' < ε) (hA : ω ∈ A)
    (hAs : ε < Y s ω ∧ Y s ω < a) (hY : ContinuousOn (Y · ω) (Icc s (ρ ω)))
    (hψ : ContinuousOn (ψ · ω) (Icc s (ρ ω))) (hψN : ∀ r ∈ Icc s (ρ ω), ψ r ω - ψ s ω < N) {u : ℝ≥0}
    (hu : u ∈ Icc s (ρ ω)) (hYu : Y u ω ≤ ε') (hlt : ∀ r ∈ Icc s u, Y r ω < a) :
    Y (lifetime (stopLoc Y ψ A ρ s ε a N) s t ω) ω ≤ ε := by
  set ρL := lifetime (stopLoc Y ψ A ρ s ε a N) s t ω with hρdef
  have hN : 0 ≤ N := by have := hψN s ⟨le_rfl, hsρ⟩; simp only [sub_self] at this; exact this.le
  have hb := bounds_on_lifetime_stop (A := A) (t := t) hsρ hAs hN hY hψ
  have hsρL : s ≤ ρL := le_lifetimeOf _ _ _
  have hρLρ : ρL ≤ ρ ω := lifetime_stop_le hsρ
  by_contra hcon
  push Not at hcon
  have hρu : ρL < u := by
    by_contra h
    push Not at h
    have := (hb u ⟨hu.1, h⟩).1
    linarith
  have hYa : Y ρL ω < a := hlt ρL ⟨hsρL, hρu.le⟩
  have hρmem : ρL ∈ Icc s (ρ ω) := ⟨hsρL, hρLρ⟩
  have hψρ : ψ ρL ω - ψ s ω < N := hψN ρL hρmem
  have hev : ∀ᶠ r in 𝓝[Icc s (ρ ω)] ρL, ε < Y r ω ∧ Y r ω < a ∧ ψ r ω - ψ s ω < N := by
    refine ((hY ρL hρmem).eventually (lt_mem_nhds hcon)).and
      (((hY ρL hρmem).eventually (gt_mem_nhds hYa)).and ?_)
    exact ((hψ ρL hρmem).sub continuousWithinAt_const).eventually (gt_mem_nhds hψρ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set v : ℝ≥0 := min (ρL + (δ / 2).toNNReal) u with hv
  have hδ2 : (0 : ℝ) < ((δ / 2).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]; positivity
  have hρv : ρL < v := by
    refine lt_min ?_ hρu
    have : (0 : ℝ≥0) < (δ / 2).toNNReal := by exact_mod_cast hδ2
    exact lt_add_of_pos_right _ this
  have hvu : v ≤ u := min_le_right _ _
  have hvρ : (v : ℝ) ≤ ρL + δ / 2 := by
    have : v ≤ ρL + (δ / 2).toNNReal := min_le_left _ _
    have h' : ((ρL + (δ / 2).toNNReal : ℝ≥0) : ℝ) = ρL + δ / 2 := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity)]
    rw [← h']; exact_mod_cast this
  have halive : ω ∈ stopLoc Y ψ A ρ s ε a N v := by
    have hvs : ¬ v < s := not_lt.2 (hsρL.trans hρv.le)
    simp only [stopLoc, hvs, ite_false, mem_inter_iff, mem_iInter, Set.mem_ofPred_eq]
    refine ⟨⟨hA, hvu.trans hu.2⟩, fun q hq => ?_⟩
    by_cases hqρ : (q : ℝ) < ρL
    · exact (cond_of_lt_lifetime_stop (t := t) hq.1 hqρ).2
    · push Not at hqρ
      have hq0 : (0 : ℝ) ≤ q := s.2.trans hq.1
      have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
      have hmem : (q : ℝ).toNNReal ∈ Metric.ball ρL δ ∩ Icc s (ρ ω) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [Metric.mem_ball, NNReal.dist_eq, hqc, abs_sub_lt_iff]
          constructor <;> linarith [hq.2]
        · rw [← NNReal.coe_le_coe, hqc]; exact hq.1
        · rw [← NNReal.coe_le_coe, hqc]
          exact hq.2.trans (by exact_mod_cast hvu.trans hu.2)
      have h := hball hmem
      exact ⟨h.1, h.2.1, h.2.2.le⟩
  have := le_lifetimeOf_of (A := fun u => ω ∈ stopLoc Y ψ A ρ s ε a N u) (s := s)
    (hvu.trans (hu.2.trans hρt)) halive
  exact absurd this (not_le.2 hρv)

/-- The clamped process satisfies the hypotheses of Itô's formula on `[s, ρ_L]`. -/
lemma isTanakaPath_clampProc_stop {σ C : ℝ} {B β : ℝ≥0 → Ω → ℝ} (hsρ : s ≤ ρ ω) (hε : 0 < ε)
    (hεa : ε ≤ a) (hN : 0 ≤ N) (hAs : ω ∈ A → ε < Y s ω ∧ Y s ω < a)
    (hP : ω ∈ A → IsRepulsionPath σ a C s (ρ ω) (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    IsTanakaPath σ 0 (max a N) s (lifetime (stopLoc Y ψ A ρ s ε a N) s t ω)
      (clampProc ε a Y · ω) (B · ω) (fun _ => 0) (β · ω) := by
  have ha : 0 ≤ a := hε.le.trans hεa
  have habs : ∀ u, |clampProc ε a Y u ω| ≤ max a N := fun u => by
    have h := clampProc_mem (Y := Y) hεa u ω
    rw [abs_of_nonneg (hε.le.trans h.1)]; exact h.2.trans (le_max_left _ _)
  by_cases hA : ω ∈ A
  swap
  · rw [lifetime_stop_eq_of_not_mem hA]
    exact isTanakaPath_singleton (habs s) (ha.trans (le_max_left _ _))
  obtain ⟨hYc, hBc, hψc, hdec⟩ := hP hA
  set ρL := lifetime (stopLoc Y ψ A ρ s ε a N) s t ω
  have hρLρ : ρL ≤ ρ ω := lifetime_stop_le hsρ
  have hsρL : s ≤ ρL := le_lifetimeOf _ _ _
  have hsub : Icc s ρL ⊆ Icc s (ρ ω) := Icc_subset_Icc le_rfl hρLρ
  have hb := bounds_on_lifetime_stop (A := A) (t := t) hsρ (hAs hA) hN hYc hψc
  have hcl : ∀ u ∈ Icc s ρL, clampProc ε a Y u ω = Y u ω := fun u hu =>
    clampProc_eq (hb u hu).1 (hb u hu).2.1
  have hpos : ∀ u ∈ Icc s ρL, ∀ r ∈ Icc s u, 0 < Y r ω ∧ Y r ω ≤ a := fun u hu r hr =>
    have hr' : r ∈ Icc s ρL := ⟨hr.1, hr.2.trans hu.2⟩
    ⟨lt_of_lt_of_le hε (hb r hr').1, (hb r hr').2.1⟩
  have hdρ := hdec ρL ⟨hsρL, hρLρ⟩ (hpos ρL ⟨hsρL, le_rfl⟩)
  refine ⟨?_, hBc.mono hsub, continuousOn_const, hdρ.1, ?_, monotoneOn_const, fun _ _ _ _ _ _ => rfl,
    fun u _ => habs u, ?_, ?_⟩
  · show ContinuousOn (fun x => max ε (min a (Y x ω))) (Icc s ρL)
    exact ((continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn hYc).mono hsub
  · intro u hu
    have h2 := (hdec u (hsub hu) (hpos u hu)).2.1
    beta_reduce at h2 ⊢
    rw [hcl u hu, hcl s ⟨le_rfl, hsρL⟩, h2]
    ring
  · exact hdρ.2.2.1.trans ((hb ρL ⟨hsρL, le_rfl⟩).2.2.trans (le_max_right _ _))
  · simp only [sub_self]; exact ha.trans (le_max_left _ _)

end Lifetime

section Ito

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B β : ℝ≥0 → Ω → ℝ}
  {σ C : ℝ}

/-- The pointwise generator inequality on `[s, ρ_L]`. -/
lemma integral_generator_nonpos_stop {ω : Ω} (hσ : σ ≠ 0) (hsρ : s ≤ ρ ω) (hε : 0 < ε) (hN : 0 ≤ N)
    (hAs : ω ∈ A → ε < Y s ω ∧ Y s ω < a)
    (hP : ω ∈ A → IsRepulsionPath σ a C s (ρ ω) (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    (∫ r in (s : ℝ)..(lifetime (stopLoc Y ψ A ρ s ε a N) s t ω),
        repulsionF1 (2 * C / σ ^ 2) ε (clampProc ε a Y r.toNNReal ω) * β r.toNNReal ω) +
      σ ^ 2 / 2 * ∫ r in (s : ℝ)..(lifetime (stopLoc Y ψ A ρ s ε a N) s t ω),
        repulsionF2 (2 * C / σ ^ 2) ε (clampProc ε a Y r.toNNReal ω) ≤ 0 := by
  set η := 2 * C / σ ^ 2
  by_cases hA : ω ∈ A
  swap
  · rw [lifetime_stop_eq_of_not_mem hA]; simp
  obtain ⟨hYc, -, hψc, hdec⟩ := hP hA
  set ρL := lifetime (stopLoc Y ψ A ρ s ε a N) s t ω
  have hρLρ : ρL ≤ ρ ω := lifetime_stop_le hsρ
  have hsρL : s ≤ ρL := le_lifetimeOf _ _ _
  have hsρ' : (s : ℝ) ≤ ρL := by exact_mod_cast hsρL
  have hsub : Icc s ρL ⊆ Icc s (ρ ω) := Icc_subset_Icc le_rfl hρLρ
  have hb := bounds_on_lifetime_stop (A := A) (t := t) hsρ (hAs hA) hN hYc hψc
  have hpos : ∀ r ∈ Icc s ρL, 0 < Y r ω ∧ Y r ω ≤ a := fun r hr =>
    ⟨lt_of_lt_of_le hε (hb r hr).1, (hb r hr).2.1⟩
  have hdρ := hdec ρL ⟨hsρL, hρLρ⟩ (fun r hr => hpos r hr)
  have hXc : ContinuousOn (fun r : ℝ => clampProc ε a Y r.toNNReal ω) (Icc (s : ℝ) ρL) :=
    continuousOn_comp_toNNReal (G := fun u => clampProc ε a Y u ω)
      (((continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn hYc).mono hsub)
  have hI1 : IntervalIntegrable (fun r : ℝ => repulsionF1 η ε (clampProc ε a Y r.toNNReal ω) *
      β r.toNNReal ω) volume s ρL := by
    refine hdρ.1.continuousOn_mul ?_
    rw [uIcc_of_le hsρ']
    exact (continuous_repulsionF1 η hε).comp_continuousOn hXc
  have hI2 : IntervalIntegrable (fun r : ℝ => repulsionF2 η ε (clampProc ε a Y r.toNNReal ω))
      volume s ρL := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hsρ']
    exact (continuous_repulsionF2 η hε).comp_continuousOn hXc
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1 (hI2.const_mul _)]
  have h0 : (∫ r in (s : ℝ)..ρL, (0 : ℝ)) = 0 := intervalIntegral.integral_zero
  rw [← h0]
  refine intervalIntegral.integral_mono_ae_restrict hsρ' (hI1.add (hI2.const_mul _))
    intervalIntegrable_const ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [hdρ.2.2.2] with r hr hrI
  have hrI' := Sec4.Repulsion.toNNReal_mem_Icc_of_mem hrI
  have hy := hpos _ hrI'
  have hcl : clampProc ε a Y r.toNNReal ω = Y r.toNNReal ω :=
    clampProc_eq (hb _ hrI').1 (hb _ hrI').2.1
  have hβ := hr hrI
  simp only [hcl, repulsionF1_eq η hε (hb _ hrI').1, repulsionF2_eq η (hb _ hrI').1]
  set y := Y r.toNNReal ω
  have hκ : 0 < σ ^ 2 := by positivity
  have hgen := repulsionDeriv_generator (C := C) hκ hy.1
  have hneg := repulsionDeriv_neg η hy.1
  have : repulsionDeriv η y * β r.toNNReal ω ≤ repulsionDeriv η y * (σ ^ 2 / (2 * y) - C) :=
    mul_le_mul_of_nonpos_left hβ hneg.le
  linarith

/-- **The supermartingale estimate** up to the stopping time `ρ`. -/
theorem integral_repulsionF_sub_le_stop (hB : IsFilteredPreBrownian B 𝓕 P) (hσ : σ ≠ 0)
    (hε : 0 < ε) (hεa : ε ≤ a) (hN : 0 ≤ N) (hst : s ≤ t) (hY : ∀ u, Measurable[𝓕 u] (Y u))
    (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (hA : MeasurableSet[𝓕 s] A)
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) (hsρ : ∀ ω, s ≤ ρ ω)
    (hAs : ∀ ω ∈ A, ε < Y s ω ∧ Y s ω < a)
    (hpath : ∀ᵐ ω ∂P, ω ∈ A → IsRepulsionPath σ a C s (ρ ω) (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    ∫ ω, (repulsionF (2 * C / σ ^ 2) ε a
        (clampProc ε a Y (lifetime (stopLoc Y ψ A ρ s ε a N) s t ω) ω) -
      repulsionF (2 * C / σ ^ 2) ε a (clampProc ε a Y s ω)) ∂P ≤ 0 := by
  set η := 2 * C / σ ^ 2
  set 𝒢 := stopLoc Y ψ A ρ s ε a N
  have hT : ∀ᵐ ω ∂P, IsTanakaPath σ 0 (max a N) s (lifetime 𝒢 s t ω) (clampProc ε a Y · ω)
      (B · ω) ((fun _ _ => (0 : ℝ)) · ω) (β · ω) := by
    filter_upwards [hpath] with ω hω
    exact isTanakaPath_clampProc_stop (hsρ ω) hε hεa hN (hAs ω) hω
  have hXm : ∀ u, Measurable[𝓕 u] (clampProc ε a Y u) := measurable_clampProc hY
  have h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u) := measurableSet_stopLoc hY hψ hA hρ
  have h𝒢a : Antitone 𝒢 := stopLoc_antitone
  have hf2 := continuous_repulsionF2 η hε
  have hIto := integral_sub_eq_of_isTanakaPath hB hst hXm h𝒢 h𝒢a (hasDerivAt_repulsionF η hε a)
    (hasDerivAt_repulsionF1 η hε) hf2 hT
  rw [hIto]
  have iA := integrable_limitA hB hst hXm h𝒢 h𝒢a (continuous_repulsionF1 η hε) hT
  have h𝒢m : ∀ u, MeasurableSet (𝒢 u) := fun u => 𝓕.le u _ (h𝒢 u)
  have hXm' : ∀ u, Measurable (clampProc ε a Y u) := fun u => (hXm u).mono (𝓕.le u) le_rfl
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf2 (max a N)
  have iT : Integrable (fun ω => ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
      repulsionF2 η ε (clampProc ε a Y r.toNNReal ω)) P := by
    refine integrable_of_ae_tendsto (C := K * ((t : ℝ) - s))
      (measurable_termT h𝒢m hXm' hf2) (fun n => ?_) (ae_tendsto_termT h𝒢a hst hT hf2)
    filter_upwards [hT] with ω hP
    refine (abs_termT_le (a := σ) (c := 0) (B := B) (J := fun _ _ => (0 : ℝ)) (b := β) hst hP hK
      hK0 n).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using sub_nonneg.2 (by exact_mod_cast hst : (s : ℝ) ≤ t)
    · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn)]
  rw [← integral_const_mul, ← integral_add iA (iT.const_mul _)]
  refine integral_nonpos_of_ae ?_
  filter_upwards [hpath] with ω hω
  simp only [zero_mul, add_zero, Pi.zero_apply]
  exact integral_generator_nonpos_stop hσ (hsρ ω) hε hN (hAs ω) hω

/-- **(RP3) up to a stopping time**: if `ℓ ≤ Y_s < a` on `A ∈ 𝓕_s`, the probability that `Y` falls below `ε'`
before `ρ ≤ t` (staying below `a`, with `ψ − ψ_s < N`) is at most `F(ℓ)/F(ε)` for `0 < ε' < ε < ℓ < a`. -/
theorem measure_hit_le_stop (hB : IsFilteredPreBrownian B 𝓕 P) (hσ : σ ≠ 0) (hC : 0 ≤ C) {ℓ ε' : ℝ}
    (hε : 0 < ε) (hε' : ε' < ε) (hεℓ : ε < ℓ) (hℓa : ℓ < a) (hN : 0 ≤ N) (hst : s ≤ t)
    (hY : ∀ u, Measurable[𝓕 u] (Y u)) (hψ : ∀ u, Measurable[𝓕 u] (ψ u))
    (hA : MeasurableSet[𝓕 s] A) (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0))
    (hsρ : ∀ ω, s ≤ ρ ω) (hρt : ∀ ω, ρ ω ≤ t) (hAs : ∀ ω ∈ A, ℓ ≤ Y s ω ∧ Y s ω < a)
    (hpath : ∀ᵐ ω ∂P, ω ∈ A → IsRepulsionPath σ a C s (ρ ω) (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    P {ω | ω ∈ A ∧ (∀ r ∈ Icc s (ρ ω), ψ r ω - ψ s ω < N) ∧
        ∃ u ∈ Icc s (ρ ω), Y u ω ≤ ε' ∧ ∀ r ∈ Icc s u, Y r ω < a} ≤
      ENNReal.ofReal (repulsionInt (2 * C / σ ^ 2) a ℓ / repulsionInt (2 * C / σ ^ 2) a ε) := by
  set η := 2 * C / σ ^ 2
  have hη : 0 ≤ η := div_nonneg (by linarith) (sq_nonneg σ)
  set 𝒢 := stopLoc Y ψ A ρ s ε a N
  set f := repulsionF η ε a
  have hℓ : 0 < ℓ := hε.trans hεℓ
  have hεa : ε ≤ a := (hεℓ.trans hℓa).le
  have hAs' : ∀ ω ∈ A, ε < Y s ω ∧ Y s ω < a := fun ω hω =>
    ⟨hεℓ.trans_le (hAs ω hω).1, (hAs ω hω).2⟩
  have hT : ∀ᵐ ω ∂P, IsTanakaPath σ 0 (max a N) s (lifetime 𝒢 s t ω) (clampProc ε a Y · ω)
      (B · ω) ((fun _ _ => (0 : ℝ)) · ω) (β · ω) := by
    filter_upwards [hpath] with ω hω
    exact isTanakaPath_clampProc_stop (hsρ ω) hε hεa hN (hAs' ω) hω
  have hXm : ∀ u, Measurable[𝓕 u] (clampProc ε a Y u) := measurable_clampProc hY
  have h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u) := measurableSet_stopLoc hY hψ hA hρ
  have hS := integrable_limitS hst hXm h𝒢 stopLoc_antitone (continuous_repulsionF η hε a) hT
  set Fℓ := repulsionInt η a ℓ
  set Fε := repulsionInt η a ε
  set g : Ω → ℝ := fun ω => f (clampProc ε a Y (lifetime 𝒢 s t ω) ω) - f (clampProc ε a Y s ω) + Fℓ
  have hfX : ∀ u ω, f (clampProc ε a Y u ω) = repulsionInt η a (clampProc ε a Y u ω) :=
    fun u ω => repulsionF_eq η hε (clampProc_mem hεa u ω).1 (clampProc_mem hεa u ω).2
  have hfs : ∀ ω ∈ A, f (clampProc ε a Y s ω) ≤ Fℓ := fun ω hω => by
    rw [hfX, clampProc_eq (hAs' ω hω).1.le (hAs ω hω).2.le]
    exact repulsionInt_le hℓ (hAs ω hω).1 (hAs ω hω).2.le
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by
    by_cases hω : ω ∈ A
    · have h1 : 0 ≤ f (clampProc ε a Y (lifetime 𝒢 s t ω) ω) := by
        rw [hfX]
        exact repulsionInt_nonneg (hε.trans_le (clampProc_mem hεa _ ω).1) (clampProc_mem hεa _ ω).2
      have h2 := hfs ω hω
      simp only [g]; linarith
    · simp only [g, 𝒢, lifetime_stop_eq_of_not_mem hω, sub_self, zero_add]
      exact repulsionInt_nonneg hℓ hℓa.le
  have hgi : Integrable g P := hS.add (integrable_const _)
  have hEg : ∫ ω, g ω ∂P ≤ Fℓ := by
    simp only [g]
    rw [integral_add hS (integrable_const _), integral_const, probReal_univ, one_smul]
    linarith [integral_repulsionF_sub_le_stop (N := N) hB hσ hε hεa hN hst hY hψ hA hρ hsρ hAs' hpath]
  have hFε : 0 < Fε := by
    have := log_sub_log_le_repulsionInt (a := a) hη hε hεa
    have : Real.log ε < Real.log a := Real.log_lt_log hε (hεℓ.trans hℓa)
    linarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hg0) hgi Fε
  have hreal : P.real {ω | Fε ≤ g ω} ≤ Fℓ / Fε := by
    rw [le_div_iff₀ hFε, mul_comm]; exact hMarkov.trans hEg
  refine (measure_mono_ae ?_).trans ((ofReal_measureReal (measure_ne_top _ _)).symm.le.trans
    (ENNReal.ofReal_le_ofReal hreal))
  filter_upwards [hpath] with ω hω
  rintro ⟨hA', hψN, u, hu, hYu, hlt⟩
  obtain ⟨hYc, -, hψc, -⟩ := hω hA'
  have hle := le_of_hit_stop (N := N) (hsρ ω) (hρt ω) hε' hA' (hAs' ω hA') hYc hψc hψN hu hYu hlt
  have hcl : clampProc ε a Y (lifetime 𝒢 s t ω) ω = ε := by
    unfold clampProc
    exact max_eq_left ((min_le_right _ _).trans hle)
  have hfε : f ε = Fε := repulsionF_eq η hε le_rfl hεa
  show Fε ≤ g ω
  simp only [g, hcl, hfε]
  linarith [hfs ω hA']

end Ito

end InteractingSLE.GB7a
