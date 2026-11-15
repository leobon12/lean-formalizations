/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.RepulsionTest
import InteractingSLE.Stochastic.LocalTime.ItoExpectation
import InteractingSLE.Stochastic.LocalTime.Stopped

/-!
# The localized repulsion criterion (Aux. lemma 5)

Packet PROVE-SEC4-A2. Specification §2.2, Aux. lemma 5 (`source/spec/p001-048.md`, (RP1)–(RP3)).
Let `B` be a Brownian motion for the filtration `𝓕`, `σ ≠ 0`, `a > 0`, `C ≥ 0`, and let `Y` be an
`𝓕`-adapted process. Suppose that almost surely, on the event `A ∈ 𝓕_s`, the path of `Y` is
continuous on `[s, t]` and, on every interval `[s, u] ⊆ [s, t]` on which `0 < Y ≤ a`,

  `Y_u = Y_s + σ (B_u − B_s) + ∫_s^u β`,   `∫_s^u |β| ≤ ψ_u − ψ_s`,
  `β_r ≥ σ²/(2 Y_r) − C` for almost every `r` (RP1),

for an adapted continuous dominating process `ψ` ("localize the remaining coefficients"). Then
almost surely on `A ∩ {0 < Y_s < a}`, `Y` stays positive on `[s, t]` as long as it stays below `a`
(`ae_pos_of_isRepulsionPath`): it cannot reach zero before leaving through `a` or reaching `t`.

Proof (the source's): Itô's formula in expectation (`LocalTime.integral_sub_eq_of_isTanakaPath`) for
the test function `F(y) = ∫_y^a e^{2Cs/σ²}/s ds` of `RepulsionTest.lean`, whose generator
`σ²/2 F'' + (σ²/(2y) − C) F'` vanishes, stopped when `Y` leaves `(ε, a)` (`repulsionLocalizer`),
gives `E[F(Y_ρ) − F(Y_s)] ≤ 0` (`integral_repulsionF_sub_le`); hence the probability of reaching `ε`
first is at most `F(ℓ)/F(ε)` when `Y_s ≥ ℓ` (RP3, `measure_hit_le`), and `F(ε) → ∞`.
No stochastic integral, change of measure or conditioning on a future event is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology ENNReal

namespace InteractingSLE.Sec4.Repulsion

open LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The pathwise hypotheses of Aux. lemma 5 on `[s, t]`: continuity of `y`, of the Brownian path `b`
and of the dominating path `ψ`, and, on every `[s, u]` on which `0 < y ≤ a`, the decomposition
`y_u = y_s + σ (b_u − b_s) + ∫_s^u β`, the domination `∫_s^u |β| ≤ ψ_u − ψ_s`, and the drift
inequality (RP1) `β ≥ σ²/(2y) − C` almost everywhere. -/
def IsRepulsionPath (σ a C : ℝ) (s t : ℝ≥0) (y b β ψ : ℝ≥0 → ℝ) : Prop :=
  ContinuousOn y (Icc s t) ∧ ContinuousOn b (Icc s t) ∧ ContinuousOn ψ (Icc s t) ∧
  ∀ u ∈ Icc s t, (∀ r ∈ Icc s u, 0 < y r ∧ y r ≤ a) →
    IntervalIntegrable (fun r : ℝ => β r.toNNReal) volume s u ∧
    y u = y s + σ * (b u - b s) + (∫ r in (s : ℝ)..u, β r.toNNReal) ∧
    (∫ r in (s : ℝ)..u, |β r.toNNReal|) ≤ ψ u - ψ s ∧
    ∀ᵐ r ∂volume, r ∈ Icc (s : ℝ) u → σ ^ 2 / (2 * y r.toNNReal) - C ≤ β r.toNNReal

/-- The localizing events: alive at `u ≥ s` on `A` while `ε < Y < a` and `ψ − ψ_s ≤ N` at every
rational time of `[s, u]`. -/
def repulsionLocalizer (Y ψ : ℝ≥0 → Ω → ℝ) (A : Set Ω) (s : ℝ≥0) (ε a N : ℝ) (u : ℝ≥0) :
    Set Ω :=
  if u < s then univ else
    A ∩ ⋂ (q : ℚ) (_ : (s : ℝ) ≤ q ∧ (q : ℝ) ≤ u),
      {ω | ε < Y (q : ℝ).toNNReal ω ∧ Y (q : ℝ).toNNReal ω < a ∧
        ψ (q : ℝ).toNNReal ω - ψ s ω ≤ N}

/-- The process clamped to `[ε, a]`. -/
def clampProc (ε a : ℝ) (Y : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ := max ε (min a (Y u ω))

variable {Y ψ : ℝ≥0 → Ω → ℝ} {A : Set Ω} {s t : ℝ≥0} {ε a N : ℝ}

lemma repulsionLocalizer_antitone : Antitone (repulsionLocalizer Y ψ A s ε a N) := by
  intro u v huv ω hω
  unfold repulsionLocalizer at hω ⊢
  by_cases hu : u < s
  · simp [hu]
  · have hv : ¬ v < s := fun h => hu (lt_of_le_of_lt huv h)
    simp only [hv, hu, ite_false, mem_inter_iff, mem_iInter] at hω ⊢
    exact ⟨hω.1, fun q hq => hω.2 q ⟨hq.1, hq.2.trans (by exact_mod_cast huv)⟩⟩

lemma measurableSet_repulsionLocalizer {𝓕 : Filtration ℝ≥0 mΩ} (hY : ∀ u, Measurable[𝓕 u] (Y u))
    (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (hA : MeasurableSet[𝓕 s] A) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] (repulsionLocalizer Y ψ A s ε a N u) := by
  unfold repulsionLocalizer
  split_ifs with hu
  · exact MeasurableSet.univ
  · have hsu : s ≤ u := not_lt.1 hu
    have hψs : Measurable[𝓕 u] (ψ s) := (hψ s).mono (𝓕.mono hsu) le_rfl
    refine (𝓕.mono hsu _ hA).inter (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_)
    have hq' : (q : ℝ).toNNReal ≤ u := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hq.2
    have hYq : Measurable[𝓕 u] (Y (q : ℝ).toNNReal) := (hY _).mono (𝓕.mono hq') le_rfl
    have hψq : Measurable[𝓕 u] (ψ (q : ℝ).toNNReal) := (hψ _).mono (𝓕.mono hq') le_rfl
    exact (measurableSet_lt measurable_const hYq).inter ((measurableSet_lt hYq measurable_const).inter
      (measurableSet_le (hψq.sub hψs) measurable_const))

lemma measurable_clampProc {𝓕 : Filtration ℝ≥0 mΩ} (hY : ∀ u, Measurable[𝓕 u] (Y u)) (u : ℝ≥0) :
    Measurable[𝓕 u] (clampProc ε a Y u) :=
  measurable_const.max (measurable_const.min (hY u))

lemma clampProc_eq {u : ℝ≥0} {ω : Ω} (h1 : ε ≤ Y u ω) (h2 : Y u ω ≤ a) :
    clampProc ε a Y u ω = Y u ω := by
  unfold clampProc; rw [min_eq_right h2, max_eq_right h1]

lemma clampProc_mem (hεa : ε ≤ a) (u : ℝ≥0) (ω : Ω) : clampProc ε a Y u ω ∈ Icc ε a :=
  ⟨le_max_left _ _, max_le hεa (min_le_left _ _)⟩

/-! ### Pathwise facts about the lifetime -/

section Lifetime

variable {ω : Ω}

lemma lifetime_repulsion_eq_of_not_mem (hω : ω ∉ A) :
    lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω = s := by
  refine lifetimeOf_eq_of_not (fun u v huv h => repulsionLocalizer_antitone huv h) ?_
  simp only [repulsionLocalizer, lt_irrefl, ite_false, mem_inter_iff]
  exact fun h => hω h.1

/-- At a rational time of `[s, ρ)` the localized conditions hold. -/
lemma cond_of_lt_lifetime {q : ℚ} (hsq : (s : ℝ) ≤ q)
    (hq : (q : ℝ) < lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω) :
    ω ∈ A ∧ ε < Y (q : ℝ).toNNReal ω ∧ Y (q : ℝ).toNNReal ω < a ∧
      ψ (q : ℝ).toNNReal ω - ψ s ω ≤ N := by
  have hq0 : (0 : ℝ) ≤ q := s.2.trans hsq
  have hsq' : s ≤ (q : ℝ).toNNReal := by rw [Real.le_toNNReal_iff_coe_le hq0]; exact hsq
  have hlt : (q : ℝ).toNNReal < lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq
  have hmem := of_lt_lifetimeOf (A := fun u => ω ∈ repulsionLocalizer Y ψ A s ε a N u)
    (fun u v huv h => repulsionLocalizer_antitone huv h) hsq' hlt
  simp only [repulsionLocalizer, not_lt.2 hsq', ite_false, mem_inter_iff, mem_iInter] at hmem
  refine ⟨hmem.1, hmem.2 q ⟨hsq, ?_⟩⟩
  rw [Real.coe_toNNReal _ hq0]

/-- On `[s, ρ]` the closed localized conditions hold (for paths continuous on `[s, t]`). -/
lemma bounds_on_lifetime (hst : s ≤ t) (hAs : ε < Y s ω ∧ Y s ω < a) (hN : 0 ≤ N)
    (hY : ContinuousOn (Y · ω) (Icc s t)) (hψ : ContinuousOn (ψ · ω) (Icc s t)) :
    ∀ u ∈ Icc s (lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω),
      ε ≤ Y u ω ∧ Y u ω ≤ a ∧ ψ u ω - ψ s ω ≤ N := by
  set ρ := lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω
  have hρt : ρ ≤ t := lifetimeOf_le hst
  have hsub : Icc s ρ ⊆ Icc s t := Icc_subset_Icc le_rfl hρt
  intro u hu
  refine ⟨?_, ?_, ?_⟩
  · have := le_of_le_rat (g := fun u => -Y u ω) (N := -ε) (hY.mono hsub).neg (by linarith [hAs.1])
      (fun q hsq hq => by
        have := (cond_of_lt_lifetime (t := t) hsq hq).2.1
        linarith) u hu
    linarith
  · exact le_of_le_rat (hY.mono hsub) hAs.2.le
      (fun q hsq hq => (cond_of_lt_lifetime (t := t) hsq hq).2.2.1.le) u hu
  · exact le_of_le_rat (g := fun u => ψ u ω - ψ s ω) ((hψ.mono hsub).sub continuousOn_const)
      (by simp [hN]) (fun q hsq hq => (cond_of_lt_lifetime (t := t) hsq hq).2.2.2) u hu

end Lifetime

/-- **The hitting configuration** (pathwise step of (RP3)): if `Y` reaches `(−∞, 0]` at a time
`u ≤ t` while staying below `a` on `[s, u]`, and `ψ − ψ_s < N` on `[s, t]`, then at the lifetime
`ρ` of the localizer `Y_ρ ≤ ε`. -/
lemma le_of_hit {ω : Ω} (hst : s ≤ t) (hε : 0 < ε) (hA : ω ∈ A)
    (hAs : ε < Y s ω ∧ Y s ω < a) (hY : ContinuousOn (Y · ω) (Icc s t))
    (hψ : ContinuousOn (ψ · ω) (Icc s t)) (hψN : ∀ r ∈ Icc s t, ψ r ω - ψ s ω < N) {u : ℝ≥0}
    (hu : u ∈ Icc s t) (hYu : Y u ω ≤ 0) (hlt : ∀ r ∈ Icc s u, Y r ω < a) :
    Y (lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω) ω ≤ ε := by
  set ρ := lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω with hρdef
  have hN : 0 ≤ N := by have := hψN s ⟨le_rfl, hst⟩; simp only [sub_self] at this; exact this.le
  have hb := bounds_on_lifetime (A := A) (t := t) hst hAs hN hY hψ
  have hsρ : s ≤ ρ := le_lifetimeOf _ _ _
  have hρt : ρ ≤ t := lifetimeOf_le hst
  by_contra hcon
  push Not at hcon
  have hρu : ρ < u := by
    by_contra h
    push Not at h
    have := (hb u ⟨hu.1, h⟩).1
    linarith
  have hYa : Y ρ ω < a := hlt ρ ⟨hsρ, hρu.le⟩
  have hψρ : ψ ρ ω - ψ s ω < N := hψN ρ ⟨hsρ, hρt⟩
  have hρmem : ρ ∈ Icc s t := ⟨hsρ, hρt⟩
  have hev : ∀ᶠ r in 𝓝[Icc s t] ρ, ε < Y r ω ∧ Y r ω < a ∧ ψ r ω - ψ s ω < N := by
    refine ((hY ρ hρmem).eventually (lt_mem_nhds hcon)).and
      (((hY ρ hρmem).eventually (gt_mem_nhds hYa)).and ?_)
    exact ((hψ ρ hρmem).sub continuousWithinAt_const).eventually (gt_mem_nhds hψρ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set v : ℝ≥0 := min (ρ + (δ / 2).toNNReal) u with hv
  have hδ2 : (0 : ℝ) < ((δ / 2).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by positivity)]; positivity
  have hρv : ρ < v := by
    refine lt_min ?_ hρu
    have : (0 : ℝ≥0) < (δ / 2).toNNReal := by exact_mod_cast hδ2
    exact lt_add_of_pos_right _ this
  have hvu : v ≤ u := min_le_right _ _
  have hvρ : (v : ℝ) ≤ ρ + δ / 2 := by
    have : v ≤ ρ + (δ / 2).toNNReal := min_le_left _ _
    have h' : ((ρ + (δ / 2).toNNReal : ℝ≥0) : ℝ) = ρ + δ / 2 := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity)]
    rw [← h']; exact_mod_cast this
  have halive : ω ∈ repulsionLocalizer Y ψ A s ε a N v := by
    have hvs : ¬ v < s := not_lt.2 (hsρ.trans hρv.le)
    simp only [repulsionLocalizer, hvs, ite_false, mem_inter_iff, mem_iInter]
    refine ⟨hA, fun q hq => ?_⟩
    by_cases hqρ : (q : ℝ) < ρ
    · exact (cond_of_lt_lifetime (t := t) hq.1 hqρ).2
    · push Not at hqρ
      have hq0 : (0 : ℝ) ≤ q := s.2.trans hq.1
      have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
      have hmem : (q : ℝ).toNNReal ∈ Metric.ball ρ δ ∩ Icc s t := by
        refine ⟨?_, ?_, ?_⟩
        · rw [Metric.mem_ball, NNReal.dist_eq, hqc, abs_sub_lt_iff]
          constructor <;> linarith [hq.2]
        · rw [← NNReal.coe_le_coe, hqc]; exact hq.1
        · rw [← NNReal.coe_le_coe, hqc]
          exact hq.2.trans (by exact_mod_cast hvu.trans hu.2)
      have h := hball hmem
      exact ⟨h.1, h.2.1, h.2.2.le⟩
  have := le_lifetimeOf_of (A := fun u => ω ∈ repulsionLocalizer Y ψ A s ε a N u) (s := s)
    (hvu.trans hu.2) halive
  exact absurd this (not_le.2 hρv)

/-- The clamped process satisfies the hypotheses of Itô's formula on `[s, ρ]`. -/
lemma isTanakaPath_clampProc {σ C : ℝ} {B β : ℝ≥0 → Ω → ℝ} {ω : Ω} (hst : s ≤ t) (hε : 0 < ε)
    (hεa : ε ≤ a) (hN : 0 ≤ N) (hAs : ω ∈ A → ε < Y s ω ∧ Y s ω < a)
    (hP : ω ∈ A → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    IsTanakaPath σ 0 (max a N) s (lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω)
      (clampProc ε a Y · ω) (B · ω) (fun _ => 0) (β · ω) := by
  have ha : 0 ≤ a := hε.le.trans hεa
  have habs : ∀ u, |clampProc ε a Y u ω| ≤ max a N := fun u => by
    have h := clampProc_mem (Y := Y) hεa u ω
    rw [abs_of_nonneg (hε.le.trans h.1)]; exact h.2.trans (le_max_left _ _)
  by_cases hA : ω ∈ A
  swap
  · rw [lifetime_repulsion_eq_of_not_mem hA]
    exact isTanakaPath_singleton (habs s) (ha.trans (le_max_left _ _))
  obtain ⟨hYc, hBc, hψc, hdec⟩ := hP hA
  set ρ := lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω
  have hρt : ρ ≤ t := lifetimeOf_le hst
  have hsρ : s ≤ ρ := le_lifetimeOf _ _ _
  have hsub : Icc s ρ ⊆ Icc s t := Icc_subset_Icc le_rfl hρt
  have hb := bounds_on_lifetime (A := A) (t := t) hst (hAs hA) hN hYc hψc
  have hcl : ∀ u ∈ Icc s ρ, clampProc ε a Y u ω = Y u ω := fun u hu =>
    clampProc_eq (hb u hu).1 (hb u hu).2.1
  have hpos : ∀ u ∈ Icc s ρ, ∀ r ∈ Icc s u, 0 < Y r ω ∧ Y r ω ≤ a := fun u hu r hr =>
    have hr' : r ∈ Icc s ρ := ⟨hr.1, hr.2.trans hu.2⟩
    ⟨lt_of_lt_of_le hε (hb r hr').1, (hb r hr').2.1⟩
  have hdρ := hdec ρ ⟨hsρ, hρt⟩ (hpos ρ ⟨hsρ, le_rfl⟩)
  refine ⟨?_, hBc.mono hsub, continuousOn_const, hdρ.1, ?_, monotoneOn_const, fun _ _ _ _ _ _ => rfl,
    fun u _ => habs u, ?_, ?_⟩
  · show ContinuousOn (fun x => max ε (min a (Y x ω))) (Icc s ρ)
    exact ((continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn hYc).mono
      hsub
  · intro u hu
    have h2 := (hdec u (hsub hu) (hpos u hu)).2.1
    beta_reduce at h2 ⊢
    rw [hcl u hu, hcl s ⟨le_rfl, hsρ⟩, h2]
    ring
  · exact hdρ.2.2.1.trans ((hb ρ ⟨hsρ, le_rfl⟩).2.2.trans (le_max_right _ _))
  · simp only [sub_self]; exact ha.trans (le_max_left _ _)

/-! ### The supermartingale estimate -/

section Ito

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B β : ℝ≥0 → Ω → ℝ}
  {σ C : ℝ}

lemma toNNReal_mem_Icc_of_mem {u v : ℝ≥0} {r : ℝ} (hr : r ∈ Icc (u : ℝ) v) :
    r.toNNReal ∈ Icc u v :=
  ⟨(Real.le_toNNReal_iff_coe_le (u.2.trans hr.1)).2 hr.1, Real.toNNReal_le_iff_le_coe.2 hr.2⟩

/-- The pointwise generator inequality on `[s, ρ]`:
`∫_s^ρ F'(Y) β + σ²/2 ∫_s^ρ F''(Y) ≤ 0`, from (RP1) and (RP2). -/
lemma integral_generator_nonpos {ω : Ω} (hσ : σ ≠ 0) (hst : s ≤ t) (hε : 0 < ε) (hN : 0 ≤ N) (hAs : ω ∈ A → ε < Y s ω ∧ Y s ω < a)
    (hP : ω ∈ A → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    (∫ r in (s : ℝ)..(lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω),
        repulsionF1 (2 * C / σ ^ 2) ε (clampProc ε a Y r.toNNReal ω) * β r.toNNReal ω) +
      σ ^ 2 / 2 * ∫ r in (s : ℝ)..(lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω),
        repulsionF2 (2 * C / σ ^ 2) ε (clampProc ε a Y r.toNNReal ω) ≤ 0 := by
  set η := 2 * C / σ ^ 2
  by_cases hA : ω ∈ A
  swap
  · rw [lifetime_repulsion_eq_of_not_mem hA]; simp
  obtain ⟨hYc, -, hψc, hdec⟩ := hP hA
  set ρ := lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω
  have hρt : ρ ≤ t := lifetimeOf_le hst
  have hsρ : s ≤ ρ := le_lifetimeOf _ _ _
  have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
  have hsub : Icc s ρ ⊆ Icc s t := Icc_subset_Icc le_rfl hρt
  have hb := bounds_on_lifetime (A := A) (t := t) hst (hAs hA) hN hYc hψc
  have hpos : ∀ r ∈ Icc s ρ, 0 < Y r ω ∧ Y r ω ≤ a := fun r hr =>
    ⟨lt_of_lt_of_le hε (hb r hr).1, (hb r hr).2.1⟩
  have hdρ := hdec ρ ⟨hsρ, hρt⟩ (fun r hr => hpos r hr)
  have hXc : ContinuousOn (fun r : ℝ => clampProc ε a Y r.toNNReal ω) (Icc (s : ℝ) ρ) :=
    continuousOn_comp_toNNReal (G := fun u => clampProc ε a Y u ω)
      (((continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn hYc).mono
        hsub)
  have hI1 : IntervalIntegrable (fun r : ℝ => repulsionF1 η ε (clampProc ε a Y r.toNNReal ω) *
      β r.toNNReal ω) volume s ρ := by
    refine hdρ.1.continuousOn_mul ?_
    rw [uIcc_of_le hsρ']
    exact (continuous_repulsionF1 η hε).comp_continuousOn hXc
  have hI2 : IntervalIntegrable (fun r : ℝ => repulsionF2 η ε (clampProc ε a Y r.toNNReal ω))
      volume s ρ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hsρ']
    exact (continuous_repulsionF2 η hε).comp_continuousOn hXc
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1 (hI2.const_mul _)]
  have h0 : (∫ r in (s : ℝ)..ρ, (0 : ℝ)) = 0 := intervalIntegral.integral_zero
  rw [← h0]
  refine intervalIntegral.integral_mono_ae_restrict hsρ' (hI1.add (hI2.const_mul _))
    intervalIntegrable_const ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [hdρ.2.2.2] with r hr hrI
  have hrI' := toNNReal_mem_Icc_of_mem hrI
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

/-- **The supermartingale estimate** of the proof of Aux. lemma 5: for the test function `F` and
the lifetime `ρ` of the localizer, `E[F(Y_ρ) − F(Y_s)] ≤ 0` (Itô's formula in expectation). -/
theorem integral_repulsionF_sub_le (hB : IsFilteredPreBrownian B 𝓕 P) (hσ : σ ≠ 0)
    (hε : 0 < ε) (hεa : ε ≤ a) (hN : 0 ≤ N) (hst : s ≤ t) (hY : ∀ u, Measurable[𝓕 u] (Y u))
    (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (hA : MeasurableSet[𝓕 s] A)
    (hAs : ∀ ω ∈ A, ε < Y s ω ∧ Y s ω < a)
    (hpath : ∀ᵐ ω ∂P, ω ∈ A → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    ∫ ω, (repulsionF (2 * C / σ ^ 2) ε a
        (clampProc ε a Y (lifetime (repulsionLocalizer Y ψ A s ε a N) s t ω) ω) -
      repulsionF (2 * C / σ ^ 2) ε a (clampProc ε a Y s ω)) ∂P ≤ 0 := by
  set η := 2 * C / σ ^ 2
  set 𝒢 := repulsionLocalizer Y ψ A s ε a N
  have hT : ∀ᵐ ω ∂P, IsTanakaPath σ 0 (max a N) s (lifetime 𝒢 s t ω) (clampProc ε a Y · ω)
      (B · ω) ((fun _ _ => (0 : ℝ)) · ω) (β · ω) := by
    filter_upwards [hpath] with ω hω
    exact isTanakaPath_clampProc hst hε hεa hN (hAs ω) hω
  have hXm : ∀ u, Measurable[𝓕 u] (clampProc ε a Y u) := measurable_clampProc hY
  have h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u) := measurableSet_repulsionLocalizer hY hψ hA
  have h𝒢a : Antitone 𝒢 := repulsionLocalizer_antitone
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
  exact integral_generator_nonpos hσ hst hε hN (hAs ω) hω

end Ito

/-! ### The hitting estimate (RP3) and Aux. lemma 5 -/

section Hit

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B β : ℝ≥0 → Ω → ℝ}
  {σ C ℓ : ℝ}

/-- **(RP3)**: if `ℓ ≤ Y_s < a` on `A`, the probability that `Y` reaches `(−∞, 0]` before `a` and
before `t` (while the dominating process stays below `N`) is at most `F(ℓ)/F(ε)` for every
`0 < ε < ℓ`. -/
theorem measure_hit_le (hB : IsFilteredPreBrownian B 𝓕 P) (hσ : σ ≠ 0) (hC : 0 ≤ C)
    (hε : 0 < ε) (hεℓ : ε < ℓ) (hℓa : ℓ < a) (hN : 0 ≤ N) (hst : s ≤ t)
    (hY : ∀ u, Measurable[𝓕 u] (Y u)) (hψ : ∀ u, Measurable[𝓕 u] (ψ u))
    (hA : MeasurableSet[𝓕 s] A) (hAs : ∀ ω ∈ A, ℓ ≤ Y s ω ∧ Y s ω < a)
    (hpath : ∀ᵐ ω ∂P, ω ∈ A → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    P {ω | ω ∈ A ∧ (∀ r ∈ Icc s t, ψ r ω - ψ s ω < N) ∧
        ∃ u ∈ Icc s t, Y u ω ≤ 0 ∧ ∀ r ∈ Icc s u, Y r ω < a} ≤
      ENNReal.ofReal (repulsionInt (2 * C / σ ^ 2) a ℓ / repulsionInt (2 * C / σ ^ 2) a ε) := by
  set η := 2 * C / σ ^ 2
  have hη : 0 ≤ η := div_nonneg (by linarith) (sq_nonneg σ)
  set 𝒢 := repulsionLocalizer Y ψ A s ε a N
  set f := repulsionF η ε a
  have hℓ : 0 < ℓ := hε.trans hεℓ
  have hεa : ε ≤ a := (hεℓ.trans hℓa).le
  have hAs' : ∀ ω ∈ A, ε < Y s ω ∧ Y s ω < a := fun ω hω =>
    ⟨hεℓ.trans_le (hAs ω hω).1, (hAs ω hω).2⟩
  have hT : ∀ᵐ ω ∂P, IsTanakaPath σ 0 (max a N) s (lifetime 𝒢 s t ω) (clampProc ε a Y · ω)
      (B · ω) ((fun _ _ => (0 : ℝ)) · ω) (β · ω) := by
    filter_upwards [hpath] with ω hω
    exact isTanakaPath_clampProc hst hε hεa hN (hAs' ω) hω
  have hXm : ∀ u, Measurable[𝓕 u] (clampProc ε a Y u) := measurable_clampProc hY
  have h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u) := measurableSet_repulsionLocalizer hY hψ hA
  have hS := integrable_limitS hst hXm h𝒢 repulsionLocalizer_antitone
    (continuous_repulsionF η hε a) hT
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
    · simp only [g, 𝒢, lifetime_repulsion_eq_of_not_mem hω, sub_self, zero_add]
      exact repulsionInt_nonneg hℓ hℓa.le
  have hgi : Integrable g P := hS.add (integrable_const _)
  have hEg : ∫ ω, g ω ∂P ≤ Fℓ := by
    simp only [g]
    rw [integral_add hS (integrable_const _), integral_const, probReal_univ, one_smul]
    linarith [integral_repulsionF_sub_le (N := N) hB hσ hε hεa hN hst hY hψ hA hAs' hpath]
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
  have hN' : 0 ≤ N := hN
  have hle := le_of_hit (N := N) hst hε hA' (hAs' ω hA') hYc hψc hψN hu hYu hlt
  have hcl : clampProc ε a Y (lifetime 𝒢 s t ω) ω = ε := by
    unfold clampProc
    exact max_eq_left ((min_le_right _ _).trans hle)
  have hfε : f ε = Fε := repulsionF_eq η hε le_rfl hεa
  show Fε ≤ g ω
  simp only [g, hcl, hfε]
  linarith [hfs ω hA']

/-- **Aux. lemma 5 (the localized repulsion criterion)**, Specification §2.2. Let `B` be an
`𝓕`-Brownian motion, `σ ≠ 0`, `a > 0`, `C ≥ 0`, `Y` and `ψ` adapted, `A ∈ 𝓕_s`, and suppose
that almost surely on `A` the path hypotheses `IsRepulsionPath` hold on `[s, t]` (the semimartingale
decomposition `dY = σ dB + β dt` and the drift inequality (RP1) `β ≥ σ²/(2Y) − C` on every interval
on which `0 < Y ≤ a`). Then almost surely on `A ∩ {0 < Y_s < a}`, `Y` does not reach `(−∞, 0]` on
`[s, t]` before leaving through `a`. -/
theorem ae_pos_of_isRepulsionPath (hB : IsFilteredPreBrownian B 𝓕 P) (hσ : σ ≠ 0) (hC : 0 ≤ C)
    (hst : s ≤ t) (hY : ∀ u, Measurable[𝓕 u] (Y u)) (hψ : ∀ u, Measurable[𝓕 u] (ψ u))
    (hA : MeasurableSet[𝓕 s] A)
    (hpath : ∀ᵐ ω ∂P, ω ∈ A → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω)) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < Y s ω → Y s ω < a → ∀ u ∈ Icc s t, (∀ r ∈ Icc s u, Y r ω < a) →
      0 < Y u ω := by
  set η := 2 * C / σ ^ 2
  have hη : 0 ≤ η := div_nonneg (by linarith) (sq_nonneg σ)
  -- the bad events
  let Am : ℕ → Set Ω := fun m => A ∩ {ω | 1 / ((m : ℝ) + 1) ≤ Y s ω ∧ Y s ω < a}
  let Bad : ℕ → ℕ → Set Ω := fun m N => {ω | ω ∈ Am m ∧ (∀ r ∈ Icc s t, ψ r ω - ψ s ω < N) ∧
    ∃ u ∈ Icc s t, Y u ω ≤ 0 ∧ ∀ r ∈ Icc s u, Y r ω < a}
  have hAm : ∀ m, MeasurableSet[𝓕 s] (Am m) := fun m =>
    hA.inter ((measurableSet_le measurable_const (hY s)).inter
      (measurableSet_lt (hY s) measurable_const))
  have hBad : ∀ m N, P (Bad m N) = 0 := by
    intro m N
    set ℓ : ℝ := 1 / ((m : ℝ) + 1)
    have hℓ : 0 < ℓ := by positivity
    by_cases hℓa : ℓ < a
    swap
    · have : Bad m N = ∅ := by
        ext ω
        simp only [Bad, Am, mem_ofPred_eq, mem_inter_iff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, h1, h2⟩, -⟩
        exact hℓa (h1.trans_lt h2)
      rw [this, measure_empty]
    have hpath' : ∀ᵐ ω ∂P, ω ∈ Am m → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω)
        (ψ · ω) := by
      filter_upwards [hpath] with ω hω h using hω h.1
    have hAs : ∀ ω ∈ Am m, ℓ ≤ Y s ω ∧ Y s ω < a := fun ω hω => hω.2
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) bot_le
    rw [zero_add]
    have hFℓ : 0 ≤ repulsionInt η a ℓ := repulsionInt_nonneg hℓ hℓa.le
    obtain ⟨ε₀, hε₀, -, hK⟩ := exists_le_repulsionInt (η := η) hη (hℓ.trans hℓa)
      (repulsionInt η a ℓ / δ)
    set ε := min ε₀ (ℓ / 2)
    have hε : 0 < ε := lt_min hε₀ (by positivity)
    have hεℓ : ε < ℓ := (min_le_right _ _).trans_lt (by linarith)
    have hKε := hK ε hε (min_le_left _ _)
    have hFε : 0 < repulsionInt η a ε := by
      have := log_sub_log_le_repulsionInt (a := a) hη hε (hεℓ.trans hℓa).le
      have : Real.log ε < Real.log a := Real.log_lt_log hε (hεℓ.trans hℓa)
      linarith
    have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine (measure_hit_le hB hσ hC hε hεℓ hℓa hNn hst hY hψ (hAm m) hAs hpath').trans ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hFε]
    have hδ' : (0 : ℝ) < δ := hδ
    have := (div_le_iff₀ hδ').1 hKε
    linarith
  -- the exceptional set is covered by the bad events and the failure of the path hypotheses
  rw [ae_iff]
  refine measure_mono_null (t := (⋃ m, ⋃ N, Bad m N) ∪
    {ω | ¬ (ω ∈ A → IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω))}) ?_
    (measure_union_null (measure_iUnion_null fun m => measure_iUnion_null fun N => hBad m N)
      (ae_iff.1 hpath))
  intro ω hω
  simp only [mem_ofPred_eq, not_forall, not_lt, exists_prop] at hω
  obtain ⟨hA', hY0, hYa, u, hu, hlt, hYu⟩ := hω
  by_cases hgood : IsRepulsionPath σ a C s t (Y · ω) (B · ω) (β · ω) (ψ · ω)
  swap
  · exact Or.inr fun h => hgood (h hA')
  left
  obtain ⟨-, -, hψc, -⟩ := hgood
  obtain ⟨K, hK⟩ := (isCompact_Icc.bddAbove_image hψc :
    BddAbove ((fun r => ψ r ω) '' Icc s t))
  obtain ⟨N, hN⟩ := exists_nat_gt (K - ψ s ω)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hY0
  simp only [mem_iUnion]
  refine ⟨m, N, ⟨hA', hm.le, hYa⟩, fun r hr => ?_, u, hu, hYu, hlt⟩
  have := hK (mem_image_of_mem _ hr)
  linarith

end Hit

end InteractingSLE.Sec4.Repulsion
