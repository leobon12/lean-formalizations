/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.Tanaka
import Mathlib.Probability.Process.Stopping

/-!
# Tanaka and occupation statements up to a stopping time (no integrability assumptions)

Packet PROVE-TANAKA. The user-facing forms of `ae_volume_zeroSet_eq_zero` and
`ae_singular_eq_of_isTanakaPath`. Let `τ` be an `𝓕`-stopping time and `s ≤ t`. Write
`I(ω) = {u : s ≤ u ≤ t, u ≤ τ ω}`. Suppose that almost surely, whenever `s ≤ τ ω`, on `I(ω)`

  `X_u = X_s + a (B_u - B_s) + ∫_s^u b + c (J_u - J_s)`

with `X, B, J, ψ` continuous, `b` integrable, `J` nondecreasing and constant on intervals where
`X ≠ 0`, and `∫_s^u |b| ≤ ψ_u - ψ_s` for an adapted process `ψ` (`IsTanakaPathOn`). Then
almost surely the zero set of `X` on `I(ω)` is Lebesgue-null (`ae_volume_zeroSet_stopped`, for
`a ≠ 0`); if moreover `X ≥ 0` and `∫_s^u X⁻¹ ≤ ψ_u - ψ_s` on `I(ω)`, then `J` is constant on
`I(ω)` (`ae_singular_const_stopped`, for `a ≠ 0`, `c ≠ 0`).

The dominating process `ψ` replaces any measurability requirement on `b` or on `X⁻¹`: in the
specification, `ψ` is a sum of multiples of `|V^j - V^j_s|` for monotone force-point coordinates,
because `∫ 2 / |V^j - W| ≤ |V^j_v - V^j_u|` (pp. 36, 39).

Localization: `localizer τ X J ψ s N u` is the event that `u < τ`, `|X_s| ≤ N`, and
`|X_q| ≤ N`, `J_q - J_s ≤ N`, `ψ_q - ψ_s ≤ N` at every rational `q ∈ [s, u]` (an `𝓕_u`-event);
on the complement of `{|X_s| ≤ N}` the process is replaced by `0` after time `s`
(`cutoffProc`), so that the localized hypotheses hold almost surely for every `N`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology ENNReal

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The pathwise hypotheses on `[s, e]`, with a dominating process `ψ` for `∫ |b|`. -/
def IsTanakaPathOn (a c : ℝ) (s e : ℝ≥0) (x β j b ψ : ℝ≥0 → ℝ) : Prop :=
  ContinuousOn x (Icc s e) ∧ ContinuousOn β (Icc s e) ∧ ContinuousOn j (Icc s e) ∧
  ContinuousOn ψ (Icc s e) ∧
  IntervalIntegrable (fun r : ℝ => b r.toNNReal) volume s e ∧
  (∀ u ∈ Icc s e, x u = x s + a * (β u - β s) + (∫ r in (s : ℝ)..u, b r.toNNReal) +
    c * (j u - j s)) ∧
  MonotoneOn j (Icc s e) ∧
  (∀ u v, s ≤ u → u ≤ v → v ≤ e → (∀ r ∈ Icc u v, x r ≠ 0) → j u = j v) ∧
  (∀ u ∈ Icc s e, ∫ r in (s : ℝ)..u, |b r.toNNReal| ≤ ψ u - ψ s)

/-- The end `min t τ` of the interval `I(ω)` (as an element of `ℝ≥0`). -/
def stopEnd (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ≥0 := min t (WithTop.untopD t (τ ω))

lemma stopEnd_le (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : stopEnd τ t ω ≤ t := min_le_left _ _

lemma untopD_eq_of_coe {τ : WithTop ℝ≥0} {t v : ℝ≥0} (h : τ = ↑v) : WithTop.untopD t τ = v := by
  subst h; rfl

lemma untopD_eq_of_top {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : τ = ⊤) : WithTop.untopD t τ = t := by
  subst h; rfl

lemma coe_stopEnd_le (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (stopEnd τ t ω : WithTop ℝ≥0) ≤ τ ω := by
  unfold stopEnd
  cases h : τ ω with
  | top => exact le_top
  | coe v =>
    rw [untopD_eq_of_coe rfl]
    exact WithTop.coe_le_coe.2 (min_le_right _ _)

lemma le_stopEnd_iff {τ : Ω → WithTop ℝ≥0} {t u : ℝ≥0} {ω : Ω} :
    u ≤ stopEnd τ t ω ↔ u ≤ t ∧ (u : WithTop ℝ≥0) ≤ τ ω := by
  unfold stopEnd
  cases h : τ ω with
  | top => rw [untopD_eq_of_top rfl, min_self]; exact ⟨fun h => ⟨h, le_top⟩, fun h => h.1⟩
  | coe v => rw [untopD_eq_of_coe rfl, le_min_iff, WithTop.coe_le_coe]

/-! ### The localizer -/

/-- The localizing events. -/
def localizer (τ : Ω → WithTop ℝ≥0) (X J ψ : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (N : ℝ) (u : ℝ≥0) :
    Set Ω :=
  if u < s then univ else
    {ω | (u : WithTop ℝ≥0) < τ ω} ∩ {ω | |X s ω| ≤ N} ∩
      ⋂ (q : ℚ) (_ : (s : ℝ) ≤ q ∧ (q : ℝ) ≤ u),
        {ω | |X (q : ℝ).toNNReal ω| ≤ N ∧ J (q : ℝ).toNNReal ω - J s ω ≤ N ∧
          ψ (q : ℝ).toNNReal ω - ψ s ω ≤ N}

variable {τ : Ω → WithTop ℝ≥0} {X J ψ : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {N : ℝ}

lemma localizer_antitone : Antitone (localizer τ X J ψ s N) := by
  intro u v huv ω hω
  unfold localizer at hω ⊢
  by_cases hu : u < s
  · simp [hu]
  · have hv : ¬ v < s := fun h => hu (lt_of_le_of_lt huv h)
    simp only [hv, hu, ite_false, mem_inter_iff, mem_ofPred_eq, mem_iInter] at hω ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hω
    refine ⟨⟨lt_of_le_of_lt (WithTop.coe_le_coe.2 huv) h1, h2⟩, ?_⟩
    exact fun q hq => h3 q ⟨hq.1, hq.2.trans (by exact_mod_cast huv)⟩

lemma measurableSet_localizer {𝓕 : Filtration ℝ≥0 mΩ} (hτ : IsStoppingTime 𝓕 τ)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (hJ : ∀ u, Measurable[𝓕 u] (J u))
    (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] (localizer τ X J ψ s N u) := by
  unfold localizer
  split_ifs with hu
  · exact MeasurableSet.univ
  · have hsu : s ≤ u := not_lt.1 hu
    have hXs : Measurable[𝓕 u] (X s) := (hX s).mono (𝓕.mono hsu) le_rfl
    have hJs : Measurable[𝓕 u] (J s) := (hJ s).mono (𝓕.mono hsu) le_rfl
    have hψs : Measurable[𝓕 u] (ψ s) := (hψ s).mono (𝓕.mono hsu) le_rfl
    refine ((?_ : MeasurableSet[𝓕 u] {ω | (u : WithTop ℝ≥0) < τ ω}).inter
      (measurableSet_le (continuous_abs.measurable.comp hXs) measurable_const)).inter
      (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_)
    · have := (hτ u).compl
      convert this using 1
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    · have hq : (q : ℝ).toNNReal ≤ u := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hq.2
      have hXq : Measurable[𝓕 u] (X (q : ℝ).toNNReal) := (hX _).mono (𝓕.mono hq) le_rfl
      have hJq : Measurable[𝓕 u] (J (q : ℝ).toNNReal) := (hJ _).mono (𝓕.mono hq) le_rfl
      have hψq : Measurable[𝓕 u] (ψ (q : ℝ).toNNReal) := (hψ _).mono (𝓕.mono hq) le_rfl
      exact (measurableSet_le (continuous_abs.measurable.comp hXq) measurable_const).inter
        ((measurableSet_le (hJq.sub hJs) measurable_const).inter
          (measurableSet_le (hψq.sub hψs) measurable_const))

/-- The process cut off to `0` after time `s` on `{|X_s| > N} ∪ {τ ≤ s}`. -/
def cutoffProc (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (s : ℝ≥0) (N : ℝ) (u : ℝ≥0) (ω : Ω) :
    ℝ :=
  if s ≤ u ∧ (N < |X s ω| ∨ τ ω ≤ s) then 0 else X u ω

lemma measurable_cutoffProc {𝓕 : Filtration ℝ≥0 mΩ} (hτ : IsStoppingTime 𝓕 τ)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (u : ℝ≥0) : Measurable[𝓕 u] (cutoffProc X τ s N u) := by
  unfold cutoffProc
  by_cases hsu : s ≤ u
  · have hXs : Measurable[𝓕 u] (X s) := (hX s).mono (𝓕.mono hsu) le_rfl
    have hτs : MeasurableSet[𝓕 u] {ω | τ ω ≤ s} := 𝓕.mono hsu _ (hτ s)
    simp only [hsu, true_and]
    exact Measurable.ite ((measurableSet_lt measurable_const
      (continuous_abs.measurable.comp hXs)).union hτs) measurable_const (hX u)
  · simp only [hsu, false_and, ite_false]
    exact hX u

lemma cutoffProc_eq {ω : Ω} (h1 : ¬ N < |X s ω|) (h2 : ¬ τ ω ≤ s) (u : ℝ≥0) :
    cutoffProc X τ s N u ω = X u ω := by
  unfold cutoffProc
  rw [ite_eq_right_iff]
  intro h
  exact absurd h.2 (not_or.2 ⟨h1, h2⟩)

/-! ### Pathwise transfer -/

/-- A bound at `s` and at the rational times of `[s, ρ)` extends to `[s, ρ]` by continuity. -/
lemma le_of_le_rat {g : ℝ≥0 → ℝ} {s ρ : ℝ≥0} {N : ℝ} (hg : ContinuousOn g (Icc s ρ))
    (hs : g s ≤ N) (hq : ∀ q : ℚ, (s : ℝ) ≤ q → (q : ℝ) < ρ → g (q : ℝ).toNNReal ≤ N) :
    ∀ u ∈ Icc s ρ, g u ≤ N := by
  intro u hu
  rcases hu.1.eq_or_lt with rfl | hsu
  · exact hs
  by_contra hcon
  push Not at hcon
  have hev := (hg u hu).eventually (lt_mem_nhds hcon)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hsu' : (s : ℝ) < u := by exact_mod_cast hsu
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hsu' (sub_lt_self (u : ℝ) hε))
  have hqs : (s : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hq0 : (0 : ℝ) ≤ q := s.2.trans hqs.le
  have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have hmem : (q : ℝ).toNNReal ∈ Metric.ball u ε ∩ Icc s ρ := by
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · rw [Metric.mem_ball, NNReal.dist_eq, hqc, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith [le_max_right (s : ℝ) ((u : ℝ) - ε)]
    · rw [← NNReal.coe_le_coe, hqc]; exact hqs.le
    · rw [← NNReal.coe_le_coe, hqc]; exact (hq2.trans_le (by exact_mod_cast hu.2)).le
  have h1 := hball hmem
  have h2 := hq q hqs.le (hq2.trans_le (by exact_mod_cast hu.2))
  simp only [mem_ofPred_eq] at h1
  linarith

/-- `IsTanakaPath` on a degenerate interval. -/
lemma isTanakaPath_singleton {a c N : ℝ} {s : ℝ≥0} {x β j b : ℝ≥0 → ℝ} (hx : |x s| ≤ N)
    (hN : 0 ≤ N) : IsTanakaPath a c N s s x β j b := by
  have hI : Icc s s = {s} := Icc_self s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hI]; exact continuousOn_singleton _ _
  · rw [hI]; exact continuousOn_singleton _ _
  · rw [hI]; exact continuousOn_singleton _ _
  · exact IntervalIntegrable.refl
  · intro u hu
    rw [hI, mem_singleton_iff] at hu
    subst hu; simp
  · rw [hI]; exact (subsingleton_singleton).monotoneOn _
  · intro u v hu huv hv _
    rw [le_antisymm (huv.trans hv) hu, le_antisymm hv (hu.trans huv)]
  · intro u hu
    rw [hI, mem_singleton_iff] at hu
    rw [hu]; exact hx
  · simp [hN]
  · simp [hN]

lemma lifetimeOf_eq_of_not {A : ℝ≥0 → Prop} (hA : ∀ u v, u ≤ v → A v → A u) {s t : ℝ≥0}
    (hs : ¬ A s) : lifetimeOf A s t = s := by
  refine le_antisymm (csSup_le (insert_nonempty _ _) ?_) (le_lifetimeOf A s t)
  rintro u (rfl | ⟨_, hu⟩)
  · exact le_rfl
  · by_contra h
    exact hs (hA _ _ (not_le.1 h).le hu)

variable {a c : ℝ} {t : ℝ≥0} {B b : ℝ≥0 → Ω → ℝ}

lemma lifetime_localizer_le {ω : Ω} (hst : s ≤ t) (hsτ : (s : WithTop ℝ≥0) ≤ τ ω) :
    lifetime (localizer τ X J ψ s N) s t ω ≤ stopEnd τ t ω := by
  rw [le_stopEnd_iff]
  refine ⟨lifetimeOf_le hst, ?_⟩
  cases h : τ ω with
  | top => exact le_top
  | coe v =>
    rw [h] at hsτ
    refine WithTop.coe_le_coe.2 (csSup_le (insert_nonempty _ _) ?_)
    rintro u (rfl | ⟨_, hu⟩)
    · exact WithTop.coe_le_coe.1 hsτ
    · by_cases hus : u < s
      · exact hus.le.trans (WithTop.coe_le_coe.1 hsτ)
      · have hu' := hu
        simp only [localizer, hus, ite_false, mem_inter_iff, mem_ofPred_eq] at hu'
        rw [h] at hu'
        exact (WithTop.coe_lt_coe.1 hu'.1.1).le

lemma localizer_antitone' {ω : Ω} : ∀ u v : ℝ≥0, u ≤ v → ω ∈ localizer τ X J ψ s N v →
    ω ∈ localizer τ X J ψ s N u := fun _ _ huv h => localizer_antitone huv h

/-- On `[s, ρ_N]`, the localized bounds hold (when alive at `s`). -/
lemma localizer_bounds {ω : Ω} (hst : s ≤ t) (hs : ω ∈ localizer τ X J ψ s N s)
    (hP : IsTanakaPathOn a c s (stopEnd τ t ω) (X · ω) (B · ω) (J · ω) (b · ω) (ψ · ω)) :
    ∀ u ∈ Icc s (lifetime (localizer τ X J ψ s N) s t ω),
      |X u ω| ≤ N ∧ J u ω - J s ω ≤ N ∧ ψ u ω - ψ s ω ≤ N := by
  set ρ := lifetime (localizer τ X J ψ s N) s t ω
  have hs' := hs
  simp only [localizer, lt_irrefl, ite_false, mem_inter_iff, mem_ofPred_eq] at hs'
  obtain ⟨⟨hsτ, hXs⟩, _⟩ := hs'
  have hN : 0 ≤ N := (abs_nonneg _).trans hXs
  have hsub : Icc s ρ ⊆ Icc s (stopEnd τ t ω) :=
    Icc_subset_Icc le_rfl (lifetime_localizer_le hst hsτ.le)
  have hrat : ∀ q : ℚ, (s : ℝ) ≤ q → (q : ℝ) < ρ →
      |X (q : ℝ).toNNReal ω| ≤ N ∧ J (q : ℝ).toNNReal ω - J s ω ≤ N ∧
        ψ (q : ℝ).toNNReal ω - ψ s ω ≤ N := by
    intro q hsq hqρ
    have hq0 : (0 : ℝ) ≤ q := s.2.trans hsq
    have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have hsq' : s ≤ (q : ℝ).toNNReal := by rw [← NNReal.coe_le_coe, hqc]; exact hsq
    have hqρ' : (q : ℝ).toNNReal < ρ := by rw [← NNReal.coe_lt_coe, hqc]; exact hqρ
    have hal := of_lt_lifetimeOf (A := fun u => ω ∈ localizer τ X J ψ s N u)
      localizer_antitone' hsq' hqρ'
    have hnot : ¬ (q : ℝ).toNNReal < s := not_lt.2 hsq'
    simp only [localizer, hnot, ite_false, mem_inter_iff, mem_ofPred_eq, mem_iInter] at hal
    exact hal.2 q ⟨hsq, hqc.ge⟩
  intro u hu
  refine ⟨le_of_le_rat (g := fun u => |X u ω|) (continuous_abs.comp_continuousOn (hP.1.mono hsub))
    hXs (fun q h1 h2 => (hrat q h1 h2).1) u hu,
    le_of_le_rat (g := fun u => J u ω - J s ω) ((hP.2.2.1.mono hsub).sub continuousOn_const)
      (by simp [hN]) (fun q h1 h2 => (hrat q h1 h2).2.1) u hu,
    le_of_le_rat (g := fun u => ψ u ω - ψ s ω) ((hP.2.2.2.1.mono hsub).sub continuousOn_const)
      (by simp [hN]) (fun q h1 h2 => (hrat q h1 h2).2.2) u hu⟩

/-- The localized hypotheses hold for the cut-off process, for every `N ≥ 0`. -/
lemma isTanakaPath_cutoff {ω : Ω} (hN : 0 ≤ N) (hst : s ≤ t)
    (hP : (s : WithTop ℝ≥0) ≤ τ ω → IsTanakaPathOn a c s (stopEnd τ t ω) (X · ω) (B · ω) (J · ω)
      (b · ω) (ψ · ω)) :
    IsTanakaPath a c N s (lifetime (localizer τ X J ψ s N) s t ω) (cutoffProc X τ s N · ω)
      (B · ω) (J · ω) (b · ω) := by
  set ρ := lifetime (localizer τ X J ψ s N) s t ω
  by_cases hs : ω ∈ localizer τ X J ψ s N s
  · have hs' := hs
    simp only [localizer, lt_irrefl, ite_false, mem_inter_iff, mem_ofPred_eq] at hs'
    obtain ⟨⟨hsτ, hXs⟩, _⟩ := hs'
    have hcut : (cutoffProc X τ s N · ω) = (X · ω) :=
      funext (cutoffProc_eq (not_lt.2 hXs) (not_le.2 hsτ))
    rw [hcut]
    have hPω := hP hsτ.le
    obtain ⟨hx, hβ, hj, _, hb, hdec, hmono, hsupp, hdom⟩ := id hPω
    have hρe : ρ ≤ stopEnd τ t ω := lifetime_localizer_le hst hsτ.le
    have hsρ : s ≤ ρ := le_lifetimeOf _ _ _
    have hsub : Icc s ρ ⊆ Icc s (stopEnd τ t ω) := Icc_subset_Icc le_rfl hρe
    have hbd := localizer_bounds hst hs hPω
    have hρmem : ρ ∈ Icc s ρ := ⟨hsρ, le_rfl⟩
    have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
    have hρe' : (ρ : ℝ) ≤ stopEnd τ t ω := by exact_mod_cast hρe
    refine ⟨hx.mono hsub, hβ.mono hsub, hj.mono hsub, ?_, fun u hu => hdec u (hsub hu),
      hmono.mono hsub, fun u v hu huv hv h => hsupp u v hu huv (hv.trans hρe) h,
      fun u hu => (hbd u hu).1, (hdom ρ (hsub hρmem)).trans (hbd ρ hρmem).2.2,
      (hbd ρ hρmem).2.1⟩
    exact hb.mono_set (uIcc_subset_uIcc_left (by
      rw [uIcc_of_le (hsρ'.trans hρe')]; exact ⟨hsρ', hρe'⟩))
  · have hρ : ρ = s := lifetimeOf_eq_of_not (A := fun u => ω ∈ localizer τ X J ψ s N u)
      localizer_antitone' hs
    rw [hρ]
    refine isTanakaPath_singleton ?_ hN
    simp only [cutoffProc, le_refl, true_and]
    split_ifs with h
    · simpa using hN
    · exact not_lt.1 (not_or.1 h).1

lemma s_le_stopEnd {ω : Ω} (hst : s ≤ t) (hsτ : (s : WithTop ℝ≥0) ≤ τ ω) : s ≤ stopEnd τ t ω :=
  le_stopEnd_iff.2 ⟨hst, hsτ⟩

/-- For `N` large the localized lifetime is the whole interval `[s, t ∧ τ]`. -/
lemma exists_lifetime_eq {ω : Ω} (hst : s ≤ t) (hsτ : (s : WithTop ℝ≥0) ≤ τ ω)
    (hP : IsTanakaPathOn a c s (stopEnd τ t ω) (X · ω) (B · ω) (J · ω) (b · ω) (ψ · ω)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      lifetime (localizer τ X J ψ s N) s t ω = stopEnd τ t ω ∧ ¬ ((N : ℝ) < |X s ω|) := by
  set e := stopEnd τ t ω
  have hse : s ≤ e := s_le_stopEnd hst hsτ
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hP.1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP.2.2.1.sub (continuousOn_const (c := J s ω)))
  obtain ⟨M3, hM3⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hP.2.2.2.1.sub (continuousOn_const (c := ψ s ω)))
  refine ⟨⌈max M1 (max M2 M3)⌉₊, fun N hN => ?_⟩
  have hNM : max M1 (max M2 M3) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h1 : M1 ≤ N := (le_max_left _ _).trans hNM
  have h2 : M2 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hNM
  have h3 : M3 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hNM
  have hXs : |X s ω| ≤ N := by
    have := hM1 s ⟨le_rfl, hse⟩; rw [Real.norm_eq_abs] at this; linarith
  refine ⟨le_antisymm (lifetime_localizer_le hst hsτ) ?_, not_lt.2 hXs⟩
  refine le_of_forall_lt_imp_le_of_dense fun u hu => ?_
  by_cases hus : u < s
  · exact hus.le.trans (le_lifetimeOf _ _ _)
  · refine le_lifetimeOf_of ((hu.le).trans (stopEnd_le τ t ω)) ?_
    simp only [localizer, hus, ite_false, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    refine ⟨⟨lt_of_lt_of_le (WithTop.coe_lt_coe.2 hu) (coe_stopEnd_le τ t ω), hXs⟩,
      fun q hq => ?_⟩
    have hq0 : (0 : ℝ) ≤ q := s.2.trans hq.1
    have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have hmem : (q : ℝ).toNNReal ∈ Icc s e := by
      refine ⟨?_, ?_⟩
      · rw [← NNReal.coe_le_coe, hqc]; exact hq.1
      · rw [← NNReal.coe_le_coe, hqc]; exact hq.2.trans (by exact_mod_cast hu.le)
    have a1 := hM1 _ hmem
    have a2 := hM2 _ hmem
    have a3 := hM3 _ hmem
    simp only [Real.norm_eq_abs, Pi.sub_apply] at a1 a2 a3
    exact ⟨a1.trans h1, (le_abs_self _).trans (a2.trans h2), (le_abs_self _).trans (a3.trans h3)⟩

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The zero set is Lebesgue-null up to a stopping time.** For `a ≠ 0`, almost surely the zero
set of `X` on `[s, t ∧ τ]` has Lebesgue measure zero. -/
theorem ae_volume_zeroSet_stopped (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hτ : IsStoppingTime 𝓕 τ) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (hJ : ∀ u, Measurable[𝓕 u] (J u)) (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (ha : a ≠ 0)
    (hP : ∀ᵐ ω ∂μ, (s : WithTop ℝ≥0) ≤ τ ω →
      IsTanakaPathOn a c s (stopEnd τ t ω) (X · ω) (B · ω) (J · ω) (b · ω) (ψ · ω)) :
    ∀ᵐ ω ∂μ, (s : WithTop ℝ≥0) ≤ τ ω → volume (zeroSet (X · ω) s (stopEnd τ t ω)) = 0 := by
  have hloc : ∀ N : ℕ, ∀ᵐ ω ∂μ, volume (zeroSet (cutoffProc X τ s N · ω) s
      (lifetime (localizer τ X J ψ s N) s t ω)) = 0 := fun N =>
    ae_volume_zeroSet_eq_zero hB hst (measurable_cutoffProc hτ hX)
      (measurableSet_localizer hτ hX hJ hψ) localizer_antitone ha
      (hP.mono fun ω h => isTanakaPath_cutoff (Nat.cast_nonneg N) hst h)
  filter_upwards [hP, ae_all_iff.2 hloc] with ω hPω hall hsτ
  rcases hsτ.lt_or_eq with hlt | heq
  · obtain ⟨N₀, hN₀⟩ := exists_lifetime_eq hst hsτ (hPω hsτ)
    obtain ⟨hρ, hX0⟩ := hN₀ N₀ le_rfl
    have := hall N₀
    rwa [hρ, show (cutoffProc X τ s N₀ · ω) = (X · ω) from
      funext (cutoffProc_eq hX0 (not_le.2 hlt))] at this
  · have he : stopEnd τ t ω = s :=
      le_antisymm (WithTop.coe_le_coe.1 ((coe_stopEnd_le τ t ω).trans heq.ge))
        (s_le_stopEnd hst hsτ)
    refine measure_mono_null (zeroSet_subset _ _ _) ?_
    rw [he, Real.volume_Icc, sub_self, ENNReal.ofReal_zero]

/-- **Zero right local time kills the singular push, up to a stopping time.** If moreover
`X ≥ 0` and `∫_s^u X⁻¹ ≤ ψ_u - ψ_s` on `[s, t ∧ τ]`, and `a ≠ 0`, `c ≠ 0`, then almost surely `J`
is constant on `[s, t ∧ τ]`. -/
theorem ae_singular_const_stopped (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hτ : IsStoppingTime 𝓕 τ) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (hJ : ∀ u, Measurable[𝓕 u] (J u)) (hψ : ∀ u, Measurable[𝓕 u] (ψ u)) (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hP : ∀ᵐ ω ∂μ, (s : WithTop ℝ≥0) ≤ τ ω →
      IsTanakaPathOn a c s (stopEnd τ t ω) (X · ω) (B · ω) (J · ω) (b · ω) (ψ · ω))
    (hnn : ∀ᵐ ω ∂μ, (s : WithTop ℝ≥0) ≤ τ ω → ∀ u ∈ Icc s (stopEnd τ t ω), 0 ≤ X u ω)
    (hrec : ∀ᵐ ω ∂μ, (s : WithTop ℝ≥0) ≤ τ ω →
      IntervalIntegrable (fun r : ℝ => (X r.toNNReal ω)⁻¹) volume s (stopEnd τ t ω) ∧
      ∀ u ∈ Icc s (stopEnd τ t ω), ∫ r in (s : ℝ)..u, (X r.toNNReal ω)⁻¹ ≤ ψ u ω - ψ s ω) :
    ∀ᵐ ω ∂μ, ∀ u : ℝ≥0, s ≤ u → u ≤ t → (u : WithTop ℝ≥0) ≤ τ ω → J u ω = J s ω := by
  have hloc : ∀ N : ℕ, ∀ᵐ ω ∂μ, J (lifetime (localizer τ X J ψ s N) s t ω) ω = J s ω := by
    intro N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine ae_singular_eq_of_isTanakaPath hB hst (measurable_cutoffProc hτ hX)
      (measurableSet_localizer hτ hX hJ hψ) localizer_antitone ha hc
      (hP.mono fun ω h => isTanakaPath_cutoff hN hst h) ?_ ?_
    · filter_upwards [hP, hnn] with ω hPω hω u hu
      by_cases hs : ω ∈ localizer τ X J ψ s (N : ℝ) s
      · have hs' := hs
        simp only [localizer, lt_irrefl, ite_false, mem_inter_iff, mem_ofPred_eq] at hs'
        obtain ⟨⟨hsτ, hXs⟩, _⟩ := hs'
        rw [cutoffProc_eq (not_lt.2 hXs) (not_le.2 hsτ)]
        exact hω hsτ.le u ⟨hu.1, hu.2.trans (lifetime_localizer_le hst hsτ.le)⟩
      · have hρ := lifetimeOf_eq_of_not (A := fun u => ω ∈ localizer τ X J ψ s (N : ℝ) u)
          localizer_antitone' (t := t) hs
        have hus : u = s := le_antisymm (hu.2.trans_eq hρ) hu.1
        subst hus
        simp only [cutoffProc, le_refl, true_and]
        split_ifs with h
        · exact le_rfl
        · push Not at h
          exact hω (le_of_lt h.2) u ⟨le_rfl, s_le_stopEnd hst (le_of_lt h.2)⟩
    · filter_upwards [hP, hrec] with ω hPω hr
      by_cases hs : ω ∈ localizer τ X J ψ s (N : ℝ) s
      · have hs' := hs
        simp only [localizer, lt_irrefl, ite_false, mem_inter_iff, mem_ofPred_eq] at hs'
        obtain ⟨⟨hsτ, hXs⟩, _⟩ := hs'
        have hcut : (fun r : ℝ => (cutoffProc X τ s N r.toNNReal ω)⁻¹) =
            fun r : ℝ => (X r.toNNReal ω)⁻¹ := funext fun r => by
          rw [cutoffProc_eq (not_lt.2 hXs) (not_le.2 hsτ)]
        rw [hcut]
        obtain ⟨hri, hrb⟩ := hr hsτ.le
        set ρ := lifetime (localizer τ X J ψ s (N : ℝ)) s t ω
        have hρe := lifetime_localizer_le (X := X) (J := J) (ψ := ψ) (N := (N : ℝ)) hst hsτ.le
        have hsρ : s ≤ ρ := le_lifetimeOf _ _ _
        have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
        have hρe' : (ρ : ℝ) ≤ stopEnd τ t ω := by exact_mod_cast hρe
        refine ⟨hri.mono_set (uIcc_subset_uIcc_left (by
          rw [uIcc_of_le (hsρ'.trans hρe')]; exact ⟨hsρ', hρe'⟩)), ?_⟩
        exact (hrb ρ ⟨hsρ, hρe⟩).trans
          (localizer_bounds hst hs (hPω hsτ.le) ρ ⟨hsρ, le_rfl⟩).2.2
      · have hρ := lifetimeOf_eq_of_not (A := fun u => ω ∈ localizer τ X J ψ s (N : ℝ) u)
          localizer_antitone' (t := t) hs
        simp only [lifetime] at hρ ⊢
        rw [hρ]
        exact ⟨IntervalIntegrable.refl, by simp [hN]⟩
  filter_upwards [hP, ae_all_iff.2 hloc] with ω hPω hall u hsu hut huτ
  have hsτ : (s : WithTop ℝ≥0) ≤ τ ω := (WithTop.coe_le_coe.2 hsu).trans huτ
  have hue : u ≤ stopEnd τ t ω := le_stopEnd_iff.2 ⟨hut, huτ⟩
  obtain ⟨N₀, hN₀⟩ := exists_lifetime_eq hst hsτ (hPω hsτ)
  have hJe : J (stopEnd τ t ω) ω = J s ω := (hN₀ N₀ le_rfl).1 ▸ hall N₀
  have hmono := (hPω hsτ).2.2.2.2.2.2.1
  have hse := s_le_stopEnd hst hsτ
  have h1 := hmono ⟨le_rfl, hse⟩ ⟨hsu, hue⟩ hsu
  have h2 := hmono ⟨hsu, hue⟩ ⟨hse, le_rfl⟩ hue
  linarith

end InteractingSLE.LocalTime
