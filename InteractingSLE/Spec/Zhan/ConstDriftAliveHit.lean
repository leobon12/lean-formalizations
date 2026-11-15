/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftAliveProc

/-!
# The lower strip gap does not reach `0` (`κ ≤ 4`, `σ ≤ 1`)

Packet PROVE-ZHAN-A8. With the stopped Lyapunov bound of `ConstDriftAliveProc.lean`:

* **Markov** (`measureReal_lyap_le`): `P(lyap(X_σ) ≥ lyap δ) ≤ (lyap q − lyap R)/(lyap δ − lyap R)`, because
  `lyap(X_σ) ≥ lyap R` (`X_σ ≤ R` on the keep set, `lyap` antitone);
* **pathwise** (`lyap_le_lgStopped_of_hit`): if the tamed gap at level `c = 1/(n+1)` reaches `c` at a time `t ≤ n`
  while staying below `R` and in the ball of radius `n`, then the localizing time exits through the inner boundary, so
  `X_σ ≤ (1 + √κ)/(n+1) = δ_n` and `lyap(X_σ) ≥ lyap δ_n`;
* **uniform bounds** (`le_of_eq_integral`): `X ≤ max(q, 1) + 2 sup|ξ| + C(1) T` on `[0, T]`, for every taming level
  `c ≤ 1` (last-exit argument), and `0 ≤ Λ` (the tamed drift is `≥ 1 ≥ σ`);
* **conclusion** (`ae_exists_pos_lgProc`): almost surely, for every horizon `T` some taming level `1/(n+1)` is never
  reached on `[0, T]` (since `lyap δ_n → ∞`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace LowerGap

open Sec4 (cothHalf)

/-! ### A deterministic upper bound (last exit) -/

/-- If `X_t = X_0 − ξ_t + ∫₀ᵗ F(X)` on `[0, T]`, `X_0 ≤ A`, `F ≤ C` on `[A, ∞)` and `|ξ| ≤ D`, then `X ≤ A + 2D + CT`
on `[0, T]`. -/
theorem le_of_eq_integral {X ξ F : ℝ → ℝ} {T A C D : ℝ} (hC : 0 ≤ C) (hXc : ContinuousOn X (Icc 0 T))
    (hFc : Continuous F) (hX0 : X 0 ≤ A) (hF : ∀ x, A ≤ x → F x ≤ C) (hξ : ∀ t ∈ Icc 0 T, |ξ t| ≤ D)
    (hX : ∀ t ∈ Icc 0 T, X t = X 0 - ξ t + ∫ r in (0 : ℝ)..t, F (X r)) :
    ∀ t ∈ Icc 0 T, X t ≤ A + 2 * D + C * T := by
  intro t ht
  by_contra hlt
  push Not at hlt
  set S : Set ℝ := Icc 0 t ∩ X ⁻¹' Iic A with hS
  have hSc : IsClosed S :=
    (hXc.mono (Icc_subset_Icc le_rfl ht.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht.1⟩, hX0⟩
  have hSb : BddAbove S := ⟨t, fun r hr => hr.1.2⟩
  set a := sSup S with ha
  have haS : a ∈ S := hSc.csSup_mem ⟨0, hS0⟩ hSb
  have hat : a ≤ t := haS.1.2
  have ha0 : 0 ≤ a := haS.1.1
  have hT : ∀ r ∈ Icc a t, r ∈ Icc 0 T := fun r hr => ⟨ha0.trans hr.1, hr.2.trans ht.2⟩
  -- on `(a, t)` the path is above `A`
  have habove : ∀ r ∈ Ioo a t, A ≤ X r := by
    intro r hr
    by_contra hr'
    have : r ∈ S := ⟨⟨ha0.trans hr.1.le, hr.2.le⟩, (not_le.1 hr').le⟩
    exact absurd (le_csSup hSb this) (not_le.2 hr.1)
  have hcont : ContinuousOn (fun r => F (X r)) (Icc 0 T) := hFc.comp_continuousOn hXc
  have hint : ∀ u ∈ Icc 0 T, IntervalIntegrable (fun r => F (X r)) volume 0 u := fun u hu =>
    (hcont.mono (uIcc_subset_Icc ⟨le_rfl, hu.1.trans hu.2⟩ hu)).intervalIntegrable
  have hsub : (∫ r in (0 : ℝ)..t, F (X r)) - ∫ r in (0 : ℝ)..a, F (X r) = ∫ r in a..t, F (X r) :=
    intervalIntegral.integral_interval_sub_left (hint t ht) (hint a (hT a ⟨le_rfl, hat⟩))
  have hle : ∫ r in a..t, F (X r) ≤ ∫ r in a..t, C :=
    intervalIntegral.integral_mono_on_of_le_Ioo hat
      ((hcont.mono fun r hr => hT r (by rwa [uIcc_of_le hat] at hr)).intervalIntegrable)
      intervalIntegrable_const fun r hr => hF _ (habove r hr)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  have h1 := hX t ht
  have h2 := hX a (hT a ⟨le_rfl, hat⟩)
  have h3 := (abs_le.1 (hξ t ht))
  have h4 := (abs_le.1 (hξ a (hT a ⟨le_rfl, hat⟩)))
  have h5 : (t - a) * C ≤ T * C := mul_le_mul_of_nonneg_right (by linarith [ht.2]) hC
  have h6 : X a ≤ A := haS.2
  nlinarith

/-! ### Markov's inequality and the pathwise hit -/

section Hit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ σ q c R a : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {n : ℕ}

theorem continuous_pathX_lg (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) :
    Continuous fun t => pathX (lgDrift κ σ q c B) B t ω :=
  (lgDrift_facts hc hBc).1.prodMk hBc

theorem lgStop_eq (ω : Ω) : lgStop κ σ q c R B n ω =
    hittingBtwn (pathX (lgDrift κ σ q c B) B) (exitSet (lgRegion κ q) (lgCoord κ q) R n) 0 n ω := by
  simp [lgStop, locStop]

theorem pathX_lgStop_mem_keepSet (hc : 0 < c) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hX0 : ((0 : ℝ), (0 : ℝ)) ∉ exitSet (lgRegion κ q) (lgCoord κ q) R n) (ω : Ω) :
    pathX (lgDrift κ σ q c B) B (lgStop κ σ q c R B n ω) ω ∈ keepSet (lgRegion κ q) (lgCoord κ q) R n :=
  pathX_mem_keepSet (G := univ) hBc continuous_lgCoord.continuousOn
    (fun ω => (lgDrift_facts hc (hBc ω)).1) lgDrift_zero hB0 hX0 le_rfl

theorem lgStopped_mem (hc : 0 < c) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hX0 : ((0 : ℝ), (0 : ℝ)) ∉ exitSet (lgRegion κ q) (lgCoord κ q) R n) (ω : Ω) :
    0 < lgStopped κ σ q c R B n ω ∧ lgStopped κ σ q c R B n ω ≤ R := by
  have hk := pathX_lgStop_mem_keepSet (σ := σ) hc hBc hB0 hX0 ω
  exact ⟨keepSet_subset hk, (lgCoord_ge_of_mem_keepSet hk).2⟩

/-- **Markov's inequality for the stopped Lyapunov value.** -/
theorem measureReal_lyap_le [IsProbabilityMeasure P] (hB : IsFilteredBrownianReal 𝓖 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) (hσ : σ ≤ 1)
    (ha : 0 ≤ a) (ha' : κ / 2 - 1 + σ ≤ 2 * a) (hc : 0 < c) (hcn : c ≤ 1 / ((n : ℝ) + 1))
    (hX0 : ((0 : ℝ), (0 : ℝ)) ∉ exitSet (lgRegion κ q) (lgCoord κ q) R n) {δ : ℝ}
    (hδ : lyap a R < lyap a δ) :
    P.real {ω | lyap a δ ≤ lyap a (lgStopped κ σ q c R B n ω)} ≤
      (lyap a q - lyap a R) / (lyap a δ - lyap a R) := by
  obtain ⟨hint, hle⟩ := integral_lyap_lgStopped_le hB hBc hB0 hκ0 hκ hσ ha ha' hc hcn hX0
  set Z : Ω → ℝ := fun ω => lyap a (lgStopped κ σ q c R B n ω) - lyap a R with hZ
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by
    obtain ⟨h1, h2⟩ := lgStopped_mem (σ := σ) hc hBc hB0 hX0 ω
    exact sub_nonneg.2 (lyap_antitoneOn ha h1 h2)
  have hZint : Integrable Z P := hint.sub (integrable_const _)
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (Eventually.of_forall hZ0) hZint
    (lyap a δ - lyap a R)
  have hEZ : ∫ ω, Z ω ∂P = (∫ ω, lyap a (lgStopped κ σ q c R B n ω) ∂P) - lyap a R := by
    rw [hZ, integral_sub hint (integrable_const _), integral_const]
    simp
  have hset : {x | lyap a δ - lyap a R ≤ Z x} = {ω | lyap a δ ≤ lyap a (lgStopped κ σ q c R B n ω)} := by
    ext ω; simp [hZ]
  rw [hset, hEZ] at hm
  rw [le_div_iff₀ (sub_pos.2 hδ)]
  linarith

/-- **The pathwise hit.** If the tamed gap at level `c = 1/(n+1)` reaches `c` at a time `t ≤ n` while staying below
`R` and in the ball of radius `n`, then `lyap(X_σ) ≥ lyap((1 + √κ)/(n+1))`. -/
theorem lyap_le_lgStopped_of_hit (hc : c = 1 / ((n : ℝ) + 1)) (ha : 0 ≤ a) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hX0 : ((0 : ℝ), (0 : ℝ)) ∉ exitSet (lgRegion κ q) (lgCoord κ q) R n) {ω : Ω}
    {t : ℝ≥0} (htn : t ≤ n) (hXt : lgProc κ σ q c B t ω ≤ c)
    (hbd : ∀ r ≤ t, lgProc κ σ q c B r ω < R ∧ ‖pathX (lgDrift κ σ q c B) B r ω‖ < n) :
    lyap a ((1 + Real.sqrt κ) / ((n : ℝ) + 1)) ≤ lyap a (lgStopped κ σ q c R B n ω) := by
  have hc0 : 0 < c := by rw [hc]; positivity
  set U := lgRegion κ q
  set E := exitSet U (lgCoord κ q) R n with hEdef
  have hcont := continuous_pathX_lg (κ := κ) (σ := σ) (q := q) hc0 (hBc ω)
  have hmemt : pathX (lgDrift κ σ q c B) B t ω ∈ E := by
    left
    by_cases hU : pathX (lgDrift κ σ q c B) B t ω ∈ U
    · refine (infDist_le_lgCoord hU).trans ?_
      rw [lgCoord_pathX, ← hc]; exact hXt
    · rw [Metric.infDist_zero_of_mem hU]; positivity
  have hσt : lgStop κ σ q c R B n ω ≤ t := by
    rw [lgStop_eq]; exact hittingBtwn_le_of_mem zero_le htn hmemt
  have hmemσ : pathX (lgDrift κ σ q c B) B (lgStop κ σ q c R B n ω) ω ∈ E := by
    rw [lgStop_eq]
    exact mem_of_hittingBtwn hcont (isClosed_exitSet continuous_lgCoord.continuousOn) ⟨t, ⟨zero_le, htn⟩, hmemt⟩
  obtain ⟨hR, hN⟩ := hbd _ hσt
  have hinf : Metric.infDist (pathX (lgDrift κ σ q c B) B (lgStop κ σ q c R B n ω) ω) Uᶜ ≤
      1 / ((n : ℝ) + 1) := by
    rcases hmemσ with h | h | h
    · exact h
    · exact absurd h (not_le.2 hN)
    · rw [lgCoord_pathX] at h; exact absurd h.2 (not_le.2 hR)
  have hpos := (lgStopped_mem (σ := σ) hc0 hBc hB0 hX0 ω).1
  have hle : lgStopped κ σ q c R B n ω ≤ (1 + Real.sqrt κ) / ((n : ℝ) + 1) := by
    have := lgCoord_le_infDist (κ := κ) (q := q) (pathX (lgDrift κ σ q c B) B (lgStop κ σ q c R B n ω) ω)
    rw [lgStopped]
    calc _ ≤ (1 + Real.sqrt κ) * Metric.infDist _ Uᶜ := this
      _ ≤ (1 + Real.sqrt κ) * (1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hinf (by positivity)
      _ = _ := by ring
  exact lyap_antitoneOn ha hpos hle

end Hit


/-! ### Uniform bounds and the almost sure conclusion -/

section Ae

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ σ q c : ℝ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The taming level `1/(n+1)`. -/
def lvl (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem lvl_pos (n : ℕ) : 0 < lvl n := by unfold lvl; positivity

theorem lvl_le_one (n : ℕ) : lvl n ≤ 1 := by
  unfold lvl
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The tamed gap solves `X_t = q − (√κ B_t + σ t) + ∫₀ᵗ C(max(X, c))`. -/
theorem lgProc_eq (hc : 0 < c) {ω : Ω} (hBc : Continuous (B · ω)) (t : ℝ) (ht : 0 ≤ t) :
    lgProc κ σ q c B t.toNNReal ω = q - (Real.sqrt κ * B t.toNNReal ω + σ * t) +
      ∫ r in (0 : ℝ)..t, tame c (lgProc κ σ q c B r.toNNReal ω) := by
  have h := (lgDrift_facts (κ := κ) (σ := σ) (q := q) hc hBc).2 t.toNNReal
  rw [Real.coe_toNNReal t ht] at h
  have hint : IntervalIntegrable (fun r : ℝ => tame c (lgProc κ σ q c B r.toNNReal ω)) volume 0 t :=
    ((lipschitzWith_tame hc).continuous.comp ((continuous_lgProc hc hBc).comp
      continuous_real_toNNReal)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at h
  rw [lgProc, h]
  ring

theorem lgDrift_nonneg (hc : 0 < c) (hσ : σ ≤ 1) {ω : Ω} (hBc : Continuous (B · ω)) (t : ℝ≥0) :
    0 ≤ lgDrift κ σ q c B t ω := by
  rw [(lgDrift_facts hc hBc).2 t]
  refine intervalIntegral.integral_nonneg t.coe_nonneg fun r _ => ?_
  have := one_le_tame hc (lgProc κ σ q c B r.toNNReal ω)
  linarith

/-- **Uniform bounds** on `[0, T]` for every taming level `1/(n+1)`. -/
theorem exists_unif_bound (hσ : σ ≤ 1) (hq : 0 < q) {ω : Ω} (hBc : Continuous (B · ω)) (hB0 : B 0 ω = 0)
    (T : ℝ≥0) : ∃ R M : ℕ, q < R ∧ ∀ n : ℕ, ∀ t ≤ T, lgProc κ σ q (lvl n) B t ω < R ∧
      ‖pathX (lgDrift κ σ q (lvl n) B) B t ω‖ < M := by
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn hBc.continuousOn
  set MB := max C0 0 with hMB
  have hMB0 : 0 ≤ MB := le_max_right _ _
  have hBb : ∀ t ≤ T, |B t ω| ≤ MB := fun t ht =>
    (by simpa using hC0 t ⟨zero_le, ht⟩ : |B t ω| ≤ C0).trans (le_max_left _ _)
  set D := Real.sqrt κ * MB + |σ| * T with hD
  set K := max q 1 + 2 * D + cothHalf 1 * T with hK
  have hC1 : 0 ≤ cothHalf 1 := zero_le_one.trans (Sec4.one_le_cothHalf one_pos)
  have hD0 : 0 ≤ D := by positivity
  have hXb : ∀ n : ℕ, ∀ t ≤ T, lgProc κ σ q (lvl n) B t ω ≤ K := by
    intro n t ht
    have hc := lvl_pos n
    set X : ℝ → ℝ := fun r => lgProc κ σ q (lvl n) B r.toNNReal ω with hXdef
    have hXc : ContinuousOn X (Icc 0 (T : ℝ)) :=
      ((continuous_lgProc hc hBc).comp continuous_real_toNNReal).continuousOn
    have hX0 : X 0 = q := by simp [hXdef, lgProc, hB0, lgDrift_zero]
    have hF : ∀ x, max q 1 ≤ x → tame (lvl n) x ≤ cothHalf 1 := by
      intro x hx
      have h1 : 1 ≤ x := (le_max_right _ _).trans hx
      rw [tame_of_le ((lvl_le_one n).trans h1)]
      exact Sec4.cothHalf_le_cothHalf one_pos h1
    have hξ : ∀ r ∈ Icc (0 : ℝ) T, |Real.sqrt κ * B r.toNNReal ω + σ * r| ≤ D := by
      intro r hr
      have hrT : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hr.2
      have h1 := hBb _ hrT
      have h2 : |σ * r| ≤ |σ| * T := by
        rw [abs_mul, abs_of_nonneg hr.1]; exact mul_le_mul_of_nonneg_left hr.2 (abs_nonneg σ)
      calc |Real.sqrt κ * B r.toNNReal ω + σ * r| ≤ |Real.sqrt κ * B r.toNNReal ω| + |σ * r| := abs_add_le _ _
        _ ≤ Real.sqrt κ * MB + |σ| * T := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg κ)) h2
    have hXeq : ∀ r ∈ Icc (0 : ℝ) T, X r = X 0 - (Real.sqrt κ * B r.toNNReal ω + σ * r) +
        ∫ u in (0 : ℝ)..r, tame (lvl n) (X u) := by
      intro r hr
      rw [hX0]
      exact lgProc_eq hc hBc r hr.1
    have key := le_of_eq_integral (ξ := fun r => Real.sqrt κ * B r.toNNReal ω + σ * r) hC1 hXc
      (lipschitzWith_tame hc).continuous (hX0.le.trans (le_max_left q 1)) hF hξ hXeq (t : ℝ)
      ⟨t.coe_nonneg, by exact_mod_cast ht⟩
    have e : X t = lgProc κ σ q (lvl n) B t ω := by simp only [hXdef, Real.toNNReal_coe]
    rw [← e]
    exact key
  have hKq : q ≤ K := by
    have := le_max_left q 1
    have : 0 ≤ cothHalf 1 * (T : ℝ) := by positivity
    linarith
  refine ⟨⌈K⌉₊ + 1, ⌈max (K + Real.sqrt κ * MB) MB⌉₊ + 1, ?_, fun n t ht => ⟨?_, ?_⟩⟩
  · have := Nat.le_ceil K; push_cast; linarith
  · have := Nat.le_ceil K; push_cast; linarith [hXb n t ht]
  · have hc := lvl_pos n
    have hΛ0 := lgDrift_nonneg (κ := κ) (q := q) hc hσ hBc t
    have hΛ : lgDrift κ σ q (lvl n) B t ω ≤ K + Real.sqrt κ * MB := by
      have h1 := hXb n t ht
      have h2 := hBb t ht
      have h3 : B t ω ≤ MB := (abs_le.1 h2).2
      have h4 : Real.sqrt κ * B t ω ≤ Real.sqrt κ * MB := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg κ)
      simp only [lgProc] at h1
      linarith
    have hmax := Nat.le_ceil (max (K + Real.sqrt κ * MB) MB)
    have hn : ‖pathX (lgDrift κ σ q (lvl n) B) B t ω‖ ≤ max (K + Real.sqrt κ * MB) MB := by
      rw [pathX, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ0]
      exact max_le_max hΛ (hBb t ht)
    push_cast
    linarith

variable [IsProbabilityMeasure P]

/-- **The lower gap does not reach `0`**: almost surely, for every horizon `T` some taming level `1/(n+1)` is never
reached by the tamed gap on `[0, T]` (so that gap is a positive solution of the untamed equation there). -/
theorem ae_exists_pos_lgProc (hB : IsFilteredBrownianReal 𝓖 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 4) (hσ : σ ≤ 1) (hq : 0 < q) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ n : ℕ, ∀ t : ℝ≥0, t ≤ T → lvl n < lgProc κ σ q (lvl n) B t ω := by
  set a := max 0 ((1 + σ) / 2) with hadef
  have ha : 0 ≤ a := le_max_left _ _
  have ha' : κ / 2 - 1 + σ ≤ 2 * a := by
    rcases le_total (-1) σ with h | h
    · have : (1 + σ) / 2 ≤ a := le_max_right _ _
      linarith
    · linarith
  rw [ae_all_iff]
  intro T
  rw [ae_iff]
  set S : ℕ → ℕ → Set Ω := fun R M => {ω | (∀ n : ℕ, ∃ t : ℝ≥0, t ≤ T ∧ lgProc κ σ q (lvl n) B t ω ≤ lvl n) ∧
    q < R ∧ ∀ n : ℕ, ∀ t ≤ (T : ℝ≥0), lgProc κ σ q (lvl n) B t ω < R ∧
      ‖pathX (lgDrift κ σ q (lvl n) B) B t ω‖ < M} with hSdef
  have hsub : {ω | ¬ ∃ n : ℕ, ∀ t : ℝ≥0, t ≤ T → lvl n < lgProc κ σ q (lvl n) B t ω} ⊆ ⋃ R, ⋃ M, S R M := by
    intro ω hω
    simp only [mem_ofPred_eq, not_exists, not_forall, not_lt, exists_prop] at hω
    obtain ⟨R, M, hqR, hb⟩ := exists_unif_bound (κ := κ) hσ hq (hBc ω) (hB0 ω) (T : ℝ≥0)
    exact mem_iUnion.2 ⟨R, mem_iUnion.2 ⟨M, hω, hqR, hb⟩⟩
  refine measure_mono_null hsub (measure_iUnion_null fun R => measure_iUnion_null fun M => ?_)
  by_cases hqR : q < R
  swap
  · have : S R M = ∅ := by
      ext ω; simp only [hSdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hqR h.2.1
    rw [this, measure_empty]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := hε
  set K₂ := a + lyap a R + (lyap a q - lyap a R) / ε + 1 with hK₂
  have hlim : Tendsto (fun n : ℕ => (1 + Real.sqrt κ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 + Real.sqrt κ)
  have hm : (0 : ℝ) < min (min q 1) (Real.exp (-K₂)) := lt_min (lt_min hq one_pos) (Real.exp_pos _)
  obtain ⟨n, hnδ, hnN⟩ := ((hlim.eventually (gt_mem_nhds hm)).and
    (eventually_ge_atTop (max (max T M) 1))).exists
  set δ := (1 + Real.sqrt κ) / ((n : ℝ) + 1) with hδdef
  have hδeq : (1 + Real.sqrt κ) * (1 / ((n : ℝ) + 1)) = δ := by rw [hδdef]; ring
  rw [hδeq] at hnδ
  have hδq : δ < q := hnδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hnδ.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδK : δ ≤ Real.exp (-K₂) := hnδ.le.trans (min_le_right _ _)
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hnT : T ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hnN)
  have hnM : M ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hnN)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hnN
  -- `lyap δ` is large
  have hlog : K₂ ≤ -Real.log δ := by
    have := Real.log_le_log hδ0 hδK
    rw [Real.log_exp] at this
    linarith
  have hlyδ : lyap a R + (lyap a q - lyap a R) / ε + 1 ≤ lyap a δ := by
    have h1 := neg_log_le_lyap a hδ0
    have h2 : a * δ ≤ a := by nlinarith
    linarith
  have hqR' : lyap a R ≤ lyap a q := lyap_antitoneOn ha hq hqR.le
  have hdiv0 : 0 ≤ (lyap a q - lyap a R) / ε := div_nonneg (by linarith) hε'.le
  have hRδ : lyap a R < lyap a δ := by linarith
  -- the exit point
  have hX0 : ((0 : ℝ), (0 : ℝ)) ∉ exitSet (lgRegion κ q) (lgCoord κ q) R n := by
    rintro (h | h | h)
    · have h1 := lgCoord_le_infDist (κ := κ) (q := q) ((0 : ℝ), (0 : ℝ))
      rw [lgCoord_zero] at h1
      have h2 : (1 + Real.sqrt κ) * Metric.infDist ((0 : ℝ), (0 : ℝ)) (lgRegion κ q)ᶜ ≤
          (1 + Real.sqrt κ) * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left h (by positivity)
      rw [hδeq] at h2
      linarith
    · simp only [Prod.norm_def, norm_zero, max_self] at h
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    · rw [lgCoord_zero] at h
      exact absurd h.2 (not_le.2 hqR)
  -- inclusion in the Markov event
  have hincl : S R M ⊆ {ω | lyap a δ ≤ lyap a (lgStopped κ σ q (lvl n) R B n ω)} := by
    intro ω hω
    obtain ⟨hhit, -, hb⟩ := hω
    obtain ⟨t, htT, ht⟩ := hhit n
    refine lyap_le_lgStopped_of_hit rfl ha hBc hB0 hX0 (htT.trans (by exact_mod_cast hnT)) ht
      fun r hr => ⟨(hb n r (hr.trans htT)).1, (hb n r (hr.trans htT)).2.trans_le (by exact_mod_cast hnM)⟩
  have hmk := measureReal_lyap_le (κ := κ) (σ := σ) (q := q) (n := n) hB hBc hB0 hκ0 hκ hσ ha ha' (lvl_pos n)
    le_rfl hX0 hRδ
  have hratio : (lyap a q - lyap a R) / (lyap a δ - lyap a R) ≤ ε := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : (lyap a q - lyap a R) / ε * ε = lyap a q - lyap a R := div_mul_cancel₀ _ hε'.ne'
    nlinarith
  calc P (S R M) ≤ P {ω | lyap a δ ≤ lyap a (lgStopped κ σ q (lvl n) R B n ω)} := measure_mono hincl
    _ = ENNReal.ofReal (P.real {ω | lyap a δ ≤ lyap a (lgStopped κ σ q (lvl n) R B n ω)}) :=
        (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (hmk.trans hratio)
    _ = ε := ENNReal.ofReal_coe_nnreal

end Ae

end LowerGap

end Zhan

end InteractingSLE
