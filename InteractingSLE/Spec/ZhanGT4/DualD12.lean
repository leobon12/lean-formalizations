/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD11
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Zhan's A.1.4, (D12): the patched density as a concatenation of one-curve martingales

Packet PROVE-ZHAN-GT4-A13. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L380–L407, R38):
"For a time `I ≤ t̄` known at a stopping time `R`, the process `M(R + s, I)` … is a local martingale in `s` … On each
`[R_{k−1}, R_k]` [the ratio of (D11) to its value at `R_{k−1}`] is `M(s, I_k)/M(R_{k−1}, I_k)`. After at most `n` such
intervals it is constant. Thus `M*(s, t̄)` is a bounded martingale."

## The normalization

The density is taken with respect to two **ordinary** curves, as in A8–A12: `Ñ(s, t) = M̃(s, t)/M̃(0, 0)` and
`M = Ñ(s, t)/(Ñ(s, 0) Ñ(0, t))` ((D6)), so `M(·, 0) = M(0, ·) = 1`. With `L = log Ñ`, `m = log M = L(x, y) − L(x, 0) −
L(0, y) + L(0, 0)`. With the other curve frozen at a deterministic height `h`, A8 (`martingale_MTilde_stopped`) makes
`s ↦ Ñ(s ∧ S, h)/Ñ(0, h)` a martingale of the growing curve. The marginal factor `D₁(s) = Ñ(s ∧ max C, 0)/Ñ(0, 0)` is the
density of the marginal force law of curve `1` with respect to the ordinary one.

## Main results

* `patchLog_add_marginal` (deterministic): `log M*(s, t) + log D₁(s) = ∑_c (L(c ∧ s, h c ∧ t) − L(prev c ∧ s, h c ∧ t))`:
  **in the ordinary base the patched density is a product, over the columns, of ratios of the frozen-height
  quantities `Ñ(·, h)` that A8 makes martingales** (the `Ñ(0, h)` factors cancel inside each column, the marginal factors
  telescope);
* `Martingale.switch` (stochastic): **switching, at a stopping time `σ`, from a martingale `X` to the ratio
  `Y_j(· ∧ τ)/Y_j(σ)` of a predictably chosen positive bounded martingale `Y_j` of a finite family gives a martingale**
  — the step "`M(R + s, I)` with `I` known at `R`" of (D12), applied column by column.
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### The patched density in the ordinary base -/

section Deterministic

variable {ι : Type*} [Fintype ι] {S₁ S₂ : ι → ℝ}

/-- The normalized two-parameter log-density `m = log M` of a log-density `L = log Ñ` ((D6)). -/
def normLog (L : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := L x y - L x 0 - L 0 y + L 0 0

theorem normLog_zero_left (L : ℝ → ℝ → ℝ) (y : ℝ) : normLog L 0 y = 0 := by unfold normLog; ring

theorem normLog_zero_right (L : ℝ → ℝ → ℝ) (x : ℝ) : normLog L x 0 = 0 := by unfold normLog; ring

/-- **The patched density times the marginal factor is a product of column ratios** (log form): with `m = normLog L`,
`log M*(s, t) + (L(max C ∧ s, 0) − L(0, 0)) = ∑_c (L(c ∧ s, h c ∧ t) − L(prev c ∧ s, h c ∧ t))`. -/
theorem patchLog_add_marginal (hS₁ : ∀ i, 0 ≤ S₁ i) (L : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    patchLog S₁ S₂ (normLog L) s t + (L (min (maxIn (stairCols S₁)) s) 0 - L 0 0) =
      ∑ c ∈ stairCols S₁, (L (min c s) (min (stairH S₁ S₂ c) t) -
        L (min (prevIn (stairCols S₁) c) s) (min (stairH S₁ S₂ c) t)) := by
  have hC : ∀ c ∈ stairCols S₁, 0 ≤ c := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    exact hS₁ i
  have htel := sum_sub_prevIn (stairCols S₁) hC fun c => L (min c s) 0
  simp only [min_eq_left hs] at htel
  unfold patchLog normLog
  rw [← htel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The same identity for the densities**: with `M = Ñ(x, y)Ñ(0, 0)/(Ñ(x, 0)Ñ(0, y))` for a positive `Ñ`,
`M*(s, t) · Ñ(max C ∧ s, 0)/Ñ(0, 0) = ∏_c Ñ(c ∧ s, h c ∧ t)/Ñ(prev c ∧ s, h c ∧ t)`. -/
theorem patch_mul_marginal (hS₁ : ∀ i, 0 ≤ S₁ i) {N : ℝ → ℝ → ℝ} (hN : ∀ x y, 0 < N x y) {s : ℝ} (hs : 0 ≤ s)
    (t : ℝ) :
    patch S₁ S₂ (fun x y => N x y * N 0 0 / (N x 0 * N 0 y)) s t * (N (min (maxIn (stairCols S₁)) s) 0 / N 0 0) =
      ∏ c ∈ stairCols S₁, (N (min c s) (min (stairH S₁ S₂ c) t) /
        N (min (prevIn (stairCols S₁) c) s) (min (stairH S₁ S₂ c) t)) := by
  set L : ℝ → ℝ → ℝ := fun x y => Real.log (N x y) with hL
  have hlog : (fun x y => Real.log (N x y * N 0 0 / (N x 0 * N 0 y))) = normLog L := by
    funext x y
    have h1 := hN x y; have h2 := hN 0 0; have h3 := hN x 0; have h4 := hN 0 y
    simp only [normLog, hL]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h2.ne', Real.log_mul h3.ne' h4.ne']
    ring
  have h := patchLog_add_marginal (S₂ := S₂) hS₁ L hs t
  unfold patch
  rw [hlog]
  have hprod : ∏ c ∈ stairCols S₁, (N (min c s) (min (stairH S₁ S₂ c) t) /
      N (min (prevIn (stairCols S₁) c) s) (min (stairH S₁ S₂ c) t)) =
      Real.exp (∑ c ∈ stairCols S₁, (L (min c s) (min (stairH S₁ S₂ c) t) -
        L (min (prevIn (stairCols S₁) c) s) (min (stairH S₁ S₂ c) t))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [hL]
    rw [Real.exp_sub, Real.exp_log (hN _ _), Real.exp_log (hN _ _)]
  have hmarg : N (min (maxIn (stairCols S₁)) s) 0 / N 0 0 =
      Real.exp (L (min (maxIn (stairCols S₁)) s) 0 - L 0 0) := by
    simp only [hL]
    rw [Real.exp_sub, Real.exp_log (hN _ _), Real.exp_log (hN _ _)]
  rw [hprod, hmarg, ← Real.exp_add, h]

end Deterministic

/-! ### Optional sampling with bounded multipliers -/

section Stoch

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- **Optional sampling against a bounded `𝓕_σ`-measurable multiplier**: for a right-continuous martingale `M`, bounded
stopping times `σ ≤ τ` and a bounded `𝓕_σ`-measurable `g`, `E[g M_τ] = E[g M_σ]`. -/
theorem integral_mul_stoppedValue_eq [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hMrc : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t) {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ)
    (hτ : IsStoppingTime 𝓕 τ) (hle : σ ≤ τ) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) {g : Ω → ℝ}
    (hg : StronglyMeasurable[hσ.measurableSpace] g) {K : ℝ} (hgK : ∀ ω, |g ω| ≤ K) :
    ∫ ω, g ω * stoppedValue M τ ω ∂P = ∫ ω, g ω * stoppedValue M σ ω ∂P := by
  have hm := hσ.measurableSpace_le
  have hce := InteractingSLE.Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hM hMrc hσ hτ hle hτT
  have hiτ : Integrable (stoppedValue M τ) P :=
    (tendsto_lintegral_stoppedValue_dyadicUpperTime hM.supermartingale hMrc hτ hτT).2.1
  have hgm : AEStronglyMeasurable g P := (hg.mono hm).aestronglyMeasurable
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ K := Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgK ω
  have hint : Integrable (g * stoppedValue M τ) P := hiτ.bdd_mul hgm hgb
  have h1 : ∫ ω, g ω * stoppedValue M τ ω ∂P = ∫ ω, (P[g * stoppedValue M τ | hσ.measurableSpace]) ω ∂P :=
    (integral_condExp hm).symm
  rw [h1, integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg hint hiτ)]
  refine integral_congr_ae ?_
  filter_upwards [hce] with ω hω
  simp only [Pi.mul_apply, hω]

/-- A bounded strongly measurable function is integrable for a finite measure. -/
theorem integrable_of_abs_le [IsFiniteMeasure P] {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {K : ℝ}
    (hK : ∀ ω, |f ω| ≤ K) : Integrable f P :=
  (integrable_const K).mono' hf (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hK ω)

/-- An `𝓕_u`-event inside `{u < σ}` is an `𝓕_σ`-event. -/
theorem measurableSet_inter_lt_stopping {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) {u : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[𝓕 u] A) : MeasurableSet[hσ.measurableSpace] (A ∩ {ω | (u : WithTop ℝ≥0) < σ ω}) := by
  have hgt : MeasurableSet[𝓕 u] {ω | (u : WithTop ℝ≥0) < σ ω} := by
    have : {ω | (u : WithTop ℝ≥0) < σ ω} = {ω | σ ω ≤ u}ᶜ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [this]; exact (hσ u).compl
  refine ⟨(le_iSup (fun i => (𝓕 i : MeasurableSpace Ω)) u) _ (hA.inter hgt), fun i => ?_⟩
  by_cases hui : u ≤ i
  · exact ((𝓕.mono hui _ hA).inter (𝓕.mono hui _ hgt)).inter (hσ i)
  · have : A ∩ {ω | (u : WithTop ℝ≥0) < σ ω} ∩ {ω | σ ω ≤ i} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      have h1 : (u : WithTop ℝ≥0) < σ ω := hω.1.2
      have h2 : σ ω ≤ (i : WithTop ℝ≥0) := hω.2
      exact hui (WithTop.coe_le_coe.1 (h1.trans_le h2).le)
    rw [this]; exact @MeasurableSet.empty _ (𝓕 i)

/-- The value of a stopped process at a finite time is a value of the process. -/
theorem abs_stoppedProcess_le {X : ℝ≥0 → Ω → ℝ} {K : ℝ} (hX : ∀ s ω, |X s ω| ≤ K) (σ : Ω → WithTop ℝ≥0)
    (s : ℝ≥0) (ω : Ω) : |stoppedProcess X σ s ω| ≤ K := hX _ _

/-- **Concatenation of martingales at a stopping time** (the product step of (D12)): if `X` and `V` are bounded
right-continuous martingales and `V = 1` up to the stopping time `σ`, then `s ↦ X_{s ∧ σ} V_s` is a martingale. -/
theorem martingale_stoppedProcess_mul [IsFiniteMeasure P] {X V : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P)
    (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t) (hV : Martingale V 𝓕 P)
    (hVrc : ∀ ω t, ContinuousWithinAt (V · ω) (Ici t) t) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ)
    {K₁ K₂ : ℝ} (hXb : ∀ s ω, |X s ω| ≤ K₁) (hVb : ∀ s ω, |V s ω| ≤ K₂)
    (hV1 : ∀ (s : ℝ≥0) ω, (s : WithTop ℝ≥0) ≤ σ ω → V s ω = 1) :
    Martingale (fun s ω => stoppedProcess X σ s ω * V s ω) 𝓕 P := by
  have hU := InteractingSLE.Martingale.stoppedProcess_of_rightContinuous hX hXrc hσ
  set U := stoppedProcess X σ with hUdef
  have hadp : StronglyAdapted 𝓕 fun s ω => U s ω * V s ω := fun s => (hU.1 s).mul (hV.1 s)
  have hint : ∀ s, Integrable (fun ω => U s ω * V s ω) P := fun s =>
    integrable_of_abs_le ((hadp s).mono (𝓕.le s)).aestronglyMeasurable (K := K₁ * K₂) fun ω => by
      rw [abs_mul]
      exact mul_le_mul (abs_stoppedProcess_le hXb σ s ω) (hVb s ω) (abs_nonneg _) ((abs_nonneg _).trans (hXb 0 ω))
  have hUi : ∀ s, Integrable (U s) P := fun s => hU.integrable s
  have hVi : ∀ s, Integrable (V s) P := fun s => hV.integrable s
  refine ⟨hadp, fun u v huv => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le u) (hint v) (fun A _ _ => (hint u).integrableOn)
    (fun A hA _ => ?_) (hadp u).aestronglyMeasurable).symm
  have hAm : MeasurableSet A := 𝓕.le u _ hA
  -- (T1): the `V`-increment against the `𝓕_u`-measurable `1_A U_u`
  have hT1 : ∫ ω, A.indicator (U u) ω * V v ω ∂P = ∫ ω, A.indicator (U u) ω * V u ω ∂P := by
    have hg : StronglyMeasurable[(isStoppingTime_const 𝓕 u).measurableSpace] (A.indicator (U u)) := by
      rw [IsStoppingTime.measurableSpace_const]; exact (hU.1 u).indicator hA
    have h := integral_mul_stoppedValue_eq hV hVrc (isStoppingTime_const 𝓕 u) (isStoppingTime_const 𝓕 v)
      (fun _ => WithTop.coe_le_coe.2 huv) (T := v) (fun _ => le_rfl) hg (K := K₁) fun ω => by
        by_cases hω : ω ∈ A
        · rw [indicator_of_mem hω]; exact abs_stoppedProcess_le hXb σ u ω
        · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hXb 0 ω)
    simpa only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] using h
  -- (T2): the `U`-increment, which lives on `{u < σ}` and is `𝓕_{v ∧ σ}`-measurable
  set ρ : Ω → WithTop ℝ≥0 := fun ω => min (v : WithTop ℝ≥0) (σ ω) with hρdef
  set ρ' : Ω → WithTop ℝ≥0 := fun ω => min (u : WithTop ℝ≥0) (σ ω) with hρ'def
  have hρ : IsStoppingTime 𝓕 ρ := (isStoppingTime_const 𝓕 v).min hσ
  have hρ' : IsStoppingTime 𝓕 ρ' := (isStoppingTime_const 𝓕 u).min hσ
  have hρ'ρ : ρ' ≤ ρ := fun ω => min_le_min_right _ (WithTop.coe_le_coe.2 huv)
  set B := A ∩ {ω | (u : WithTop ℝ≥0) < σ ω} with hBdef
  have hBρ : MeasurableSet[hρ.measurableSpace] B := by
    refine (IsStoppingTime.measurableSet_min_iff (isStoppingTime_const 𝓕 v) hσ B).2 ⟨?_,
      measurableSet_inter_lt_stopping hσ hA⟩
    rw [IsStoppingTime.measurableSpace_const]
    have hgt : MeasurableSet[𝓕 u] {ω | (u : WithTop ℝ≥0) < σ ω} := by
      have : {ω | (u : WithTop ℝ≥0) < σ ω} = {ω | σ ω ≤ u}ᶜ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      rw [this]; exact (hσ u).compl
    exact 𝓕.mono huv _ (hA.inter hgt)
  have hprog := isStronglyProgressive_of_rightContinuous hX.1 hXrc
  have hmρ : Measurable[hρ.measurableSpace] (stoppedValue X ρ) := measurable_stoppedValue hprog hρ
  have hmρ' : Measurable[hρ.measurableSpace] (stoppedValue X ρ') :=
    (measurable_stoppedValue hprog hρ').mono (hρ'.measurableSpace_mono hρ hρ'ρ) le_rfl
  set g : Ω → ℝ := B.indicator fun ω => stoppedValue X ρ ω - stoppedValue X ρ' ω with hgdef
  have hgm : StronglyMeasurable[hρ.measurableSpace] g :=
    ((hmρ.sub hmρ').stronglyMeasurable).indicator hBρ
  have hgb : ∀ ω, |g ω| ≤ 2 * K₁ := fun ω => by
    by_cases hω : ω ∈ B
    · rw [hgdef, indicator_of_mem hω]
      have h1 : |stoppedValue X ρ ω| ≤ K₁ := hXb _ _
      have h2 : |stoppedValue X ρ' ω| ≤ K₁ := hXb _ _
      exact (abs_sub _ _).trans (by linarith)
    · rw [hgdef, indicator_of_notMem hω, abs_zero]; linarith [abs_nonneg (X 0 ω), hXb 0 ω]
  have hgeq : ∀ ω, A.indicator (fun ω => U v ω - U u ω) ω = g ω := fun ω => by
    by_cases hωA : ω ∈ A
    · by_cases hωσ : (u : WithTop ℝ≥0) < σ ω
      · rw [indicator_of_mem hωA, hgdef, indicator_of_mem (show ω ∈ B from ⟨hωA, hωσ⟩)]
        rfl
      · have hσu : σ ω ≤ u := not_lt.1 hωσ
        have hσv : σ ω ≤ v := hσu.trans (WithTop.coe_le_coe.2 huv)
        rw [indicator_of_mem hωA, hgdef, indicator_of_notMem (fun h : ω ∈ B => hωσ h.2)]
        simp only [hUdef, stoppedProcess, min_eq_right hσu, min_eq_right hσv, sub_self]
    · rw [indicator_of_notMem hωA, hgdef, indicator_of_notMem (fun h : ω ∈ B => hωA h.1)]
  have hT2 : ∫ ω, A.indicator (fun ω => U v ω - U u ω) ω * V v ω ∂P = 0 := by
    have h := integral_mul_stoppedValue_eq hV hVrc hρ (isStoppingTime_const 𝓕 v) (fun ω => min_le_left _ _)
      (T := v) (fun _ => le_rfl) hgm hgb
    have hVρ : ∀ ω, stoppedValue V ρ ω = 1 := fun ω => by
      have hne : ρ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      refine hV1 _ ω ?_
      obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
      have hx' : (ρ ω).untopA = x := by rw [← hx]; simp only [WithTop.untopA, WithTop.untopD_coe]
      rw [hx', hx]
      exact min_le_right _ _
    have hVv : ∀ ω, stoppedValue V (fun _ => (v : WithTop ℝ≥0)) ω = V v ω := fun ω => by
      simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    simp only [hVv, hVρ, mul_one] at h
    calc ∫ ω, A.indicator (fun ω => U v ω - U u ω) ω * V v ω ∂P = ∫ ω, g ω * V v ω ∂P := by
          simp only [hgeq]
      _ = ∫ ω, g ω ∂P := h
      _ = ∫ ω, A.indicator (fun ω => U v ω - U u ω) ω ∂P := by simp only [hgeq]
      _ = 0 := by
          rw [integral_indicator hAm, integral_sub (hUi v).integrableOn (hUi u).integrableOn,
            hU.setIntegral_eq huv hA, sub_self]
  -- combine
  have hsplit : ∀ ω, A.indicator (fun ω => U v ω * V v ω) ω - A.indicator (fun ω => U u ω * V u ω) ω =
      A.indicator (U u) ω * V v ω - A.indicator (U u) ω * V u ω +
        A.indicator (fun ω => U v ω - U u ω) ω * V v ω := fun ω => by
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω]; ring
    · simp only [indicator_of_notMem hω]; ring
  have hiA : ∀ s, Integrable (A.indicator fun ω => U s ω * V s ω) P := fun s => (hint s).indicator hAm
  have hi1 : Integrable (fun ω => A.indicator (U u) ω * V v ω) P :=
    (hVi v).bdd_mul ((hUi u).indicator hAm).aestronglyMeasurable (c := K₁) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ A
      · rw [indicator_of_mem hω]; exact abs_stoppedProcess_le hXb σ u ω
      · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hXb 0 ω))
  have hi2 : Integrable (fun ω => A.indicator (U u) ω * V u ω) P :=
    (hVi u).bdd_mul ((hUi u).indicator hAm).aestronglyMeasurable (c := K₁) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ A
      · rw [indicator_of_mem hω]; exact abs_stoppedProcess_le hXb σ u ω
      · rw [indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hXb 0 ω))
  have hi3 : Integrable (fun ω => A.indicator (fun ω => U v ω - U u ω) ω * V v ω) P :=
    (hVi v).bdd_mul (((hUi v).sub (hUi u)).indicator hAm).aestronglyMeasurable (c := 2 * K₁)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, hgeq]; exact hgb ω)
  have hdiff : ∫ ω, (A.indicator (fun ω => U v ω * V v ω) ω - A.indicator (fun ω => U u ω * V u ω) ω) ∂P = 0 := by
    have hadd := integral_add (μ := P) (hi1.sub hi2) hi3
    simp only [Pi.sub_apply] at hadd
    rw [integral_congr_ae (Eventually.of_forall hsplit), hadd, integral_sub hi1 hi2, hT1, sub_self, zero_add, hT2]
  rw [integral_sub (hiA v) (hiA u), integral_indicator hAm, integral_indicator hAm, sub_eq_zero] at hdiff
  exact hdiff.symm

/-- A stopped right-continuous process is right-continuous. -/
theorem continuousWithinAt_stoppedProcess {X : ℝ≥0 → Ω → ℝ} (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (σ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) : ContinuousWithinAt (stoppedProcess X σ · ω) (Ici t) t := by
  by_cases h : σ ω = ⊤
  · have e : (stoppedProcess X σ · ω) = (X · ω) := by
      funext s; simp only [stoppedProcess, h, le_top, min_eq_left, WithTop.untopA, WithTop.untopD_coe]
    rw [e]; exact hXrc ω t
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
    have e : (stoppedProcess X σ · ω) = fun s => X (min s a) ω := by
      funext s
      simp only [stoppedProcess, ← ha, WithTop.untopA]
      rw [← WithTop.coe_min, WithTop.untopD_coe]
    rw [e]
    have hc : ContinuousWithinAt (fun s : ℝ≥0 => min s a) (Ici t) t := (continuous_id.min continuous_const).continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun s : ℝ≥0 => min s a) (x := t) (hXrc ω (min t a)) hc
      fun s hs => show min t a ≤ min s a from min_le_min_right a hs

/-- **The ratio of a positive bounded martingale stopped at `τ` and at `σ ≤ τ` is a martingale** (it is `1` before
`σ` and `Y_{s ∧ τ}/Y_σ` after). -/
theorem martingale_ratio_stopped [IsFiniteMeasure P] {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y 𝓕 P)
    (hYrc : ∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t) {c C : ℝ} (hc : 0 < c)
    (hYb : ∀ s ω, c ≤ Y s ω ∧ Y s ω ≤ C) {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ)
    (hτ : IsStoppingTime 𝓕 τ) (hστ : σ ≤ τ) :
    Martingale (fun s ω => stoppedProcess Y τ s ω / stoppedProcess Y σ s ω) 𝓕 P := by
  have hYτ := InteractingSLE.Martingale.stoppedProcess_of_rightContinuous hY hYrc hτ
  have hYσ := InteractingSLE.Martingale.stoppedProcess_of_rightContinuous hY hYrc hσ
  have hb : ∀ (ρ : Ω → WithTop ℝ≥0) s ω, c ≤ stoppedProcess Y ρ s ω ∧ stoppedProcess Y ρ s ω ≤ C :=
    fun ρ s ω => hYb _ _
  have hpos : ∀ (ρ : Ω → WithTop ℝ≥0) s ω, 0 < stoppedProcess Y ρ s ω := fun ρ s ω => hc.trans_le (hb ρ s ω).1
  have hadp : StronglyAdapted 𝓕 fun s ω => stoppedProcess Y τ s ω / stoppedProcess Y σ s ω :=
    fun s => (hYτ.1 s).div (hYσ.1 s)
  have hRb : ∀ s ω, |stoppedProcess Y τ s ω / stoppedProcess Y σ s ω| ≤ C / c := fun s ω => by
    rw [abs_div, abs_of_pos (hpos τ s ω), abs_of_pos (hpos σ s ω)]
    exact div_le_div₀ ((hpos τ s ω).le.trans (hb τ s ω).2) (hb τ s ω).2 hc (hb σ s ω).1
  have hint : ∀ s, Integrable (fun ω => stoppedProcess Y τ s ω / stoppedProcess Y σ s ω) P := fun s =>
    integrable_of_abs_le ((hadp s).mono (𝓕.le s)).aestronglyMeasurable (hRb s)
  have hprog := isStronglyProgressive_of_rightContinuous hY.1 hYrc
  have hinvb : ∀ (ρ : Ω → WithTop ℝ≥0) s ω, |1 / stoppedProcess Y ρ s ω| ≤ 1 / c := fun ρ s ω => by
    rw [abs_of_pos (one_div_pos.2 (hpos ρ s ω))]
    exact one_div_le_one_div_of_le hc (hb ρ s ω).1
  refine ⟨hadp, fun u v huv => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le u) (hint v) (fun A _ _ => (hint u).integrableOn)
    (fun A hA _ => ?_) (hadp u).aestronglyMeasurable).symm
  have hgt : MeasurableSet[𝓕 u] {ω | (u : WithTop ℝ≥0) < σ ω} := by
    have : {ω | (u : WithTop ℝ≥0) < σ ω} = {ω | σ ω ≤ u}ᶜ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [this]; exact (hσ u).compl
  rw [← integral_inter_add_sdiff (𝓕.le u _ hgt) (hint u).integrableOn,
    ← integral_inter_add_sdiff (𝓕.le u _ hgt) (hint v).integrableOn]
  congr 1
  · -- on `B = A ∩ {u < σ}`: the ratio is `1` at `u`; optional sampling between `v ∧ σ` and `v ∧ τ`
    set B := A ∩ {ω | (u : WithTop ℝ≥0) < σ ω} with hBdef
    set ρ : Ω → WithTop ℝ≥0 := fun ω => min (v : WithTop ℝ≥0) (σ ω) with hρdef
    set ρ₂ : Ω → WithTop ℝ≥0 := fun ω => min (v : WithTop ℝ≥0) (τ ω) with hρ₂def
    have hρ : IsStoppingTime 𝓕 ρ := (isStoppingTime_const 𝓕 v).min hσ
    have hρ₂ : IsStoppingTime 𝓕 ρ₂ := (isStoppingTime_const 𝓕 v).min hτ
    have hBm : MeasurableSet B := 𝓕.le u _ (hA.inter hgt)
    have hBρ : MeasurableSet[hρ.measurableSpace] B := by
      refine (IsStoppingTime.measurableSet_min_iff (isStoppingTime_const 𝓕 v) hσ B).2 ⟨?_,
        measurableSet_inter_lt_stopping hσ hA⟩
      rw [IsStoppingTime.measurableSpace_const]
      exact 𝓕.mono huv _ (hA.inter hgt)
    set h : Ω → ℝ := B.indicator fun ω => 1 / stoppedValue Y ρ ω with hhdef
    have hhm : StronglyMeasurable[hρ.measurableSpace] h :=
      ((measurable_const.div (measurable_stoppedValue hprog hρ)).stronglyMeasurable).indicator hBρ
    have hhb : ∀ ω, |h ω| ≤ 1 / c := fun ω => by
      by_cases hω : ω ∈ B
      · rw [hhdef, indicator_of_mem hω]; exact hinvb σ v ω
      · rw [hhdef, indicator_of_notMem hω, abs_zero]; positivity
    have hOS := integral_mul_stoppedValue_eq hY hYrc hρ hρ₂ (fun ω => min_le_min_left _ (hστ ω)) (T := v)
      (fun ω => min_le_left _ _) hhm hhb
    have e1 : ∀ ω, B.indicator (fun ω => stoppedProcess Y τ v ω / stoppedProcess Y σ v ω) ω =
        h ω * stoppedValue Y ρ₂ ω := fun ω => by
      by_cases hω : ω ∈ B
      · rw [indicator_of_mem hω, hhdef, indicator_of_mem hω]
        simp only [stoppedProcess, stoppedValue, hρdef, hρ₂def]
        ring
      · rw [indicator_of_notMem hω, hhdef, indicator_of_notMem hω, zero_mul]
    have e2 : ∀ ω, h ω * stoppedValue Y ρ ω = B.indicator (fun _ => (1 : ℝ)) ω := fun ω => by
      by_cases hω : ω ∈ B
      · rw [hhdef, indicator_of_mem hω, indicator_of_mem hω]
        exact one_div_mul_cancel (hpos σ v ω).ne'
      · rw [hhdef, indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
    have e3 : ∀ ω ∈ B, stoppedProcess Y τ u ω / stoppedProcess Y σ u ω = 1 := fun ω hω => by
      have h1 : (u : WithTop ℝ≥0) ≤ σ ω := hω.2.le
      have h2 : (u : WithTop ℝ≥0) ≤ τ ω := h1.trans (hστ ω)
      simp only [stoppedProcess, min_eq_left h1, min_eq_left h2]
      exact div_self (hc.trans_le (hYb _ _).1).ne'
    calc ∫ ω in B, stoppedProcess Y τ u ω / stoppedProcess Y σ u ω ∂P = ∫ ω in B, (1 : ℝ) ∂P :=
          setIntegral_congr_fun hBm e3
      _ = ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂P := (integral_indicator hBm).symm
      _ = ∫ ω, h ω * stoppedValue Y ρ ω ∂P := integral_congr_ae (Eventually.of_forall fun ω => (e2 ω).symm)
      _ = ∫ ω, h ω * stoppedValue Y ρ₂ ω ∂P := hOS.symm
      _ = ∫ ω, B.indicator (fun ω => stoppedProcess Y τ v ω / stoppedProcess Y σ v ω) ω ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => (e1 ω).symm)
      _ = ∫ ω in B, stoppedProcess Y τ v ω / stoppedProcess Y σ v ω ∂P := integral_indicator hBm
  · -- on `A ∩ {σ ≤ u}`: the denominator is frozen at `Y_σ`; the stopped martingale `Y^τ` against `1/Y_σ`
    set A₁ := A \ {ω | (u : WithTop ℝ≥0) < σ ω} with hA₁def
    have hA₁ : MeasurableSet[𝓕 u] A₁ := hA.diff hgt
    have hA₁m : MeasurableSet A₁ := 𝓕.le u _ hA₁
    set g : Ω → ℝ := A₁.indicator fun ω => 1 / stoppedProcess Y σ u ω with hgdef
    have hgm : StronglyMeasurable[(isStoppingTime_const 𝓕 u).measurableSpace] g := by
      rw [IsStoppingTime.measurableSpace_const]
      exact ((stronglyMeasurable_const.div (hYσ.1 u))).indicator hA₁
    have hgb : ∀ ω, |g ω| ≤ 1 / c := fun ω => by
      by_cases hω : ω ∈ A₁
      · rw [hgdef, indicator_of_mem hω]; exact hinvb σ u ω
      · rw [hgdef, indicator_of_notMem hω, abs_zero]; positivity
    have hOS := integral_mul_stoppedValue_eq hYτ (fun ω t => continuousWithinAt_stoppedProcess hYrc τ ω t)
      (isStoppingTime_const 𝓕 u) (isStoppingTime_const 𝓕 v) (fun _ => WithTop.coe_le_coe.2 huv) (T := v)
      (fun _ => le_rfl) hgm hgb
    have hsv : ∀ (r : ℝ≥0) ω, stoppedValue (stoppedProcess Y τ) (fun _ => (r : WithTop ℝ≥0)) ω =
        stoppedProcess Y τ r ω := fun r ω => by simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    simp only [hsv] at hOS
    have e : ∀ r, u ≤ r → ∀ ω, A₁.indicator (fun ω => stoppedProcess Y τ r ω / stoppedProcess Y σ r ω) ω =
        g ω * stoppedProcess Y τ r ω := fun r hr ω => by
      by_cases hω : ω ∈ A₁
      · have hσu : σ ω ≤ u := not_lt.1 hω.2
        have hσr : σ ω ≤ r := hσu.trans (WithTop.coe_le_coe.2 hr)
        rw [indicator_of_mem hω, hgdef, indicator_of_mem hω]
        simp only [stoppedProcess, min_eq_right hσu, min_eq_right hσr]
        ring
      · rw [indicator_of_notMem hω, hgdef, indicator_of_notMem hω, zero_mul]
    calc ∫ ω in A₁, stoppedProcess Y τ u ω / stoppedProcess Y σ u ω ∂P
        = ∫ ω, A₁.indicator (fun ω => stoppedProcess Y τ u ω / stoppedProcess Y σ u ω) ω ∂P :=
          (integral_indicator hA₁m).symm
      _ = ∫ ω, g ω * stoppedProcess Y τ u ω ∂P := integral_congr_ae (Eventually.of_forall (e u le_rfl))
      _ = ∫ ω, g ω * stoppedProcess Y τ v ω ∂P := hOS.symm
      _ = ∫ ω, A₁.indicator (fun ω => stoppedProcess Y τ v ω / stoppedProcess Y σ v ω) ω ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => (e v huv ω).symm)
      _ = ∫ ω in A₁, stoppedProcess Y τ v ω / stoppedProcess Y σ v ω ∂P := integral_indicator hA₁m

/-- **An `𝓕_σ`-event times a martingale that vanishes up to `σ` is a martingale.** -/
theorem martingale_indicator_of_eq_zero [IsFiniteMeasure P] {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓕 P)
    (hNrc : ∀ ω t, ContinuousWithinAt (N · ω) (Ici t) t)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ) (hN0 : ∀ (s : ℝ≥0) ω, (s : WithTop ℝ≥0) ≤ σ ω → N s ω = 0)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) :
    Martingale (fun s => E.indicator (N s)) 𝓕 P := by
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hE
  have hEs : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] (E ∩ {ω | σ ω ≤ s}) := fun s => hE.2 s
  have hpt : ∀ (s : ℝ≥0) ω, E.indicator (N s) ω = (E ∩ {ω | σ ω ≤ s}).indicator (N s) ω := fun s ω => by
    by_cases hω : ω ∈ E
    · by_cases hσs : σ ω ≤ s
      · rw [indicator_of_mem hω, indicator_of_mem (show ω ∈ E ∩ {ω | σ ω ≤ s} from ⟨hω, hσs⟩)]
      · rw [indicator_of_mem hω, indicator_of_notMem (fun h : ω ∈ E ∩ {ω | σ ω ≤ s} => hσs h.2),
          hN0 s ω (not_le.1 hσs).le]
    · rw [indicator_of_notMem hω, indicator_of_notMem (fun h : ω ∈ E ∩ {ω | σ ω ≤ s} => hω h.1)]
  have hadp : StronglyAdapted 𝓕 fun s => E.indicator (N s) := fun s => by
    have e : E.indicator (N s) = (E ∩ {ω | σ ω ≤ s}).indicator (N s) := funext (hpt s)
    show StronglyMeasurable[𝓕 s] (E.indicator (N s))
    rw [e]; exact (hN.1 s).indicator (hEs s)
  have hint : ∀ s, Integrable (E.indicator (N s)) P := fun s => (hN.integrable s).indicator hEm
  refine ⟨hadp, fun u v huv => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le u) (hint v) (fun A _ _ => (hint u).integrableOn)
    (fun A hA _ => ?_) (hadp u).aestronglyMeasurable).symm
  have hgt : MeasurableSet[𝓕 u] {ω | (u : WithTop ℝ≥0) < σ ω} := by
    have : {ω | (u : WithTop ℝ≥0) < σ ω} = {ω | σ ω ≤ u}ᶜ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [this]; exact (hσ u).compl
  rw [← integral_inter_add_sdiff (𝓕.le u _ hgt) (hint u).integrableOn,
    ← integral_inter_add_sdiff (𝓕.le u _ hgt) (hint v).integrableOn]
  congr 1
  · -- on `B = A ∩ {u < σ}`: zero at `u`; at `v` optional sampling between `v ∧ σ` and `v`
    set B := A ∩ {ω | (u : WithTop ℝ≥0) < σ ω} with hBdef
    have hBm : MeasurableSet B := 𝓕.le u _ (hA.inter hgt)
    have h0 : ∫ ω in B, E.indicator (N u) ω ∂P = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun ω hω => ?_
      by_cases hωE : ω ∈ E
      · rw [indicator_of_mem hωE]; exact hN0 u ω hω.2.le
      · rw [indicator_of_notMem hωE]
    rw [h0]
    set ρ : Ω → WithTop ℝ≥0 := fun ω => min (v : WithTop ℝ≥0) (σ ω) with hρdef
    have hρ : IsStoppingTime 𝓕 ρ := (isStoppingTime_const 𝓕 v).min hσ
    set D := B ∩ (E ∩ {ω | σ ω ≤ v}) with hDdef
    have hDρ : MeasurableSet[hρ.measurableSpace] D := by
      refine (IsStoppingTime.measurableSet_min_iff (isStoppingTime_const 𝓕 v) hσ D).2 ⟨?_, ?_⟩
      · rw [IsStoppingTime.measurableSpace_const]
        exact (𝓕.mono huv _ (hA.inter hgt)).inter (hEs v)
      · exact (measurableSet_inter_lt_stopping hσ hA).inter (hE.inter (hσ.measurableSet_le' v))
    have hDm : MeasurableSet D := hρ.measurableSpace_le _ hDρ
    have hOS := integral_mul_stoppedValue_eq hN hNrc hρ (isStoppingTime_const 𝓕 v) (fun ω => min_le_left _ _)
      (T := v) (fun _ => le_rfl) (g := D.indicator fun _ => (1 : ℝ))
      (stronglyMeasurable_const.indicator hDρ) (K := 1) fun ω => by
        by_cases hω : ω ∈ D
        · rw [indicator_of_mem hω, abs_one]
        · rw [indicator_of_notMem hω, abs_zero]; exact zero_le_one
    have hNρ : ∀ ω, stoppedValue N ρ ω = 0 := fun ω => by
      have hne : ρ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
      have hx' : (ρ ω).untopA = x := by rw [← hx]; simp only [WithTop.untopA, WithTop.untopD_coe]
      refine hN0 _ ω ?_
      rw [hx', hx]
      exact min_le_right _ _
    have hNv : ∀ ω, stoppedValue N (fun _ => (v : WithTop ℝ≥0)) ω = N v ω := fun ω => by
      simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    simp only [hNρ, hNv, mul_zero, integral_zero] at hOS
    have e : ∀ ω, B.indicator (E.indicator (N v)) ω = D.indicator (fun _ => (1 : ℝ)) ω * N v ω := fun ω => by
      by_cases hωB : ω ∈ B
      · by_cases hωE : ω ∈ E
        · by_cases hσv : σ ω ≤ v
          · rw [indicator_of_mem hωB, indicator_of_mem hωE, indicator_of_mem (show ω ∈ D from ⟨hωB, hωE, hσv⟩),
              one_mul]
          · rw [indicator_of_mem hωB, indicator_of_mem hωE, indicator_of_notMem (fun h : ω ∈ D => hσv h.2.2),
              zero_mul, hN0 v ω (not_le.1 hσv).le]
        · rw [indicator_of_mem hωB, indicator_of_notMem hωE, indicator_of_notMem (fun h : ω ∈ D => hωE h.2.1),
            zero_mul]
      · rw [indicator_of_notMem hωB, indicator_of_notMem (fun h : ω ∈ D => hωB h.1), zero_mul]
    rw [← integral_indicator hBm, integral_congr_ae (Eventually.of_forall e), hOS]
  · -- on `A ∩ {σ ≤ u}`: the martingale property of `N` on the `𝓕_u`-event `A ∩ E ∩ {σ ≤ u}`
    have hA₁ : A \ {ω | (u : WithTop ℝ≥0) < σ ω} = A ∩ {ω | σ ω ≤ u} := by
      ext ω; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_lt]
    rw [hA₁, setIntegral_indicator hEm, setIntegral_indicator hEm]
    have hset : A ∩ {ω | σ ω ≤ u} ∩ E = A ∩ (E ∩ {ω | σ ω ≤ u}) := by ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [hset]
    exact hN.setIntegral_eq huv (hA.inter (hEs u))

/-- A finite sum of martingales is a martingale. -/
theorem martingale_finsetSum [IsFiniteMeasure P] {ι : Type*} (S : Finset ι) {N : ι → ℝ≥0 → Ω → ℝ}
    (hN : ∀ i ∈ S, Martingale (N i) 𝓕 P) : Martingale (fun s ω => ∑ i ∈ S, N i s ω) 𝓕 P := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using martingale_const 𝓕 P (0 : ℝ)
  | insert a S ha ih =>
    have h := (hN a (Finset.mem_insert_self a S)).add (ih fun i hi => hN i (Finset.mem_insert_of_mem hi))
    convert h using 1
    funext s ω
    simp only [Finset.sum_insert ha, Pi.add_apply]

/-- **The switch step of (D12)**: from a bounded right-continuous martingale `X` stopped at `σ`, continue with the
ratio `Y_j(s ∧ τ)/Y_j(σ)` of a member, chosen at time `σ` (`{j = i} ∈ 𝓕_σ`), of a finite family of positive bounded
right-continuous martingales. The resulting process `X_{s∧σ} · Y_j(s ∧ τ)/Y_j(s ∧ σ)` is a martingale. -/
theorem Martingale.switch [IsFiniteMeasure P] {ι : Type*} [Fintype ι] {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P)
    (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t) {KX : ℝ} (hXb : ∀ s ω, |X s ω| ≤ KX)
    {Y : ι → ℝ≥0 → Ω → ℝ} (hY : ∀ i, Martingale (Y i) 𝓕 P)
    (hYrc : ∀ i ω t, ContinuousWithinAt (Y i · ω) (Ici t) t) {c C : ℝ} (hc : 0 < c)
    (hYb : ∀ i s ω, c ≤ Y i s ω ∧ Y i s ω ≤ C) {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓕 σ)
    (hτ : IsStoppingTime 𝓕 τ) (hστ : σ ≤ τ) {j : Ω → ι}
    (hj : ∀ i, MeasurableSet[hσ.measurableSpace] {ω | j ω = i}) :
    Martingale (fun s ω => stoppedProcess X σ s ω *
      (stoppedProcess (Y (j ω)) τ s ω / stoppedProcess (Y (j ω)) σ s ω)) 𝓕 P := by
  classical
  set R : ι → ℝ≥0 → Ω → ℝ := fun i s ω => stoppedProcess (Y i) τ s ω / stoppedProcess (Y i) σ s ω with hRdef
  set N : ι → ℝ≥0 → Ω → ℝ := fun i s ω => R i s ω - 1 with hNdef
  have hb : ∀ i (ρ : Ω → WithTop ℝ≥0) s ω, c ≤ stoppedProcess (Y i) ρ s ω ∧ stoppedProcess (Y i) ρ s ω ≤ C :=
    fun i ρ s ω => hYb i _ _
  have hpos : ∀ i (ρ : Ω → WithTop ℝ≥0) s ω, 0 < stoppedProcess (Y i) ρ s ω := fun i ρ s ω =>
    hc.trans_le (hb i ρ s ω).1
  have hRm : ∀ i, Martingale (R i) 𝓕 P := fun i => martingale_ratio_stopped (hY i) (hYrc i) hc (hYb i) hσ hτ hστ
  have hNm : ∀ i, Martingale (N i) 𝓕 P := fun i => (hRm i).sub (martingale_const 𝓕 P (1 : ℝ))
  have hRrc : ∀ i ω t, ContinuousWithinAt (R i · ω) (Ici t) t := fun i ω t =>
    (continuousWithinAt_stoppedProcess (hYrc i) τ ω t).div (continuousWithinAt_stoppedProcess (hYrc i) σ ω t)
      (hpos i σ t ω).ne'
  have hNrc : ∀ i ω t, ContinuousWithinAt (N i · ω) (Ici t) t := fun i ω t =>
    (hRrc i ω t).sub continuousWithinAt_const
  have hR1 : ∀ i (s : ℝ≥0) ω, (s : WithTop ℝ≥0) ≤ σ ω → R i s ω = 1 := fun i s ω hs => by
    have h2 : (s : WithTop ℝ≥0) ≤ τ ω := hs.trans (hστ ω)
    simp only [hRdef, stoppedProcess, min_eq_left hs, min_eq_left h2]
    exact div_self (hc.trans_le (hYb i _ _).1).ne'
  have hN0 : ∀ i (s : ℝ≥0) ω, (s : WithTop ℝ≥0) ≤ σ ω → N i s ω = 0 := fun i s ω hs => by
    simp only [hNdef, hR1 i s ω hs, sub_self]
  have hRb : ∀ i s ω, |R i s ω| ≤ C / c := fun i s ω => by
    rw [hRdef, abs_div, abs_of_pos (hpos i τ s ω), abs_of_pos (hpos i σ s ω)]
    exact div_le_div₀ ((hpos i τ s ω).le.trans (hb i τ s ω).2) (hb i τ s ω).2 hc (hb i σ s ω).1
  -- the switched ratio as `1 + ∑ᵢ 1_{j = i} Nᵢ`
  set V : ℝ≥0 → Ω → ℝ := fun s ω => 1 + ∑ i, {ω | j ω = i}.indicator (N i s) ω with hVdef
  have hVm : Martingale V 𝓕 P := by
    have h := (martingale_const 𝓕 P (1 : ℝ)).add (martingale_finsetSum (𝓕 := 𝓕) (P := P) Finset.univ
      (N := fun i s => {ω | j ω = i}.indicator (N i s))
      fun i _ => martingale_indicator_of_eq_zero (hNm i) (hNrc i) hσ (hN0 i) (hj i))
    convert h using 1
    funext s ω
    simp only [hVdef, Pi.add_apply]
  have hVrc : ∀ ω t, ContinuousWithinAt (V · ω) (Ici t) t := fun ω t => by
    refine continuousWithinAt_const.add (tendsto_finsetSum _ fun i _ => ?_)
    by_cases hω : j ω = i
    · simp only [indicator_of_mem (show ω ∈ {ω | j ω = i} from hω)]; exact hNrc i ω t
    · simp only [indicator_of_notMem (show ω ∉ {ω | j ω = i} from hω)]; exact continuousWithinAt_const
  have hVeq : ∀ s ω, V s ω = R (j ω) s ω := fun s ω => by
    have hsum : ∑ i, {ω | j ω = i}.indicator (N i s) ω = N (j ω) s ω := by
      rw [Finset.sum_eq_single (j ω)]
      · exact indicator_of_mem (show ω ∈ {ω | j ω = j ω} from rfl) _
      · intro i _ hi
        exact indicator_of_notMem (show ω ∉ {ω | j ω = i} from fun h => hi h.symm) _
      · intro h; exact absurd (Finset.mem_univ _) h
    show 1 + ∑ i, {ω | j ω = i}.indicator (N i s) ω = R (j ω) s ω
    rw [hsum]
    simp only [hNdef]
    ring
  have hVb : ∀ s ω, |V s ω| ≤ C / c + 1 := fun s ω => by
    rw [hVeq]; exact (hRb _ s ω).trans (by linarith)
  have hV1 : ∀ (s : ℝ≥0) ω, (s : WithTop ℝ≥0) ≤ σ ω → V s ω = 1 := fun s ω hs => by
    rw [hVeq, hR1 _ s ω hs]
  have h := martingale_stoppedProcess_mul hX hXrc hVm hVrc hσ hXb hVb hV1
  convert h using 1
  funext s ω
  rw [hVeq]

/-- **The column-by-column concatenation** of (D12): `Π₀ = 1` and `Π_{k+1}(s) = Π_k(s ∧ τ_k) · Y_{j_k}(s ∧ τ_{k+1}) /
Y_{j_k}(s ∧ τ_k)`, the ratio of the martingale `Y_{j_k}` chosen at `τ_k` over the column `[τ_k, τ_{k+1}]`. -/
def concatProc {ι : Type*} (Y : ι → ℝ≥0 → Ω → ℝ) (τ : ℕ → Ω → WithTop ℝ≥0) (j : ℕ → Ω → ι) :
    ℕ → ℝ≥0 → Ω → ℝ
  | 0 => fun _ _ => 1
  | k + 1 => fun s ω => stoppedProcess (concatProc Y τ j k) (τ k) s ω *
      (stoppedProcess (Y (j k ω)) (τ (k + 1)) s ω / stoppedProcess (Y (j k ω)) (τ k) s ω)

/-- **The concatenation of (D12) is a bounded right-continuous martingale**: for positive bounded right-continuous
martingales `Y i`, `c ≤ Y i ≤ C`, increasing stopping times `τ_k` and indices `j_k` chosen at `τ_k`,
`Π_k` is a martingale with right-continuous paths and `|Π_k| ≤ (C/c)^k`. -/
theorem martingale_concatProc [IsFiniteMeasure P] {ι : Type*} [Fintype ι] {Y : ι → ℝ≥0 → Ω → ℝ}
    (hY : ∀ i, Martingale (Y i) 𝓕 P) (hYrc : ∀ i ω t, ContinuousWithinAt (Y i · ω) (Ici t) t) {c C : ℝ}
    (hc : 0 < c) (hYb : ∀ i s ω, c ≤ Y i s ω ∧ Y i s ω ≤ C) {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ k, IsStoppingTime 𝓕 (τ k)) (hmono : ∀ k, τ k ≤ τ (k + 1)) {j : ℕ → Ω → ι}
    (hj : ∀ k i, MeasurableSet[(hτ k).measurableSpace] {ω | j k ω = i}) (k : ℕ) :
    Martingale (concatProc Y τ j k) 𝓕 P ∧
      (∀ ω t, ContinuousWithinAt (concatProc Y τ j k · ω) (Ici t) t) ∧
      ∀ s ω, |concatProc Y τ j k s ω| ≤ (C / c) ^ k := by
  have hb' : ∀ i (ρ : Ω → WithTop ℝ≥0) s ω, c ≤ stoppedProcess (Y i) ρ s ω ∧ stoppedProcess (Y i) ρ s ω ≤ C :=
    fun i ρ s ω => hYb i _ _
  have hpos : ∀ i (ρ : Ω → WithTop ℝ≥0) s ω, 0 < stoppedProcess (Y i) ρ s ω := fun i ρ s ω =>
    hc.trans_le (hb' i ρ s ω).1
  induction k with
  | zero =>
    refine ⟨martingale_const 𝓕 P (1 : ℝ), fun ω t => continuousWithinAt_const, fun s ω => ?_⟩
    simp [concatProc]
  | succ k ih =>
    obtain ⟨hm, hrc, hb⟩ := ih
    refine ⟨Martingale.switch hm hrc hb hY hYrc hc hYb (hτ k) (hτ (k + 1)) (hmono k) (hj k), fun ω t => ?_,
      fun s ω => ?_⟩
    · exact (continuousWithinAt_stoppedProcess hrc (τ k) ω t).mul
        ((continuousWithinAt_stoppedProcess (hYrc (j k ω)) (τ (k + 1)) ω t).div
          (continuousWithinAt_stoppedProcess (hYrc (j k ω)) (τ k) ω t) (hpos (j k ω) (τ k) t ω).ne')
    · have h1 : |stoppedProcess (concatProc Y τ j k) (τ k) s ω| ≤ (C / c) ^ k := hb _ _
      have h2 : |stoppedProcess (Y (j k ω)) (τ (k + 1)) s ω / stoppedProcess (Y (j k ω)) (τ k) s ω| ≤ C / c := by
        rw [abs_div, abs_of_pos (hpos _ _ s ω), abs_of_pos (hpos _ _ s ω)]
        exact div_le_div₀ ((hpos _ _ s ω).le.trans (hb' (j k ω) (τ (k + 1)) s ω).2)
          (hb' (j k ω) (τ (k + 1)) s ω).2 hc (hb' (j k ω) (τ k) s ω).1
      show |stoppedProcess (concatProc Y τ j k) (τ k) s ω *
        (stoppedProcess (Y (j k ω)) (τ (k + 1)) s ω / stoppedProcess (Y (j k ω)) (τ k) s ω)| ≤ (C / c) ^ (k + 1)
      rw [abs_mul, pow_succ]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

end Stoch

end InteractingSLE.ZhanGT4
