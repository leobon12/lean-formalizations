/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor

/-!
# Optional passage along strict upper dyadic times

Packet PROVE-WW-B19 (Astra's follow-up note, Part E.4: "Upper dyadic approximations to a stopping time, localized
strictly before contact and before a test support is met, now give (E.4) ... at every stopping time"). This file is
the probabilistic core, stated abstractly and without any monotonicity of the σ-algebras:

* `dyq n k = (k + 1)/2ⁿ`, `dyIdx n t = ⌊2ⁿ t⌋`, `dyF n t = dyq n (dyIdx n t)`: the strict upper dyadic
  approximation of `t` (`lt_dyF`, `antitone_dyF`, `tendsto_dyF`);
* **`setIntegral_eq_of_dyadic`**: let `X` be bounded by `1`, and suppose that for every grid point `q = (k+1)/2ⁿ`,
  almost surely on an event `Av q`, `E[X | 𝓜 n k] = F q`, with `‖F q‖ ≤ 1` on `Av q`. Let `θ` be a random time
  and `D` an event such that every piece `D ∩ {⌊2ⁿθ⌋ = k} ∩ Av((k+1)/2ⁿ)` is (up to a null set) in `𝓜 n k`, and almost surely
  on `D`, eventually `Av(dyF n θ)` holds and `F(dyF n θ) → G`. Then `∫_D X = ∫_D G`;
* **`ae_condExp_eq_of_forall_setIntegral`**: if `∫_{A ∩ E} X = ∫_{A ∩ E} G` for all `A ∈ m`, with `E ∈ m` and
  `1_E G` `m`-measurable and integrable, then `E[X | m] = G` almost surely on `E`.

The σ-algebras `𝓜 n k` need not increase: this is what allows the germ-enlarged σ-algebras of the two-slit union law
(which are not monotone in the forward time) to be used directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.ChartConst

/-! ### Strict upper dyadic approximations -/

/-- The dyadic grid point `(k + 1) / 2ⁿ`. -/
def dyq (n k : ℕ) : ℝ≥0 := ((k : ℝ≥0) + 1) / 2 ^ n

/-- The dyadic index `⌊2ⁿ t⌋`. -/
def dyIdx (n : ℕ) (t : ℝ≥0) : ℕ := ⌊(2 : ℝ) ^ n * t⌋₊

/-- The strict upper dyadic approximation `(⌊2ⁿ t⌋ + 1) / 2ⁿ` of `t`. -/
def dyF (n : ℕ) (t : ℝ≥0) : ℝ≥0 := dyq n (dyIdx n t)

theorem two_pow_pos' (n : ℕ) : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n

theorem dyq_coe (n k : ℕ) : (dyq n k : ℝ) = ((k : ℝ) + 1) / 2 ^ n := by
  simp only [dyq, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_pow,
    NNReal.coe_ofNat]

theorem dyF_coe (n : ℕ) (t : ℝ≥0) :
    (dyF n t : ℝ) = ((⌊(2 : ℝ) ^ n * t⌋₊ : ℝ) + 1) / 2 ^ n := by
  rw [dyF, dyq_coe, dyIdx]

theorem lt_dyF (n : ℕ) (t : ℝ≥0) : t < dyF n t := by
  rw [← NNReal.coe_lt_coe, dyF_coe, lt_div_iff₀ (by positivity), mul_comm]
  exact Nat.lt_floor_add_one _

theorem dyF_le (n : ℕ) (t : ℝ≥0) : dyF n t ≤ t + 1 / 2 ^ n := by
  rw [← NNReal.coe_le_coe, dyF_coe]
  push_cast
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2, add_mul, one_div_mul_cancel h2.ne']
  have := Nat.floor_le (show (0 : ℝ) ≤ 2 ^ n * t by positivity)
  linarith [mul_comm ((t : ℝ)) (2 ^ n)]

theorem dyF_succ_le (n : ℕ) (t : ℝ≥0) : dyF (n + 1) t ≤ dyF n t := by
  rw [← NNReal.coe_le_coe, dyF_coe, dyF_coe]
  set x : ℝ := 2 ^ n * t with hx
  have hx0 : 0 ≤ x := by positivity
  have h2x : (2 : ℝ) ^ (n + 1) * t = 2 * x := by rw [hx, pow_succ]; ring
  rw [h2x]
  -- `⌊2x⌋ ≤ 2⌊x⌋ + 1`
  have hfl : (⌊2 * x⌋₊ : ℝ) ≤ 2 * ⌊x⌋₊ + 1 := by
    have h1 : 2 * x < 2 * (⌊x⌋₊ : ℝ) + 2 := by
      have := Nat.lt_floor_add_one x
      linarith
    have h3 : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      linarith
    have h4 : ⌊2 * x⌋₊ ≤ 2 * ⌊x⌋₊ + 1 := by omega
    exact_mod_cast h4
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_div_iff₀ (by positivity) h2, pow_succ]
  nlinarith

theorem antitone_dyF (t : ℝ≥0) : Antitone fun n => dyF n t :=
  antitone_nat_of_succ_le fun n => dyF_succ_le n t

theorem tendsto_dyF (t : ℝ≥0) : Tendsto (fun n => dyF n t) atTop (𝓝 t) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hup : Tendsto (fun n : ℕ => t + 1 / 2 ^ n) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (lt_dyF n t).le)
    fun n => dyF_le n t

theorem measurable_dyIdx (n : ℕ) : Measurable (dyIdx n) :=
  Nat.measurable_floor.comp (measurable_const.mul measurable_coe_nnreal_real)

/-- The level sets of the dyadic index: `⌊2ⁿ t⌋ = k ↔ k/2ⁿ ≤ t < (k+1)/2ⁿ`. -/
theorem dyIdx_eq_iff {n k : ℕ} {t : ℝ≥0} : dyIdx n t = k ↔ (k : ℝ≥0) / 2 ^ n ≤ t ∧ t < dyq n k := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyIdx, Nat.floor_eq_iff (by positivity), ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, dyq_coe]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
  rw [div_le_iff₀ h2, lt_div_iff₀ h2, mul_comm (t : ℝ)]

/-! ### The optional passage -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Optional passage along strict upper dyadic times** (no monotonicity of the `𝓜 n k` and no measurability of the
events `Av q` is needed: only the pieces are, up to null sets, in the σ-algebras). -/
theorem setIntegral_eq_of_dyadic {X : Ω → ℂ} (hX : Integrable X μ) (hXb : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ 1)
    (𝓜 : ℕ → ℕ → MeasurableSpace Ω) (h𝓜 : ∀ n k, 𝓜 n k ≤ mΩ) {Av : ℝ≥0 → Set Ω}
    {F : ℝ≥0 → Ω → ℂ} (hFb : ∀ q ω, ω ∈ Av q → ‖F q ω‖ ≤ 1)
    (hdet : ∀ n k, ∀ᵐ ω ∂μ, ω ∈ Av (dyq n k) → μ[X | 𝓜 n k] ω = F (dyq n k) ω)
    {θ : Ω → ℝ≥0} (hθ : Measurable θ) {D : Set Ω} (hD : MeasurableSet D)
    (hmeas : ∀ n k, ∃ B, MeasurableSet[𝓜 n k] B ∧
      B =ᵐ[μ] (D ∩ {ω | dyIdx n (θ ω) = k} ∩ Av (dyq n k)))
    {G : Ω → ℂ}
    (hlim : ∀ᵐ ω ∂μ, ω ∈ D → (∀ᶠ n in atTop, ω ∈ Av (dyF n (θ ω))) ∧
      Tendsto (fun n => F (dyF n (θ ω)) ω) atTop (𝓝 (G ω))) :
    ∫ ω in D, X ω ∂μ = ∫ ω in D, G ω ∂μ := by
  classical
  have hidx : ∀ n, Measurable fun ω => dyIdx n (θ ω) := fun n => (measurable_dyIdx n).comp hθ
  set Dk : ℕ → ℕ → Set Ω := fun n k => D ∩ {ω | dyIdx n (θ ω) = k} ∩ Av (dyq n k) with hDk_def
  have hDk : ∀ n k, NullMeasurableSet (Dk n k) μ := fun n k => by
    obtain ⟨B, hBm, hBeq⟩ := hmeas n k
    exact (h𝓜 n k _ hBm).nullMeasurableSet.congr hBeq
  set Dn : ℕ → Set Ω := fun n => ⋃ k, Dk n k with hDn_def
  have hDn : ∀ n, NullMeasurableSet (Dn n) μ := fun n => NullMeasurableSet.iUnion (hDk n)
  have hmemDn : ∀ n ω, ω ∈ Dn n ↔ ω ∈ D ∧ ω ∈ Av (dyF n (θ ω)) := fun n ω => by
    simp only [hDn_def, hDk_def, mem_iUnion, mem_inter_iff, mem_ofPred_eq, dyF]
    constructor
    · rintro ⟨k, ⟨hD', rfl⟩, hA⟩
      exact ⟨hD', hA⟩
    · rintro ⟨hD', hA⟩
      exact ⟨_, ⟨hD', rfl⟩, hA⟩
  have hdisj : ∀ n, Pairwise (Function.onFun (AEDisjoint μ) (Dk n)) := fun n k l hkl => by
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun ω hk hl => hkl ?_)
    exact hk.1.2.symm.trans hl.1.2
  obtain ⟨C, hC_def⟩ : ∃ C : ℕ → ℕ → Ω → ℂ, C = fun n k => μ[X | 𝓜 n k] := ⟨_, rfl⟩
  have hCm : ∀ n k, Measurable (C n k) := fun n k => by
    rw [hC_def]
    exact (stronglyMeasurable_condExp.mono (h𝓜 _ _)).measurable
  obtain ⟨f, hf_def⟩ : ∃ f : ℕ → Ω → ℂ, f = fun n ω => C n (dyIdx n (θ ω)) ω := ⟨_, rfl⟩
  have hfm : ∀ n, Measurable (f n) := fun n => by
    have h := measurable_from_prod_countable_left (f := fun p : Ω × ℕ => C n p.2 p.1)
      (fun k => hCm n k)
    rw [hf_def]
    exact h.comp (measurable_id.prodMk (hidx n))
  obtain ⟨Z, hZ_def⟩ : ∃ Z : ℕ → Ω → ℂ, Z = fun n => (Dn n).indicator (f n) := ⟨_, rfl⟩
  -- the identity on the pieces
  have hall : ∀ᵐ ω ∂μ, ∀ n k, ω ∈ Av (dyq n k) → C n k ω = F (dyq n k) ω := by
    rw [hC_def]
    exact ae_all_iff.2 fun n => ae_all_iff.2 fun k => hdet n k
  have hZF : ∀ᵐ ω ∂μ, ∀ n, ω ∈ Dn n → f n ω = F (dyF n (θ ω)) ω := by
    filter_upwards [hall] with ω hω n hn
    rw [hf_def]
    exact hω n _ ((hmemDn n ω).1 hn).2
  have hZb : ∀ n, ∀ᵐ ω ∂μ, ‖Z n ω‖ ≤ 1 := fun n => by
    filter_upwards [hZF] with ω hω
    by_cases hn : ω ∈ Dn n
    · simp only [hZ_def]
      rw [indicator_of_mem hn, hω n hn]
      exact hFb _ _ ((hmemDn n ω).1 hn).2
    · simp only [hZ_def]
      rw [indicator_of_notMem hn, norm_zero]
      exact zero_le_one
  have hZm : ∀ n, AEStronglyMeasurable (Z n) μ := fun n => by
    rw [hZ_def]
    exact (hfm n).aestronglyMeasurable.indicator₀ (hDn n)
  have hZi : ∀ n, Integrable (Z n) μ := fun n => Integrable.of_bound (hZm n) 1 (hZb n)
  -- step (a): `∫_{Dₙ} X = ∫ Zₙ`
  have ha : ∀ n, ∫ ω in Dn n, X ω ∂μ = ∫ ω, Z n ω ∂μ := by
    intro n
    have hfi : IntegrableOn (f n) (Dn n) μ := by
      refine Integrable.of_bound (hfm n).aestronglyMeasurable 1 ?_
      rw [ae_restrict_iff'₀ (hDn n)]
      filter_upwards [hZF] with ω hω hn
      rw [hω n hn]
      exact hFb _ _ ((hmemDn n ω).1 hn).2
    rw [hZ_def, integral_indicator₀ (hDn n), integral_iUnion_ae (hDk n) (hdisj n) hX.integrableOn,
      integral_iUnion_ae (hDk n) (hdisj n) hfi]
    congr 1
    funext k
    obtain ⟨B, hBm, hBeq⟩ := hmeas n k
    have hfk : ∫ ω in Dk n k, f n ω ∂μ = ∫ ω in Dk n k, C n k ω ∂μ :=
      setIntegral_congr_fun₀ (hDk n k) fun ω hω => by
        rw [hf_def]
        simp only
        rw [hω.1.2]
    rw [hfk, ← setIntegral_congr_set hBeq, ← setIntegral_congr_set hBeq, hC_def]
    have : IsFiniteMeasure (μ.trim (h𝓜 n k)) := isFiniteMeasure_trim (h𝓜 _ _)
    exact (setIntegral_condExp (h𝓜 _ _) hX hBm).symm
  -- step (b): the two limits
  have hlimX : Tendsto (fun n => ∫ ω in Dn n, X ω ∂μ) atTop (𝓝 (∫ ω in D, X ω ∂μ)) := by
    simp only [← integral_indicator₀ (hDn _), ← integral_indicator hD]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => hX.aestronglyMeasurable.indicator₀ (hDn n)) (integrable_const 1)
      (fun n => ?_) ?_
    · filter_upwards [hXb] with ω hω
      by_cases hn : ω ∈ Dn n
      · rw [indicator_of_mem hn]; exact hω
      · rw [indicator_of_notMem hn, norm_zero]; exact zero_le_one
    · filter_upwards [hlim] with ω hω
      by_cases hωD : ω ∈ D
      · obtain ⟨hev, -⟩ := hω hωD
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        show D.indicator X ω = (Dn n).indicator X ω
        rw [indicator_of_mem hωD, indicator_of_mem ((hmemDn n ω).2 ⟨hωD, hn⟩)]
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
        show D.indicator X ω = (Dn n).indicator X ω
        rw [indicator_of_notMem hωD, indicator_of_notMem fun h => hωD ((hmemDn n ω).1 h).1]
  have hlimZ : Tendsto (fun n => ∫ ω, Z n ω ∂μ) atTop (𝓝 (∫ ω in D, G ω ∂μ)) := by
    rw [← integral_indicator hD]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      hZm (integrable_const 1) hZb ?_
    filter_upwards [hlim, hZF] with ω hω hωF
    by_cases hωD : ω ∈ D
    · obtain ⟨hev, hF⟩ := hω hωD
      rw [indicator_of_mem hωD]
      refine hF.congr' ?_
      filter_upwards [hev] with n hn
      have hn' : ω ∈ Dn n := (hmemDn n ω).2 ⟨hωD, hn⟩
      simp only [hZ_def]
      rw [indicator_of_mem hn', hωF n hn']
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      simp only [hZ_def]
      rw [indicator_of_notMem hωD, indicator_of_notMem fun h => hωD ((hmemDn n ω).1 h).1]
  exact tendsto_nhds_unique (hlimX.congr fun n => ha n) hlimZ

/-- **The conditional expectation from set integrals on an event.** -/
theorem ae_condExp_eq_of_forall_setIntegral {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {E : Set Ω}
    (hE : MeasurableSet[m] E) {X G : Ω → ℂ} (hX : Integrable X μ)
    (hG : StronglyMeasurable[m] (E.indicator G)) (hGi : Integrable (E.indicator G) μ)
    (h : ∀ A, MeasurableSet[m] A → ∫ ω in A ∩ E, X ω ∂μ = ∫ ω in A ∩ E, G ω ∂μ) :
    ∀ᵐ ω ∂μ, ω ∈ E → μ[X | m] ω = G ω := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have h1 : μ[E.indicator X | m] =ᵐ[μ] E.indicator (μ[X | m]) := condExp_indicator hX hE
  have h2 : E.indicator G =ᵐ[μ] μ[E.indicator X | m] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm (hX.indicator (hm _ hE))
      (fun A _ _ => hGi.integrableOn) (fun A hA _ => ?_) hG.aestronglyMeasurable
    rw [setIntegral_indicator (hm _ hE), setIntegral_indicator (hm _ hE), h A hA]
  filter_upwards [h1, h2] with ω h1 h2 hω
  have h3 := h2.trans h1
  rw [indicator_of_mem hω, indicator_of_mem hω] at h3
  exact h3.symm

end InteractingSLE.WangWu.ChartConst
