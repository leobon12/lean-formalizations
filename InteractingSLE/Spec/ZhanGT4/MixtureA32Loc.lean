/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualGirsanovQ

/-!
# Girsanov for a driver log-field up to a fixed horizon, from a localizing sequence

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L677–L684, ruling R38): "The function `f` is bounded, and
`∂_u X_t ≤ e^{t/2}`; hence `M_t(u)` is a true martingale on every fixed finite horizon. Girsanov with density
`M_t(u)/f(u)` changes the strip driver …".

PROVE-ZHAN-GT4-A9's Girsanov theorem (`IsDriverLogField.isFilteredBrownianReal_girsProcess`) needs a log-field `ℓ`
that is *bounded* up to the stopping time. The log of the A.3.2 density, `log f(X_t) + ∫₀ᵗ ½ sech²(X/2)`, is bounded
above but not below. This file removes the localization: if `ℓ` is a driver log-field up to each `S_n ≤ T`, every
path has `S_n = T` for all large `n`, the density `exp(ℓ(r, σB_r) − ℓ(0, σB_0))` is bounded by `e^C` and the drift rate
`σ ℓ_x(r, σB_r)` by `C'` for `r ≤ T`, then dominated convergence passes A9's identities to the horizon `T`:

* `isFilteredBrownianReal_girsProcess_const`: under `Q_T = exp(ℓ(T, σB_T) − ℓ(0, σB_0)) · P` (a probability
  measure), `B − ∫₀^{·∧T} σ ℓ_x(u, σB_u) du` is a Brownian motion of `𝓕`;
* `martingale_locN_const`: `exp(ℓ(t ∧ T, σB_{t∧T}) − ℓ(0, σB_0))` is a (true) `𝓕`-martingale under `P`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {σ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ℓ ℓx : Ω → ℝ → ℝ → ℝ}

/-- The stopped density `exp(ℓ(t ∧ S, σB_{t∧S}) − ℓ(0, σB_0))`. -/
def locN (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ : Ω → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (ℓ ω (min t (S ω) : ℝ≥0) (σ * B (min t (S ω)) ω) - ℓ ω 0 (σ * B 0 ω))

omit mΩ in
theorem girsDensity_congr {S S' : Ω → ℝ≥0} {ω : Ω} (h : S ω = S' ω) :
    girsDensity σ B S ℓ ω = girsDensity σ B S' ℓ ω := by
  simp only [girsDensity, h]

omit mΩ in
theorem girsProcess_congr {S S' : Ω → ℝ≥0} {ω : Ω} (h : S ω = S' ω) (t : ℝ≥0) :
    girsProcess σ B S ℓx t ω = girsProcess σ B S' ℓx t ω := by
  simp only [girsProcess, drvInt, drvTheta, h]

omit mΩ in
theorem locN_congr {S S' : Ω → ℝ≥0} {ω : Ω} (h : S ω = S' ω) (t : ℝ≥0) :
    locN σ B S ℓ t ω = locN σ B S' ℓ t ω := by
  simp only [locN, h]

omit mΩ in
theorem girsN_zero_eq_locN (hσ : σ ≠ 0) (S : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    girsN σ 0 B S ℓ ℓx t ω = locN σ B S ℓ t ω := by
  rw [girsN_zero_eq hσ, locN]

omit mΩ in
theorem girsDensity_const_eq_locN (T : ℝ≥0) (ω : Ω) :
    girsDensity σ B (fun _ => T) ℓ ω = locN σ B (fun _ => T) ℓ T ω := by
  simp only [girsDensity, locN, min_self]

omit mΩ in
/-- The cut drift rate is bounded by `C'` when the rate is bounded by `C'` up to `T ≥ S`. -/
theorem abs_drvTheta_le_of {S : Ω → ℝ≥0} {T : ℝ≥0} {ω : Ω} (hST : S ω ≤ T) {C' : ℝ} (hC'0 : 0 ≤ C')
    (hC' : ∀ r : ℝ≥0, r ≤ T → |σ * ℓx ω r (σ * B r ω)| ≤ C') (r : ℝ≥0) : |drvTheta σ B S ℓx r ω| ≤ C' := by
  unfold drvTheta
  split_ifs with h
  · simp only [drvRate, Real.toNNReal_coe]
    exact hC' r (h.le.trans hST)
  · simpa using hC'0

omit mΩ in
theorem abs_drvInt_le_of {S : Ω → ℝ≥0} {T : ℝ≥0} {ω : Ω} (hST : S ω ≤ T) {C' : ℝ} (hC'0 : 0 ≤ C')
    (hC' : ∀ r : ℝ≥0, r ≤ T → |σ * ℓx ω r (σ * B r ω)| ≤ C') {t : ℝ} (ht : 0 ≤ t) :
    |drvInt σ B S ℓx ω t| ≤ C' * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C')
    (f := fun u : ℝ => drvTheta σ B S ℓx u.toNNReal ω) fun u _ => by
      rw [Real.norm_eq_abs]; exact abs_drvTheta_le_of hST hC'0 hC' _
  rwa [sub_zero, abs_of_nonneg ht] at h

/-- The exponential `exp(aY_t − a²t/2)` of the Girsanov process is the Wald exponential times `e^{−aI_t}`, so it is at
most `e^{|a| C' t}` times the Wald exponential. -/
theorem exp_girsProcess_le {S : Ω → ℝ≥0} {T : ℝ≥0} {ω : Ω} (hST : S ω ≤ T) {C' : ℝ} (hC'0 : 0 ≤ C')
    (hC' : ∀ r : ℝ≥0, r ≤ T → |σ * ℓx ω r (σ * B r ω)| ≤ C') (a : ℝ) (t : ℝ≥0) :
    Real.exp (a * girsProcess σ B S ℓx t ω - a ^ 2 * (t : ℝ) / 2) ≤
      Real.exp (|a| * (C' * t)) * wald a B t ω := by
  have hI := abs_drvInt_le_of hST hC'0 hC' t.coe_nonneg (ω := ω)
  have h1 : -(a * drvInt σ B S ℓx ω t) ≤ |a| * (C' * t) := by
    have := neg_abs_le (a * drvInt σ B S ℓx ω t)
    rw [abs_mul] at this
    nlinarith [abs_nonneg a]
  rw [wald, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  simp only [girsProcess]
  linarith

section Main

variable {P : Measure Ω} {ρ : ℝ} {ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} {S : ℕ → Ω → ℝ≥0} {T : ℝ≥0} {K : ℕ → ℝ}
  {C C' : ℝ}

/-- The dominated-convergence step: `∫_A exp(aY^n_t − a²t/2) D_n dP → ∫_A exp(aY_t − a²t/2) D dP`. -/
theorem tendsto_setIntegral_girs (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hσ : 0 < σ) (hρ : 0 < ρ) (hL : ∀ n, IsDriverLogField 𝓕 σ ρ (K n) B (S n) ℓ ℓx ℓxx ℓxxx ℓt)
    (hS : ∀ n, IsStoppingTime 𝓕 fun ω => (S n ω : WithTop ℝ≥0)) (hST : ∀ n ω, S n ω ≤ T)
    (hev : ∀ ω, ∀ᶠ n in atTop, S n ω = T)
    (hC : ∀ ω (r : ℝ≥0), r ≤ T → ℓ ω r (σ * B r ω) - ℓ ω 0 (σ * B 0 ω) ≤ C)
    (hC'0 : 0 ≤ C') (hC' : ∀ ω (r : ℝ≥0), r ≤ T → |σ * ℓx ω r (σ * B r ω)| ≤ C')
    (a : ℝ) (t : ℝ≥0) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, Real.exp (a * girsProcess σ B (S n) ℓx t ω - a ^ 2 * (t : ℝ) / 2) *
        girsDensity σ B (S n) ℓ ω ∂P) atTop
      (𝓝 (∫ ω in A, Real.exp (a * girsProcess σ B (fun _ => T) ℓx t ω - a ^ 2 * (t : ℝ) / 2) *
        girsDensity σ B (fun _ => T) ℓ ω ∂P)) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hDm : ∀ n, Measurable (girsDensity σ B (S n) ℓ) := fun n => by
    have hmR := ((hL n).measurable_girsN_zero hBc hσ.ne' hρ (hS n) T).mono (𝓕.le T) le_rfl
    have e : girsDensity σ B (S n) ℓ = girsN σ 0 B (S n) ℓ ℓx T :=
      funext fun ω => girsDensity_eq_girsN hσ.ne' (hST n ω)
    rw [e]; exact hmR
  have hYm : ∀ n, Measurable (girsProcess σ B (S n) ℓx t) := fun n =>
    (((hL n).stronglyAdapted_girsProcess hBc hBm hρ (hS n) t).measurable).mono (𝓕.le t) le_rfl
  refine tendsto_integral_of_dominated_convergence
    (fun ω => Real.exp C * Real.exp (|a| * (C' * t)) * wald a B t ω) (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact ((Real.continuous_exp.measurable.comp (((hYm n).const_mul a).sub_const _)).mul
      (hDm n)).aestronglyMeasurable
  · exact (((martingale_wald hB a).integrable t).const_mul _).integrableOn
  · refine ae_of_all _ fun ω => ?_
    have hD : girsDensity σ B (S n) ℓ ω ≤ Real.exp C := Real.exp_le_exp.2 (hC ω _ (hST n ω))
    have hE := exp_girsProcess_le (hST n ω) hC'0 (hC' ω) a t (ℓx := ℓx)
    have hw : 0 ≤ wald a B t ω := (Real.exp_pos _).le
    have hDp : 0 < girsDensity σ B (S n) ℓ ω := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) hDp)]
    calc Real.exp (a * girsProcess σ B (S n) ℓx t ω - a ^ 2 * (t : ℝ) / 2) * girsDensity σ B (S n) ℓ ω
        ≤ Real.exp (|a| * (C' * t)) * wald a B t ω * Real.exp C :=
          mul_le_mul hE hD (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hw)
      _ = Real.exp C * Real.exp (|a| * (C' * t)) * wald a B t ω := by ring
  · refine ae_of_all _ fun ω => ?_
    refine tendsto_const_nhds.congr' ((hev ω).mono fun n hn => ?_)
    simp only [girsProcess_congr (S' := fun _ => T) hn t, girsDensity_congr (S' := fun _ => T) hn]

/-- **Girsanov up to the fixed horizon `T`** from a localizing sequence (see the module docstring). -/
theorem isFilteredBrownianReal_girsProcess_const (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ)
    (hL : ∀ n, IsDriverLogField 𝓕 σ ρ (K n) B (S n) ℓ ℓx ℓxx ℓxxx ℓt)
    (hS : ∀ n, IsStoppingTime 𝓕 fun ω => (S n ω : WithTop ℝ≥0)) (hST : ∀ n ω, S n ω ≤ T)
    (hev : ∀ ω, ∀ᶠ n in atTop, S n ω = T)
    (hC : ∀ ω (r : ℝ≥0), r ≤ T → ℓ ω r (σ * B r ω) - ℓ ω 0 (σ * B 0 ω) ≤ C)
    (hC'0 : 0 ≤ C') (hC' : ∀ ω (r : ℝ≥0), r ≤ T → |σ * ℓx ω r (σ * B r ω)| ≤ C') :
    IsProbabilityMeasure (girsMeasure P σ B (fun _ => T) ℓ) ∧
      IsFilteredBrownianReal 𝓕 (girsProcess σ B (fun _ => T) ℓx) (girsMeasure P σ B (fun _ => T) ℓ) := by
  have hP := hB.isProbabilityMeasure'
  have hPB := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hlim := tendsto_setIntegral_girs hB hBc hσ hρ hL hS hST hev hC hC'0 hC'
  -- measurability of the limit objects
  have hDm : ∀ n, Measurable (girsDensity σ B (S n) ℓ) := fun n => by
    have hmR := ((hL n).measurable_girsN_zero hBc hσ.ne' hρ (hS n) T).mono (𝓕.le T) le_rfl
    have e : girsDensity σ B (S n) ℓ = girsN σ 0 B (S n) ℓ ℓx T :=
      funext fun ω => girsDensity_eq_girsN hσ.ne' (hST n ω)
    rw [e]; exact hmR
  have hDTm : Measurable (girsDensity σ B (fun _ => T) ℓ) :=
    measurable_of_tendsto_metrizable hDm (tendsto_pi_nhds.2 fun ω =>
      tendsto_const_nhds.congr' ((hev ω).mono fun n hn => (girsDensity_congr (S' := fun _ => T) hn).symm))
  have hDTpos : ∀ ω, 0 ≤ girsDensity σ B (fun _ => T) ℓ ω := fun ω => (Real.exp_pos _).le
  have hYTm : ∀ t, Measurable[𝓕 t] (girsProcess σ B (fun _ => T) ℓx t) := fun t =>
    @measurable_of_tendsto_metrizable Ω ℝ (𝓕 t) _ _ _ _ _ _
      (fun n => ((hL n).stronglyAdapted_girsProcess hBc hBm hρ (hS n) t).measurable)
      (tendsto_pi_nhds.2 fun ω =>
        tendsto_const_nhds.congr' ((hev ω).mono fun n hn => (girsProcess_congr (S' := fun _ => T) hn t).symm))
  have hYTc : ∀ ω, Continuous (girsProcess σ B (fun _ => T) ℓx · ω) := fun ω => by
    obtain ⟨n, hn⟩ := (hev ω).exists
    have e : (girsProcess σ B (fun _ => T) ℓx · ω) = (girsProcess σ B (S n) ℓx · ω) :=
      funext fun t => (girsProcess_congr (S' := fun _ => T) hn t).symm
    rw [e]
    exact (hBc ω).sub (((hL n).continuous_drvInt hBc hρ (hS n) ω).comp NNReal.continuous_coe)
  -- each localized identity
  have hstepn : ∀ n (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ ω in A, Real.exp (a * girsProcess σ B (S n) ℓx t ω - a ^ 2 * (t : ℝ) / 2) * girsDensity σ B (S n) ℓ ω ∂P =
        ∫ ω in A, Real.exp (a * girsProcess σ B (S n) ℓx s ω - a ^ 2 * (s : ℝ) / 2) *
          girsDensity σ B (S n) ℓ ω ∂P := by
    intro n a s t hst A hA
    have h := ((hL n).isExpQMartingale_girsProcess hB hBc hσ hρ (hS n) (hST n) t).martingale a hst le_rfl hA
    rwa [girsMeasure, MathFin.setIntegral_withDensity_ofReal (hDm n).aestronglyMeasurable
      (fun ω => (Real.exp_pos _).le) _ (𝓕.le s A hA), MathFin.setIntegral_withDensity_ofReal
      (hDm n).aestronglyMeasurable (fun ω => (Real.exp_pos _).le) _ (𝓕.le s A hA)] at h
  have hstep : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ ω in A, Real.exp (a * girsProcess σ B (fun _ => T) ℓx t ω - a ^ 2 * (t : ℝ) / 2) *
          girsDensity σ B (fun _ => T) ℓ ω ∂P =
        ∫ ω in A, Real.exp (a * girsProcess σ B (fun _ => T) ℓx s ω - a ^ 2 * (s : ℝ) / 2) *
          girsDensity σ B (fun _ => T) ℓ ω ∂P := fun a s t hst A hA =>
    tendsto_nhds_unique ((hlim a t A).congr fun n => hstepn n a hst hA) (hlim a s A)
  -- the total mass
  have hmass : ∫ ω, girsDensity σ B (fun _ => T) ℓ ω ∂P = 1 := by
    have h1 : ∀ n, ∫ ω, girsDensity σ B (S n) ℓ ω ∂P = 1 := fun n => by
      have h := (hL n).integral_mul_girsDensity hB hBc hσ hρ (hS n) (hST n) 0 (Y := fun _ => 1)
        measurable_const (integrable_const 1) (P := P)
      simpa only [one_mul, girsN_zero_at_zero hσ.ne', integral_const, probReal_univ, smul_eq_mul,
        mul_one] using h
    have h2 := hlim 0 0 univ
    simp only [zero_mul, NNReal.coe_zero, mul_zero, zero_div, sub_zero, Real.exp_zero, one_mul,
      Measure.restrict_univ, h1] at h2
    exact (tendsto_nhds_unique tendsto_const_nhds h2).symm
  have hQ : IsProbabilityMeasure (girsMeasure P σ B (fun _ => T) ℓ) := by
    constructor
    rw [girsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hDi : Integrable (girsDensity σ B (fun _ => T) ℓ) P := by
      refine ⟨hDTm.aestronglyMeasurable, ?_⟩
      refine (hasFiniteIntegral_const (Real.exp C)).mono' (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (show 0 < girsDensity σ B (fun _ => T) ℓ ω from Real.exp_pos _)]
      exact Real.exp_le_exp.2 (hC ω T le_rfl)
    rw [← ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall hDTpos), hmass, ENNReal.ofReal_one]
  refine ⟨hQ, ?_⟩
  have hAd : StronglyAdapted 𝓕 (girsProcess σ B (fun _ => T) ℓx) := fun t => (hYTm t).stronglyMeasurable
  have hall : ∀ T', MathFin.IsExpQMartingale (girsMeasure P σ B (fun _ => T) ℓ) 𝓕
      (girsProcess σ B (fun _ => T) ℓx) T' := fun T' => by
    refine ⟨hAd, ?_, fun a s t hst _ A hA => ?_⟩
    · have hac : girsMeasure P σ B (fun _ => T) ℓ ≪ P := withDensity_absolutelyContinuous _ _
      filter_upwards [hac.ae_le (MathFin.X0_ae_eq_zero (X := B) (𝓕 := 𝓕) (P := P))] with ω hω
      simp [girsProcess, drvInt_zero, hω]
    · rw [girsMeasure, MathFin.setIntegral_withDensity_ofReal hDTm.aestronglyMeasurable hDTpos _ (𝓕.le s A hA),
        MathFin.setIntegral_withDensity_ofReal hDTm.aestronglyMeasurable hDTpos _ (𝓕.le s A hA)]
      exact hstep a hst hA
  exact ⟨MathFin.isBrownianReal_of_expMartingale hall (ae_of_all _ hYTc), hAd.adapted,
    (MathFin.isFilteredPreBrownian_of_expMartingale hall).indep⟩

/-- **The density process is a true martingale** up to the fixed horizon `T`:
`exp(ℓ(t ∧ T, σB_{t∧T}) − ℓ(0, σB_0))` is an `𝓕`-martingale, from a localizing sequence. -/
theorem martingale_locN_const (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ)
    (hL : ∀ n, IsDriverLogField 𝓕 σ ρ (K n) B (S n) ℓ ℓx ℓxx ℓxxx ℓt)
    (hS : ∀ n, IsStoppingTime 𝓕 fun ω => (S n ω : WithTop ℝ≥0)) (hST : ∀ n ω, S n ω ≤ T)
    (hev : ∀ ω, ∀ᶠ n in atTop, S n ω = T)
    (hC : ∀ ω (r : ℝ≥0), r ≤ T → ℓ ω r (σ * B r ω) - ℓ ω 0 (σ * B 0 ω) ≤ C)
    (hC'0 : 0 ≤ C') (hC' : ∀ ω (r : ℝ≥0), r ≤ T → |σ * ℓx ω r (σ * B r ω)| ≤ C') :
    Martingale (locN σ B (fun _ => T) ℓ) 𝓕 P := by
  have hP := hB.isProbabilityMeasure'
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hlim := tendsto_setIntegral_girs hB hBc hσ hρ hL hS hST hev hC hC'0 hC'
  -- adaptedness and bounds of the limit process
  have hNm : ∀ n t, Measurable[𝓕 t] (locN σ B (S n) ℓ t) := fun n t => by
    have h := (hL n).measurable_girsN_zero hBc hσ.ne' hρ (hS n) t
    have e : girsN σ 0 B (S n) ℓ ℓx t = locN σ B (S n) ℓ t := funext fun ω => girsN_zero_eq_locN hσ.ne' _ t ω
    rwa [e] at h
  have hNTm : ∀ t, Measurable[𝓕 t] (locN σ B (fun _ => T) ℓ t) := fun t =>
    @measurable_of_tendsto_metrizable Ω ℝ (𝓕 t) _ _ _ _ _ _ (fun n => hNm n t)
      (tendsto_pi_nhds.2 fun ω => tendsto_const_nhds.congr' ((hev ω).mono fun n hn => (locN_congr (S' := fun _ => T) hn t).symm))
  have hNb : ∀ {S' : Ω → ℝ≥0}, (∀ ω, S' ω ≤ T) → ∀ t ω, |locN σ B S' ℓ t ω| ≤ Real.exp C := fun {S'} hS' t ω => by
    rw [locN, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hC ω _ ((min_le_right _ _).trans (hS' ω)))
  have hNi : ∀ {S' : Ω → ℝ≥0}, (∀ ω, S' ω ≤ T) → ∀ t, Measurable (locN σ B S' ℓ t) →
      Integrable (locN σ B S' ℓ t) P := fun {S'} hS' t hm =>
    (integrable_const (Real.exp C)).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hNb hS' t ω)
  -- `∫_A D = ∫_A N_t` for `A ∈ 𝓕_t`
  have hkey : ∀ (t : ℝ≥0) {A : Set Ω}, MeasurableSet[𝓕 t] A →
      ∫ ω in A, locN σ B (fun _ => T) ℓ t ω ∂P = ∫ ω in A, girsDensity σ B (fun _ => T) ℓ ω ∂P := by
    intro t A hA
    have hAm : MeasurableSet A := 𝓕.le t A hA
    have hn : ∀ n, ∫ ω in A, locN σ B (S n) ℓ t ω ∂P = ∫ ω in A, girsDensity σ B (S n) ℓ ω ∂P := fun n => by
      have h := (hL n).integral_mul_girsDensity hB hBc hσ hρ (hS n) (hST n) t (Y := A.indicator fun _ => 1)
        ((measurable_const.indicator hA)) ((integrable_const 1).indicator hAm) (P := P)
      have e : ∀ F : Ω → ℝ, (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * F ω) = A.indicator F := fun F => by
        funext ω; by_cases hω : ω ∈ A <;> simp [hω]
      rw [e, e, integral_indicator hAm, integral_indicator hAm] at h
      rw [h]
      refine setIntegral_congr_fun hAm fun ω _ => (girsN_zero_eq_locN hσ.ne' _ t ω).symm
    have h1 : Tendsto (fun n => ∫ ω in A, locN σ B (S n) ℓ t ω ∂P) atTop
        (𝓝 (∫ ω in A, locN σ B (fun _ => T) ℓ t ω ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp C) (fun n => ?_)
        (integrable_const _).integrableOn (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
      · exact ((hNm n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hNb (hST n) t ω
      · exact tendsto_const_nhds.congr' ((hev ω).mono fun n hn => (locN_congr (S' := fun _ => T) hn t).symm)
    have h2 := hlim 0 0 A
    simp only [zero_mul, NNReal.coe_zero, mul_zero, zero_div, sub_zero, Real.exp_zero, one_mul] at h2
    exact tendsto_nhds_unique (h1.congr hn) h2
  refine ⟨fun t => (hNTm t).stronglyMeasurable, fun s t hst => ?_⟩
  have hit := hNi (fun _ => le_rfl) t ((hNTm t).mono (𝓕.le t) le_rfl)
  have his := hNi (fun _ => le_rfl) s ((hNTm s).mono (𝓕.le s) le_rfl)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hit (fun A _ _ => his.integrableOn)
    (fun A hA _ => ?_) (hNTm s).stronglyMeasurable.aestronglyMeasurable).symm
  rw [hkey t (𝓕.mono hst A hA), hkey s hA]

end Main

end InteractingSLE.ZhanGT4.Mix
