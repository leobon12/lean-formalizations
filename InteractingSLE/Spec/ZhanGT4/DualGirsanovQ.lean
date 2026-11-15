/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualGirsanovLim

/-!
# Girsanov with the other curve frozen, III: the tilted measure

Packet PROVE-ZHAN-GT4-A9. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L341–L351, R38):
"By (D8) and Girsanov, with the other curve stopped, the new drift of `W_j` is `κ_j q_j`."

For a driver log-field `ℓ` up to a stopping time `S ≤ R` (the logarithm of `M̃` with the other curve frozen, A8),
let `D = M_S/M_0 = exp(ℓ(S, σB_S) − ℓ(0, σB_0))` and `Q = D · P`. Then the process `X_t = B_t − I_t`,
`I_t = ∫₀^{t∧S} σ ∂_xℓ(u, σB_u) du`, is a Brownian motion of `𝓕` under `Q`
(**`isFilteredBrownianReal_girsProcess`**): the driver `W = σB = σX + σI` acquires the drift `σ² ∂_xℓ = κ q_j`.

Proof (no stochastic integrals): `Q` has mass one and Bayes' formula `E_Q[Y] = E_P[Y N^0_t]` holds for
`𝓕_t`-measurable integrable `Y` (`N^0 = M_{·∧S}/M_0` is the conditional expectation of `D`); then
`N^0_t exp(aX_t − a²t/2) = R_{t∧S} E_t` with `E_t = exp(aB_t − a²t/2)` (MathFin's Wald martingale) and `R` bounded; its
part up to `S` is the tilted martingale of `DualGirsanovLim`, its part after `S` has zero mean by optional sampling of
`E` at `t ∧ S` (`Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Definitions -/

/-- **The Girsanov density** `D = M_S/M_0 = exp(ℓ(S, σB_S) − ℓ(0, σB_0))`. -/
def girsDensity (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ : Ω → ℝ → ℝ → ℝ) (ω : Ω) : ℝ :=
  Real.exp (ℓ ω (S ω) (σ * B (S ω) ω) - ℓ ω 0 (σ * B 0 ω))

/-- **The tilted measure** `Q = D · P`. -/
def girsMeasure (P : Measure Ω) (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ : Ω → ℝ → ℝ → ℝ) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (girsDensity σ B S ℓ ω)

/-- **The Girsanov process** `X_t = B_t − I_t`. -/
def girsProcess (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓx : Ω → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω - drvInt σ B S ℓx ω t

/-- The stopped tilted exponential `N^a_{u∧S}`. -/
def girsN (σ a : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx : Ω → ℝ → ℝ → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  logFieldExp σ B (tiltL σ a B S ℓ ℓx) (min u (S ω)) ω

omit mΩ in
theorem girsN_zero_eq {σ : ℝ} (hσ : σ ≠ 0) {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0} {ℓ ℓx : Ω → ℝ → ℝ → ℝ} (u : ℝ≥0)
    (ω : Ω) : girsN σ 0 B S ℓ ℓx u ω =
      Real.exp (ℓ ω ((min u (S ω) : ℝ≥0) : ℝ) (σ * B (min u (S ω)) ω) - ℓ ω 0 (σ * B 0 ω)) := by
  rw [girsN, logFieldExp_tilt hσ]
  simp only [zero_mul, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]

omit mΩ in
theorem girsDensity_eq_girsN {σ : ℝ} (hσ : σ ≠ 0) {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0} {ℓ ℓx : Ω → ℝ → ℝ → ℝ}
    {T : ℝ≥0} {ω : Ω} (hT : S ω ≤ T) : girsDensity σ B S ℓ ω = girsN σ 0 B S ℓ ℓx T ω := by
  rw [girsN_zero_eq hσ, min_eq_right hT, girsDensity]

omit mΩ in
theorem girsN_zero_at_zero {σ : ℝ} (hσ : σ ≠ 0) {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0} {ℓ ℓx : Ω → ℝ → ℝ → ℝ}
    (ω : Ω) : girsN σ 0 B S ℓ ℓx 0 ω = 1 := by
  rw [girsN_zero_eq hσ, min_eq_left zero_le]; simp

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}

/-! ### The density process -/

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- `N^0_{u∧S} = M_{u∧S} e^{−ℓ(0, σB_0)}` is bounded by `e^{2K}`. -/
theorem abs_girsN_zero_le (hσ : σ ≠ 0) (hρ : 0 < ρ) (u : ℝ≥0) (ω : Ω) : |girsN σ 0 B S ℓ ℓx u ω| ≤ Real.exp (2 * K) := by
  rw [girsN_zero_eq hσ, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  have h1 := hL.abs_le hρ ω ⟨(min u (S ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
  have h0 := hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩
  simp only [Real.toNNReal_coe] at h1
  simp only [Real.toNNReal_zero] at h0
  linarith [(_root_.abs_le.1 h1).2, (_root_.abs_le.1 h0).1]

/-- `N^0_{u∧S}` is adapted. -/
theorem measurable_girsN_zero (hBc : ∀ ω, Continuous (B · ω)) (hσ : σ ≠ 0)
    (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (u : ℝ≥0) :
    Measurable[𝓕 u] (girsN σ 0 B S ℓ ℓx u) := by
  have hM := hL.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) u
  have hc : Measurable[𝓕 u] fun ω => ℓ ω 0 (σ * B 0 ω) := by
    have h := hL.meas0 0
    have e : {ω | (0 : ℝ≥0) ≤ S ω}.indicator (fun ω => ℓ ω ((0 : ℝ≥0) : ℝ) (σ * B 0 ω)) =
        fun ω => ℓ ω 0 (σ * B 0 ω) := by
      funext ω; rw [indicator_of_mem (by simp : ω ∈ {ω | (0 : ℝ≥0) ≤ S ω})]; rfl
    rw [e] at h
    exact h.mono (𝓕.mono zero_le) le_rfl
  have e : girsN σ 0 B S ℓ ℓx u = fun ω => logFieldExp σ B ℓ (min u (S ω)) ω * Real.exp (-ℓ ω 0 (σ * B 0 ω)) := by
    funext ω
    rw [girsN_zero_eq hσ, logFieldExp, ← Real.exp_add]; ring_nf
  rw [e]
  exact (continuous_mul.measurable).comp (hM.prodMk (Real.continuous_exp.measurable.comp hc.neg))

/-- **The density process is the conditional expectation of `D`**: `N^0_t = E[N^0_T | 𝓕_t]` for `t ≤ T`. -/
theorem girsN_zero_ae_eq_condExp {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) {t T : ℝ≥0} (htT : t ≤ T) :
    girsN σ 0 B S ℓ ℓx t =ᵐ[P] P[girsN σ 0 B S ℓ ℓx T | 𝓕 t] := by
  have hP := hB.isProbabilityMeasure'
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hm := fun u => hL.measurable_girsN_zero hBc hσ.ne' hρ hS u
  have hi : ∀ u, Integrable (girsN σ 0 B S ℓ ℓx u) P := fun u =>
    (integrable_const (Real.exp (2 * K))).mono' ((hm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hL.abs_girsN_zero_le hσ.ne' hρ u ω)
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) (hi T) (fun A _ _ => (hi t).integrableOn)
    (fun A hA _ => ?_) (hm t).stronglyMeasurable.aestronglyMeasurable
  have h := hL.integral_mul_tilt_stopped_eq hB hBc hσ hρ hS hSR 0 htT (ξ := A.indicator fun _ => 1)
    ((measurable_const.indicator hA)) (fun ω => by
      by_cases hω : ω ∈ A <;> simp [hω])
  have e : ∀ u : ℝ≥0, (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      logFieldExp σ B (tiltL σ 0 B S ℓ ℓx) (min u (S ω)) ω) = A.indicator (girsN σ 0 B S ℓ ℓx u) := fun u => by
    funext ω; by_cases hω : ω ∈ A <;> simp [hω, girsN]
  rw [e T, e t, integral_indicator (𝓕.le t A hA), integral_indicator (𝓕.le t A hA)] at h
  exact h.symm

/-- **Bayes' formula for the tilted measure**: `E_P[Y D] = E_P[Y N^0_t]` for every `𝓕_t`-measurable integrable `Y`. -/
theorem integral_mul_girsDensity {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (t : ℝ≥0) {Y : Ω → ℝ} (hYm : Measurable[𝓕 t] Y) (hYi : Integrable Y P) :
    ∫ ω, Y ω * girsDensity σ B S ℓ ω ∂P = ∫ ω, Y ω * girsN σ 0 B S ℓ ℓx t ω ∂P := by
  have hP := hB.isProbabilityMeasure'
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  set T := max t R with hTdef
  have hDT : girsDensity σ B S ℓ = girsN σ 0 B S ℓ ℓx T := funext fun ω =>
    girsDensity_eq_girsN hσ.ne' ((hSR ω).trans (le_max_right _ _))
  have hmT := (hL.measurable_girsN_zero hBc hσ.ne' hρ hS T).mono (𝓕.le T) le_rfl
  have hiT : Integrable (girsN σ 0 B S ℓ ℓx T) P :=
    (integrable_const (Real.exp (2 * K))).mono' hmT.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hL.abs_girsN_zero_le hσ.ne' hρ T ω)
  have hYD : Integrable (Y * girsN σ 0 B S ℓ ℓx T) P :=
    hYi.mul_bdd (c := Real.exp (2 * K)) hmT.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hL.abs_girsN_zero_le hσ.ne' hρ T ω)
  have hce := hL.girsN_zero_ae_eq_condExp hB hBc hσ hρ hS hSR (le_max_left t R) (P := P)
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 t) (μ := P) hYm.stronglyMeasurable hYD hiT
  rw [hDT]
  calc ∫ ω, Y ω * girsN σ 0 B S ℓ ℓx T ω ∂P = ∫ ω, P[Y * girsN σ 0 B S ℓ ℓx T | 𝓕 t] ω ∂P :=
        (integral_condExp (𝓕.le t)).symm
    _ = ∫ ω, Y ω * girsN σ 0 B S ℓ ℓx t ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hce] with ω h1 h2
        rw [h1, Pi.mul_apply, ← h2]

/-- **The tilted measure is a probability measure.** -/
theorem isProbabilityMeasure_girsMeasure {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) : IsProbabilityMeasure (girsMeasure P σ B S ℓ) := by
  have hP := hB.isProbabilityMeasure'
  have h := hL.integral_mul_girsDensity hB hBc hσ hρ hS hSR 0 (Y := fun _ => 1) measurable_const
    (integrable_const 1) (P := P)
  simp only [one_mul, girsN_zero_at_zero hσ.ne', integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  constructor
  rw [girsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hD : ∀ ω, 0 ≤ girsDensity σ B S ℓ ω := fun ω => (Real.exp_pos _).le
  have hDm : AEMeasurable (girsDensity σ B S ℓ) P := by
    have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
    have hmR := (hL.measurable_girsN_zero hBc hσ.ne' hρ hS R).mono (𝓕.le R) le_rfl
    have e : girsDensity σ B S ℓ = girsN σ 0 B S ℓ ℓx R := funext fun ω => girsDensity_eq_girsN hσ.ne' (hSR ω)
    rw [e]; exact hmR.aemeasurable
  have hDi : Integrable (girsDensity σ B S ℓ) P := by
    have := hL.integral_mul_girsDensity hB hBc hσ hρ hS hSR 0 (Y := fun _ => 1) measurable_const
      (integrable_const 1) (P := P)
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    have hle : ∀ ω, ‖girsDensity σ B S ℓ ω‖ ≤ Real.exp (2 * K) := fun ω => by
      have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
      rw [girsDensity_eq_girsN (ℓx := ℓx) hσ.ne' (hSR ω), Real.norm_eq_abs]
      exact hL.abs_girsN_zero_le hσ.ne' hρ R ω
    exact (hasFiniteIntegral_const (Real.exp (2 * K))).mono' (Eventually.of_forall hle)
  rw [← ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall hD), h, ENNReal.ofReal_one]

end IsDriverLogField

/-! ### Tools for the martingale step -/

omit mΩ in
/-- **Pulling a bounded `m`-measurable factor through a conditional expectation** inside an integral. -/
theorem integral_mul_eq_of_ae_eq_condExp {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {X Y G : Ω → ℝ} (hX : X =ᵐ[P] P[Y | m]) (hY : Integrable Y P)
    (hG : StronglyMeasurable[m] G) {c : ℝ} (hGb : ∀ ω, |G ω| ≤ c) :
    ∫ ω, G ω * X ω ∂P = ∫ ω, G ω * Y ω ∂P := by
  have hpull := condExp_stronglyMeasurable_mul_of_bound hm hG hY c
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)
  calc ∫ ω, G ω * X ω ∂P = ∫ ω, P[G * Y | m] ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hX, hpull] with ω h1 h2
        rw [h2, Pi.mul_apply, h1]
    _ = ∫ ω, G ω * Y ω ∂P := integral_condExp hm

/-- The Wald exponential `E_u = exp(aB_u − a²u/2)`. -/
def wald (a : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ := Real.exp (a * B u ω - a ^ 2 * (u : ℝ) / 2)

theorem martingale_wald {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P) (a : ℝ) :
    Martingale (wald a B) 𝓕 P := by
  have := hB.isProbabilityMeasure'
  have := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  exact IsFilteredPreBrownian.waldExponential_isMartingale (X := B) (𝓕 := 𝓕) (P := P) a

omit mΩ in
theorem continuous_wald (hBc : ∀ ω, Continuous (B · ω)) (a : ℝ) (ω : Ω) : Continuous (wald a B · ω) := by
  unfold wald
  have h := hBc ω
  fun_prop

/-- The bounded factor `R_u = N^0_u e^{−a I_{u∧S}}`. -/
def girsR (σ a : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx : Ω → ℝ → ℝ → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  girsN σ 0 B S ℓ ℓx u ω * Real.exp (-(a * drvInt σ B S ℓx ω ((min u (S ω) : ℝ≥0) : ℝ)))

omit mΩ in
theorem girsR_min (σ a : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx : Ω → ℝ → ℝ → ℝ) (u : ℝ≥0) (ω : Ω) :
    girsR σ a B S ℓ ℓx (min u (S ω)) ω = girsR σ a B S ℓ ℓx u ω := by
  simp only [girsR, girsN, min_eq_left (min_le_right u (S ω))]

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

theorem intervalIntegrable_drvTheta (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ω : Ω) (x y : ℝ) :
    IntervalIntegrable (fun u : ℝ => drvTheta σ B S ℓx u.toNNReal ω) volume x y :=
  (intervalIntegrable_const (c := |σ| * K)).mono_fun'
    (Girsanov.measurable_time_of_progressive (hL.isStronglyProgressive_drvTheta hBc hρ hS) ω).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      show ‖drvTheta σ B S ℓx u.toNNReal ω‖ ≤ |σ| * K
      rw [Real.norm_eq_abs]; exact hL.abs_drvTheta_le hρ _ ω)

theorem continuous_drvInt (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ω : Ω) : Continuous (drvInt σ B S ℓx ω) :=
  intervalIntegral.continuous_primitive (fun x y => hL.intervalIntegrable_drvTheta hBc hρ hS ω x y) 0

/-- **The accumulated drift is constant after `S`**: `I_u = I_{u∧S}`. -/
theorem drvInt_min (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ω : Ω) (u : ℝ≥0) :
    drvInt σ B S ℓx ω u = drvInt σ B S ℓx ω ((min u (S ω) : ℝ≥0) : ℝ) := by
  rcases le_total u (S ω) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    unfold drvInt
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (S ω : ℝ))
      (hL.intervalIntegrable_drvTheta hBc hρ hS ω 0 _) (hL.intervalIntegrable_drvTheta hBc hρ hS ω _ _)]
    have hz : ∫ x in (S ω : ℝ)..(u : ℝ), drvTheta σ B S ℓx x.toNNReal ω = 0 := by
      rw [← intervalIntegral.integral_zero (a := (S ω : ℝ)) (b := (u : ℝ)) (μ := volume)]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (NNReal.coe_le_coe.2 h)] at hx
      have hx' : S ω ≤ x.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((S ω).coe_nonneg.trans hx.1)]; exact hx.1
      simp only [drvTheta, not_lt.2 hx', ↓reduceIte]
    rw [hz, add_zero]

/-- `|R_u| ≤ e^{2K} e^{|a| |σ| K R}`. -/
theorem abs_girsR_le (hσ : σ ≠ 0) (hρ : 0 < ρ) {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (a : ℝ) (u : ℝ≥0) (ω : Ω) :
    |girsR σ a B S ℓ ℓx u ω| ≤ Real.exp (2 * K) * Real.exp (|a| * (|σ| * K * R)) := by
  rw [girsR, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (hL.abs_girsN_zero_le hσ hρ u ω) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    (Real.exp_pos _).le
  have hK : 0 ≤ K := (abs_nonneg _).trans (hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩)
  have hI := hL.abs_drvInt_le hρ ω (min u (S ω)).coe_nonneg
  have hτR : (((min u (S ω)) : ℝ≥0) : ℝ) ≤ R := NNReal.coe_le_coe.2 ((min_le_right _ _).trans (hSR ω))
  have h2 : |a * drvInt σ B S ℓx ω ((min u (S ω) : ℝ≥0) : ℝ)| ≤ |a| * (|σ| * K * R) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_left hτR (by positivity))) (abs_nonneg a)
  linarith [neg_abs_le (a * drvInt σ B S ℓx ω ((min u (S ω) : ℝ≥0) : ℝ))]

/-- `R` is adapted. -/
theorem measurable_girsR (hBc : ∀ ω, Continuous (B · ω)) (hσ : σ ≠ 0) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (a : ℝ) (u : ℝ≥0) :
    Measurable[𝓕 u] (girsR σ a B S ℓ ℓx u) := by
  have h1 := hL.measurable_girsN_zero hBc hσ hρ hS u
  have hI := hL.measurable_drvInt hBc hρ hS u
  have e : girsR σ a B S ℓ ℓx u = fun ω => girsN σ 0 B S ℓ ℓx u ω * Real.exp (-(a * drvInt σ B S ℓx ω u)) := by
    funext ω; rw [girsR, ← hL.drvInt_min hBc hρ hS ω u]
  rw [e]
  have hF : Continuous fun p : ℝ × ℝ => p.1 * Real.exp (-(a * p.2)) := by fun_prop
  exact hF.measurable.comp (h1.prodMk hI)

/-- `R` has continuous paths. -/
theorem continuous_girsR (hBc : ∀ ω, Continuous (B · ω)) (hσ : σ ≠ 0) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (a : ℝ) (ω : Ω) :
    Continuous fun u => girsR σ a B S ℓ ℓx u ω := by
  have hm : Continuous fun u : ℝ≥0 => (((min u (S ω)) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hmS : ∀ u : ℝ≥0, (((min u (S ω)) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) := fun u =>
    ⟨(min u (S ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
  have hℓ : Continuous fun u : ℝ≥0 => ℓ ω ((min u (S ω) : ℝ≥0) : ℝ)
      (σ * B (((min u (S ω) : ℝ≥0) : ℝ)).toNNReal ω) :=
    (hL.continuousOn_driver hBc hρ ω).comp_continuous hm hmS
  have hℓ' : Continuous fun u : ℝ≥0 => ℓ ω ((min u (S ω) : ℝ≥0) : ℝ) (σ * B (min u (S ω)) ω) := by
    simpa only [Real.toNNReal_coe] using hℓ
  have hI : Continuous fun u : ℝ≥0 => drvInt σ B S ℓx ω ((min u (S ω) : ℝ≥0) : ℝ) :=
    (hL.continuous_drvInt hBc hρ hS ω).comp hm
  have e : (fun u => girsR σ a B S ℓ ℓx u ω) = fun u => Real.exp (ℓ ω ((min u (S ω) : ℝ≥0) : ℝ)
      (σ * B (min u (S ω)) ω) - ℓ ω 0 (σ * B 0 ω)) * Real.exp (-(a * drvInt σ B S ℓx ω ((min u (S ω) : ℝ≥0) : ℝ))) := by
    funext u; rw [girsR, girsN_zero_eq hσ]
  rw [e]
  exact (Real.continuous_exp.comp (hℓ'.sub continuous_const)).mul (Real.continuous_exp.comp (hI.const_mul a).neg)

theorem isStronglyProgressive_girsR (hBc : ∀ ω, Continuous (B · ω)) (hσ : σ ≠ 0) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (a : ℝ) :
    IsStronglyProgressive 𝓕 (girsR σ a B S ℓ ℓx) :=
  isStronglyProgressive_of_rightContinuous (fun u => (hL.measurable_girsR hBc hσ hρ hS a u).stronglyMeasurable)
    fun ω _ => (hL.continuous_girsR hBc hσ hρ hS a ω).continuousWithinAt

end IsDriverLogField

omit mΩ in
/-- On `{B_0 = 0}`: `N^a_u = R_u E_{u∧S}`. -/
theorem girsN_eq_girsR_mul_wald (hσ : σ ≠ 0) (a : ℝ) (u : ℝ≥0) {ω : Ω} (hB0 : B 0 ω = 0) :
    girsN σ a B S ℓ ℓx u ω = girsR σ a B S ℓ ℓx u ω * wald a B (min u (S ω)) ω := by
  rw [girsR, girsN_zero_eq hσ, wald, girsN, logFieldExp_tilt hσ, hB0, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- `N^0_u exp(aX_u − a²u/2) = R_u E_u`. -/
theorem girsN_mul_expX (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (a : ℝ) (u : ℝ≥0) (ω : Ω) :
    girsN σ 0 B S ℓ ℓx u ω * Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2) =
      girsR σ a B S ℓ ℓx u ω * wald a B u ω := by
  rw [girsR, wald, girsProcess, hL.drvInt_min hBc hρ hS ω u, mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- **The core martingale identity**: `∫_A R_t E_t = ∫_A R_s E_s` for `A ∈ 𝓕_s`, `s ≤ t`. Up to `S` this is the tilted
martingale (`integral_mul_tilt_stopped_eq`); after `S` it is optional sampling of the Wald martingale `E` at `t ∧ S`
(on `{s < S}`) and the martingale property of `E` from `s` to `t` (on `{S ≤ s}`). -/
theorem setIntegral_girsR_mul_wald_eq {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, girsR σ a B S ℓ ℓx t ω * wald a B t ω ∂P = ∫ ω in A, girsR σ a B S ℓ ℓx s ω * wald a B s ω ∂P := by
  have hP := hB.isProbabilityMeasure'
  have hPB := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hAm : MeasurableSet A := 𝓕.le s A hA
  set Rr := girsR σ a B S ℓ ℓx with hRrdef
  set E := wald a B with hEdef
  set CR := Real.exp (2 * K) * Real.exp (|a| * (|σ| * K * R)) with hCR
  have hRb : ∀ u ω, |Rr u ω| ≤ CR := hL.abs_girsR_le hσ.ne' hρ hSR a
  have hRm : ∀ u, Measurable (Rr u) := fun u => (hL.measurable_girsR hBc hσ.ne' hρ hS a u).mono (𝓕.le u) le_rfl
  have hM : Martingale E 𝓕 P := martingale_wald hB a
  have hMrc : ∀ ω u, ContinuousWithinAt (E · ω) (Ici u) u := fun ω u =>
    (continuous_wald hBc a ω).continuousWithinAt
  have hτ : ∀ u : ℝ≥0, IsStoppingTime 𝓕 fun ω => ((min u (S ω) : ℝ≥0) : WithTop ℝ≥0) := fun u => by
    simpa only [WithTop.coe_min] using (isStoppingTime_const 𝓕 u).min hS
  have hEτi : ∀ u : ℝ≥0, Integrable (fun ω => E (min u (S ω)) ω) P := fun u =>
    (tendsto_lintegral_stoppedValue_dyadicUpperTime hM.supermartingale hMrc (hτ u) (T := u)
      (fun ω => WithTop.coe_le_coe.2 (min_le_left _ _))).2.1
  have hEi : ∀ u, Integrable (E u) P := fun u => hM.integrable u
  have hRE : ∀ u (f : Ω → ℝ), Integrable f P → Integrable (fun ω => Rr u ω * f ω) P := fun u f hf =>
    hf.bdd_mul (c := CR) (hRm u).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hRb u ω)
  -- (i) the part up to `S`
  have hB0 : ∀ᵐ ω ∂P, B 0 ω = 0 := MathFin.X0_ae_eq_zero (X := B) (𝓕 := 𝓕) (P := P)
  have h1 : ∫ ω in A, Rr t ω * E (min t (S ω)) ω ∂P = ∫ ω in A, Rr s ω * E (min s (S ω)) ω ∂P := by
    have hpart := hL.integral_mul_tilt_stopped_eq hB hBc hσ hρ hS hSR a hst (ξ := A.indicator fun _ => 1)
      (measurable_const.indicator hA) (fun ω => by by_cases hω : ω ∈ A <;> simp [hω])
    have e : ∀ u : ℝ≥0, ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω *
        logFieldExp σ B (tiltL σ a B S ℓ ℓx) (min u (S ω)) ω ∂P = ∫ ω in A, Rr u ω * E (min u (S ω)) ω ∂P :=
      fun u => by
        rw [← integral_indicator hAm]
        refine integral_congr_ae ?_
        filter_upwards [hB0] with ω hω
        by_cases hωA : ω ∈ A
        · simp only [indicator_of_mem hωA, one_mul]
          exact girsN_eq_girsR_mul_wald hσ.ne' a u hω
        · simp [indicator_of_notMem hωA]
    rw [e t, e s] at hpart
    exact hpart
  -- (ii) the part after `S`
  have hgt : MeasurableSet[𝓕 s] {ω | s < S ω} := by
    have h := (measurableSet_le_of_isStoppingTime hS s).compl
    have he : {ω | S ω ≤ s}ᶜ = {ω | s < S ω} := by ext ω; simp
    rwa [he] at h
  have hint : ∀ u : ℝ≥0, Integrable (fun ω => Rr u ω * (E u ω - E (min u (S ω)) ω)) P := fun u => by
    simp only [mul_sub]; exact (hRE u _ (hEi u)).sub (hRE u _ (hEτi u))
  have h2 : ∫ ω in A, Rr t ω * (E t ω - E (min t (S ω)) ω) ∂P =
      ∫ ω in A, Rr s ω * (E s ω - E (min s (S ω)) ω) ∂P := by
    rw [← integral_inter_add_sdiff (𝓕.le s _ hgt) (hint t).integrableOn,
      ← integral_inter_add_sdiff (𝓕.le s _ hgt) (hint s).integrableOn]
    congr 1
    · -- on `A ∩ {s < S}`: optional sampling at `t ∧ S`
      have hA₂ : MeasurableSet[𝓕 s] (A ∩ {ω | s < S ω}) := hA.inter hgt
      have hA₂m : MeasurableSet (A ∩ {ω | s < S ω}) := 𝓕.le s _ hA₂
      have hz : ∫ ω in A ∩ {ω | s < S ω}, Rr s ω * (E s ω - E (min s (S ω)) ω) ∂P = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun ω hω => by rw [min_eq_left hω.2.le, sub_self, mul_zero]
      rw [hz]
      have hA₂τ : MeasurableSet[(hτ t).measurableSpace] (A ∩ {ω | s < S ω}) := by
        refine ⟨(le_iSup (fun u => (𝓕 u : MeasurableSpace Ω)) s) _ hA₂, fun i => ?_⟩
        by_cases hsi : s ≤ i
        · exact (𝓕.mono hsi _ hA₂).inter ((hτ t) i)
        · have h : A ∩ {ω | s < S ω} ∩ {ω | ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0) ≤ i} = ∅ := by
            refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
            obtain ⟨⟨_, hsS⟩, hmin⟩ := hω
            have hmin' : min t (S ω) ≤ i := WithTop.coe_le_coe.1 hmin
            have : s ≤ min t (S ω) := le_min hst hsS.le
            exact hsi (this.trans hmin')
          rw [h]
          exact @MeasurableSet.empty _ (𝓕 i)
      set G := (A ∩ {ω | s < S ω}).indicator (fun ω => Rr t ω) with hGdef
      have hGm : StronglyMeasurable[(hτ t).measurableSpace] G := by
        have hsv := measurable_stoppedValue (hL.isStronglyProgressive_girsR hBc hσ.ne' hρ hS a) (hτ t)
        have e : stoppedValue Rr (fun ω => ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0)) = Rr t := by
          funext ω; exact girsR_min σ a B S ℓ ℓx t ω
        rw [e] at hsv
        exact (hsv.indicator hA₂τ).stronglyMeasurable
      have hGb : ∀ ω, |G ω| ≤ CR := fun ω => by
        by_cases hω : ω ∈ A ∩ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω]; exact hRb t ω
        · rw [hGdef, indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hRb t ω)
      have hos := Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hM hMrc (hτ t)
        (isStoppingTime_const 𝓕 t) (fun ω => WithTop.coe_le_coe.2 (min_le_left _ _)) (T := t) (fun ω => le_rfl)
      have key := integral_mul_eq_of_ae_eq_condExp ((hτ t).measurableSpace_le) hos (hEi t) hGm hGb
      have eG : ∀ f : Ω → ℝ, ∫ ω, G ω * f ω ∂P = ∫ ω in A ∩ {ω | s < S ω}, Rr t ω * f ω ∂P := fun f => by
        rw [← integral_indicator hA₂m]
        congr 1; funext ω
        by_cases hω : ω ∈ A ∩ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω, indicator_of_mem hω]
        · rw [hGdef, indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
      have key' : ∫ ω in A ∩ {ω | s < S ω}, Rr t ω * E (min t (S ω)) ω ∂P =
          ∫ ω in A ∩ {ω | s < S ω}, Rr t ω * E t ω ∂P := by
        rw [← eG, ← eG]; exact key
      simp only [mul_sub]
      rw [integral_sub (hRE t _ (hEi t)).integrableOn (hRE t _ (hEτi t)).integrableOn, key', sub_self]
    · -- on `A \ {s < S}`: `S ≤ s`, a martingale step of `E` from `s` to `t`
      have hA₁ : MeasurableSet[𝓕 s] (A \ {ω | s < S ω}) := hA.diff hgt
      have hA₁m : MeasurableSet (A \ {ω | s < S ω}) := 𝓕.le s _ hA₁
      have hcongr : ∫ ω in A \ {ω | s < S ω}, Rr t ω * (E t ω - E (min t (S ω)) ω) ∂P =
          ∫ ω in A \ {ω | s < S ω}, Rr s ω * (E t ω - E (min s (S ω)) ω) ∂P := by
        refine setIntegral_congr_fun hA₁m fun ω hω => ?_
        have hSs : S ω ≤ s := not_lt.1 hω.2
        have hSt : S ω ≤ t := hSs.trans hst
        have hRts : Rr t ω = Rr s ω := by
          show girsR σ a B S ℓ ℓx t ω = girsR σ a B S ℓ ℓx s ω
          rw [← girsR_min σ a B S ℓ ℓx t ω, ← girsR_min σ a B S ℓ ℓx s ω, min_eq_right hSt, min_eq_right hSs]
        rw [hRts, min_eq_right hSt, min_eq_right hSs]
      rw [hcongr]
      set G := (A \ {ω | s < S ω}).indicator (fun ω => Rr s ω) with hGdef
      have hGm : StronglyMeasurable[𝓕 s] G :=
        ((hL.measurable_girsR hBc hσ.ne' hρ hS a s).indicator hA₁).stronglyMeasurable
      have hGb : ∀ ω, |G ω| ≤ CR := fun ω => by
        by_cases hω : ω ∈ A \ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω]; exact hRb s ω
        · rw [hGdef, indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hRb s ω)
      have key := integral_mul_eq_of_ae_eq_condExp (𝓕.le s) (hM.condExp_ae_eq hst).symm (hEi t) hGm hGb
      have eG : ∀ f : Ω → ℝ, ∫ ω, G ω * f ω ∂P = ∫ ω in A \ {ω | s < S ω}, Rr s ω * f ω ∂P := fun f => by
        rw [← integral_indicator hA₁m]
        congr 1; funext ω
        by_cases hω : ω ∈ A \ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω, indicator_of_mem hω]
        · rw [hGdef, indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
      have key' : ∫ ω in A \ {ω | s < S ω}, Rr s ω * E s ω ∂P = ∫ ω in A \ {ω | s < S ω}, Rr s ω * E t ω ∂P := by
        rw [← eG, ← eG]; exact key
      simp only [mul_sub]
      rw [integral_sub (hRE s _ (hEi t)).integrableOn (hRE s _ (hEτi s)).integrableOn,
        integral_sub (hRE s _ (hEi s)).integrableOn (hRE s _ (hEτi s)).integrableOn, key']
  -- assembly
  have e : ∀ u : ℝ≥0, ∫ ω in A, Rr u ω * E u ω ∂P =
      ∫ ω in A, Rr u ω * E (min u (S ω)) ω ∂P + ∫ ω in A, Rr u ω * (E u ω - E (min u (S ω)) ω) ∂P := fun u => by
    rw [← integral_add (hRE u _ (hEτi u)).integrableOn (hint u).integrableOn]
    congr 1; funext ω; ring
  rw [e t, e s, h1, h2]

end IsDriverLogField

omit mΩ in
theorem drvInt_zero (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓx : Ω → ℝ → ℝ → ℝ) (ω : Ω) :
    drvInt σ B S ℓx ω 0 = 0 := intervalIntegral.integral_same

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- The Girsanov process is adapted. -/
theorem stronglyAdapted_girsProcess (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    StronglyAdapted 𝓕 (girsProcess σ B S ℓx) := fun t =>
  (continuous_sub.measurable.comp ((hBm t).prodMk (hL.measurable_drvInt hBc hρ hS t))).stronglyMeasurable

/-- **Girsanov with the other curve frozen, exponential-martingale form**: under `Q = D · P`, for every horizon `T`,
`exp(aX_t − a²t/2)` is a `Q`-martingale on `[0, T]` for every `a` (MathFin's `IsExpQMartingale`). -/
theorem isExpQMartingale_girsProcess {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (T : ℝ≥0) :
    MathFin.IsExpQMartingale (girsMeasure P σ B S ℓ) 𝓕 (girsProcess σ B S ℓx) T := by
  have hP := hB.isProbabilityMeasure'
  have hPB := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hDm : AEStronglyMeasurable (girsDensity σ B S ℓ) P := by
    have hmR := (hL.measurable_girsN_zero hBc hσ.ne' hρ hS R).mono (𝓕.le R) le_rfl
    have e : girsDensity σ B S ℓ = girsN σ 0 B S ℓ ℓx R :=
      funext fun ω => girsDensity_eq_girsN hσ.ne' (hSR ω)
    rw [e]; exact hmR.aestronglyMeasurable
  have hDpos : ∀ ω, 0 ≤ girsDensity σ B S ℓ ω := fun ω => (Real.exp_pos _).le
  have hAd := hL.stronglyAdapted_girsProcess hBc hBm hρ hS
  refine ⟨hAd, ?_, fun a s t hst _ A hA => ?_⟩
  · have hac : girsMeasure P σ B S ℓ ≪ P := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (MathFin.X0_ae_eq_zero (X := B) (𝓕 := 𝓕) (P := P))] with ω hω
    simp [girsProcess, drvInt_zero, hω]
  -- every `exp(aX_u − a²u/2)` against `D`
  have hAm : MeasurableSet A := 𝓕.le s A hA
  have hf : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2) :=
    fun u => by
      have h := (hAd u).measurable
      have hF : Continuous fun x : ℝ => Real.exp (a * x - a ^ 2 * (u : ℝ) / 2) := by fun_prop
      exact hF.measurable.comp h
  have hfi : ∀ u : ℝ≥0, Integrable (fun ω => Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2)) P :=
    fun u => by
      have hw := (martingale_wald hB a).integrable u
      have hbd : ∀ ω, ‖Real.exp (-(a * drvInt σ B S ℓx ω u))‖ ≤ Real.exp (|a| * (|σ| * K * u)) := fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.2
        have hI := hL.abs_drvInt_le hρ ω u.coe_nonneg
        have h2 : |a * drvInt σ B S ℓx ω u| ≤ |a| * (|σ| * K * u) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hI (abs_nonneg a)
        linarith [neg_abs_le (a * drvInt σ B S ℓx ω u)]
      have hIm : Measurable fun ω => Real.exp (-(a * drvInt σ B S ℓx ω u)) :=
        (Real.continuous_exp.measurable.comp ((hL.measurable_drvInt hBc hρ hS u).const_mul a).neg).mono
          (𝓕.le u) le_rfl
      have h := hw.bdd_mul (c := Real.exp (|a| * (|σ| * K * u))) hIm.aestronglyMeasurable (Eventually.of_forall hbd)
      refine h.congr (Eventually.of_forall fun ω => ?_)
      simp only [wald, girsProcess, ← Real.exp_add]
      congr 1; ring
  have hstep : ∀ u : ℝ≥0, s ≤ u → ∫ ω in A, Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2)
      ∂(girsMeasure P σ B S ℓ) = ∫ ω in A, girsR σ a B S ℓ ℓx u ω * wald a B u ω ∂P := fun u hsu => by
    rw [girsMeasure, MathFin.setIntegral_withDensity_ofReal hDm hDpos _ hAm, ← integral_indicator hAm]
    have hY : Measurable[𝓕 u] (A.indicator fun ω => Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2)) :=
      (hf u).indicator (𝓕.mono hsu _ hA)
    have hYi : Integrable (A.indicator fun ω => Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2)) P :=
      (hfi u).indicator hAm
    have hb := hL.integral_mul_girsDensity hB hBc hσ hρ hS hSR u hY hYi
    have e1 : (fun ω => A.indicator (fun ω => Real.exp (a * girsProcess σ B S ℓx u ω - a ^ 2 * (u : ℝ) / 2) *
        girsDensity σ B S ℓ ω) ω) = fun ω => A.indicator (fun ω => Real.exp (a * girsProcess σ B S ℓx u ω -
          a ^ 2 * (u : ℝ) / 2)) ω * girsDensity σ B S ℓ ω := by
      funext ω; by_cases hω : ω ∈ A <;> simp [hω]
    rw [e1, hb, ← integral_indicator hAm]
    congr 1; funext ω
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, indicator_of_mem hω, mul_comm, hL.girsN_mul_expX hBc hρ hS a u ω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
  rw [hstep t hst, hstep s le_rfl]
  exact hL.setIntegral_girsR_mul_wald_eq hB hBc hσ hρ hS hSR a hst hA

/-- **Girsanov with the other curve frozen** (§A.1.3). Let `ℓ` be a driver log-field up to a stopping time `S ≤ R` for
the Brownian motion `B` of `𝓕` (e.g. `log M̃` with the other curve frozen, `isDriverLogField_frozen`). Under
`Q = (M_S/M_0) · P`, the process `X = B − ∫₀^{·∧S} σ ∂_xℓ(u, σB_u) du` is a Brownian motion of `𝓕`. -/
theorem isFilteredBrownianReal_girsProcess {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) :
    IsFilteredBrownianReal 𝓕 (girsProcess σ B S ℓx) (girsMeasure P σ B S ℓ) := by
  have := hL.isProbabilityMeasure_girsMeasure hB hBc hσ hρ hS hSR
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hall := fun T => hL.isExpQMartingale_girsProcess hB hBc hσ hρ hS hSR T
  have hcont : ∀ᵐ ω ∂(girsMeasure P σ B S ℓ), Continuous (girsProcess σ B S ℓx · ω) :=
    ae_of_all _ fun ω => (hBc ω).sub ((hL.continuous_drvInt hBc hρ hS ω).comp NNReal.continuous_coe)
  exact ⟨MathFin.isBrownianReal_of_expMartingale hall hcont,
    (hL.stronglyAdapted_girsProcess hBc hBm hρ hS).adapted,
    (MathFin.isFilteredPreBrownian_of_expMartingale hall).indep⟩

end IsDriverLogField

end InteractingSLE.ZhanGT4
