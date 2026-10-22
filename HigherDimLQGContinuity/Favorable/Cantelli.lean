import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Cantelli's inequality (packet P8a)

Packet P8a, target `cantelli_lower` (blueprint Part A, Lemma `a:lem34`, "Cantelli's inequality"; planning audit NA0,
input I32; NA1 item 26 (b): Cantelli needs `t > 0`).

**Statement.** Let `μ` be a probability measure and `Y` a real random variable with `E Y = 0` and
`E Y² ≤ σ²` (`σ² ≥ 0`). Then for every `t > 0`
* `cantelli_upper`: `P(Y ≥ t) ≤ σ²/(σ² + t²)`;
* `cantelli_lower`: `P(Y < t) ≥ t²/(σ² + t²)`.

The second moment is a `lintegral` (junk-safe, ruling N5): with `E Y² < ∞` the variable is in `L²`, hence integrable,
so the hypothesis `∫ Y = 0` is not the Bochner junk value.

**Proof.** For `u := σ²/t ≥ 0`, `Y ≥ t` implies `(Y + u)² ≥ (t + u)² > 0`, and Markov's inequality gives
`P(Y ≥ t) ≤ E(Y + u)²/(t + u)² = (E Y² + u²)/(t + u)² ≤ (σ² + u²)/(t + u)² = σ²/(σ² + t²)`. The lower form follows
from `univ = {Y < t} ∪ {Y ≥ t}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

section Cantelli

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A real variable with a finite `lintegral` second moment is in `L²`. -/
theorem p8a_memLp_two_of_lintegral {Y : Ω → ℝ} (hYm : AEStronglyMeasurable Y μ) {σ2 : ℝ}
    (hsq : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ ≤ ENNReal.ofReal σ2) : MemLp Y 2 μ := by
  refine (memLp_two_iff_integrable_sq hYm).2 ⟨hYm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg (Y ω))]
  exact lt_of_le_of_lt hsq ENNReal.ofReal_lt_top

/-- The Bochner second moment is bounded by the `lintegral` bound. -/
theorem p8a_integral_sq_le {Y : Ω → ℝ} (hYm : AEStronglyMeasurable Y μ) {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (hsq : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ ≤ ENNReal.ofReal σ2) : ∫ ω, Y ω ^ 2 ∂μ ≤ σ2 := by
  have hint : Integrable (fun ω => Y ω ^ 2) μ := (p8a_memLp_two_of_lintegral hYm hsq).integrable_sq
  have h := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg (Y ω))
  rw [← h] at hsq
  exact (ENNReal.ofReal_le_ofReal_iff hσ2).1 hsq

/-- The algebra of Cantelli's choice `u = σ²/t`: `(σ² + u²)/(t + u)² = σ²/(σ² + t²)`. -/
theorem p8a_cantelli_algebra {σ2 t : ℝ} (hσ2 : 0 ≤ σ2) (ht : 0 < t) :
    (σ2 + (σ2 / t) ^ 2) / (t + σ2 / t) ^ 2 = σ2 / (σ2 + t ^ 2) := by
  have ht' : t ≠ 0 := ht.ne'
  have hpos : 0 < σ2 + t ^ 2 := by positivity
  have hpos' : t + σ2 / t ≠ 0 := by positivity
  rw [div_eq_div_iff (pow_ne_zero 2 hpos') hpos.ne']
  field_simp
  ring

/-- **Cantelli's inequality**, upper tail: for `E Y = 0`, `E Y² ≤ σ²` and `t > 0`,
`P(Y ≥ t) ≤ σ²/(σ² + t²)`. -/
theorem cantelli_upper [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hYm : AEStronglyMeasurable Y μ) {σ2 : ℝ}
    (hσ2 : 0 ≤ σ2) (hsq : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ ≤ ENNReal.ofReal σ2)
    (hmean : ∫ ω, Y ω ∂μ = 0) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (σ2 / (σ2 + t ^ 2)) := by
  set u : ℝ := σ2 / t with hu
  have hu0 : 0 ≤ u := div_nonneg hσ2 ht.le
  have htu : 0 < t + u := by linarith
  have hL2 : MemLp Y 2 μ := p8a_memLp_two_of_lintegral hYm hsq
  have hY1 : Integrable Y μ := hL2.integrable one_le_two
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ := hL2.integrable_sq
  have hY2le : ∫ ω, Y ω ^ 2 ∂μ ≤ σ2 := p8a_integral_sq_le hYm hσ2 hsq
  -- the shifted second moment
  have hsh : ∀ ω, (Y ω + u) ^ 2 = Y ω ^ 2 + 2 * u * Y ω + u ^ 2 := fun ω => by ring
  have hint2 : Integrable (fun ω => (Y ω + u) ^ 2) μ := by
    simp_rw [hsh]
    exact (hY2.add (hY1.const_mul (2 * u))).add (integrable_const _)
  have hmom : ∫ ω, (Y ω + u) ^ 2 ∂μ ≤ σ2 + u ^ 2 := by
    simp_rw [hsh]
    have hf : Integrable (fun ω => Y ω ^ 2 + 2 * u * Y ω) μ := hY2.add (hY1.const_mul (2 * u))
    rw [integral_add (f := fun ω => Y ω ^ 2 + 2 * u * Y ω) hf (integrable_const _),
      integral_add (f := fun ω => Y ω ^ 2) (g := fun ω => 2 * u * Y ω) hY2 (hY1.const_mul (2 * u)),
      integral_const_mul, hmean, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
    linarith
  -- Markov's inequality for `(Y + u)²`
  have hsub : {ω | t ≤ Y ω} ⊆ {ω | ENNReal.ofReal ((t + u) ^ 2) ≤ ENNReal.ofReal ((Y ω + u) ^ 2)} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ htu.le (by linarith) 2)
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal ((Y ω + u) ^ 2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hYm.aemeasurable.add_const u).pow_const 2)
  have hmk := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal ((t + u) ^ 2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun ω => sq_nonneg _)] at hmk
  have htu2 : 0 < (t + u) ^ 2 := by positivity
  have hbound : μ {ω | ENNReal.ofReal ((t + u) ^ 2) ≤ ENNReal.ofReal ((Y ω + u) ^ 2)} ≤
      ENNReal.ofReal ((σ2 + u ^ 2) / (t + u) ^ 2) := by
    rw [ENNReal.ofReal_div_of_pos htu2, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 htu2).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hmk.trans (ENNReal.ofReal_le_ofReal hmom)
  calc μ {ω | t ≤ Y ω} ≤ _ := measure_mono hsub
    _ ≤ _ := hbound
    _ = ENNReal.ofReal (σ2 / (σ2 + t ^ 2)) := by rw [hu, p8a_cantelli_algebra hσ2 ht]

/-- **Cantelli's inequality**, lower form (blueprint `a:lem34`, NA0 I32): for `E Y = 0`, `E Y² ≤ σ²` (as a
`lintegral`, junk-safe) and `t > 0`, `P(Y < t) ≥ t²/(σ² + t²)`. -/
theorem cantelli_lower [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hYm : AEStronglyMeasurable Y μ) {σ2 : ℝ}
    (hσ2 : 0 ≤ σ2) (hsq : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ ≤ ENNReal.ofReal σ2)
    (hmean : ∫ ω, Y ω ∂μ = 0) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ 2 / (σ2 + t ^ 2)) ≤ μ {ω | Y ω < t} := by
  have hpos : 0 < σ2 + t ^ 2 := by positivity
  have hup := cantelli_upper hYm hσ2 hsq hmean ht
  have hcover : (univ : Set Ω) ⊆ {ω | Y ω < t} ∪ {ω | t ≤ Y ω} := by
    intro ω _
    rcases lt_or_ge (Y ω) t with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hone : (1 : ℝ≥0∞) ≤ μ {ω | Y ω < t} + ENNReal.ofReal (σ2 / (σ2 + t ^ 2)) := by
    calc (1 : ℝ≥0∞) = μ univ := measure_univ.symm
      _ ≤ μ ({ω | Y ω < t} ∪ {ω | t ≤ Y ω}) := measure_mono hcover
      _ ≤ μ {ω | Y ω < t} + μ {ω | t ≤ Y ω} := measure_union_le _ _
      _ ≤ _ := by gcongr
  have hsum : ENNReal.ofReal (t ^ 2 / (σ2 + t ^ 2)) + ENNReal.ofReal (σ2 / (σ2 + t ^ 2)) = 1 := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div, add_comm (t ^ 2) σ2,
      div_self hpos.ne', ENNReal.ofReal_one]
  rw [← hsum] at hone
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hone

end Cantelli

end HigherDimLQGContinuity
