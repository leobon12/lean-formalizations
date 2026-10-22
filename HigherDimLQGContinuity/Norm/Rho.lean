import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Frozen.StrongUniqueness

/-!
# The mean-log normalization `rho` (packet P2; blueprint Part A `a:def-rho`, `a:lem-rho`)

Source: [C] (1.6), p. 2, l. 82–87; NA1 item 5, R0(iv), R2(f); rulings N5, N8.

* `measurable_rho`, `measurable_log_rho_apply`: measurability for a measurable assignment;
* `rho_apply`, `log_rho_apply`: `ρ^D_g = e^{-logMean D} D_g` pointwise, `log ρ = log D - logMean D` off the diagonal;
* `a:lem-rho` (a): `logMean_smul`, `rho_smul`;
* `a:lem-rho` (b): `rho_congr_ae` (an a.e. deterministic multiple has the same `rho`, a.e.);
* `a:lem-rho` (c): `integral_log_rho`;
* `a:lem-rho` (d): `integrable_log_of_strong`, `rho_ae_eq_of_strong` (via [8]'s `strongUniqueness`).

The log-integrability hypothesis (`hint`) is necessary for (a)–(d): off `L¹` the Bochner integral `logMean` is the junk
value `0` (e.g. for (a): `logMean (C·D) = 0 ≠ log C + 0` when `C ≠ 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Measurability and pointwise formulas -/

theorem rho_apply (D : DistRd d → ContMetric d) (g : DistRd d) (p : Rd d × Rd d) :
    (rho D g).1 p = Real.exp (-logMean D) * (D g).1 p := rfl

theorem measurable_rho {D : DistRd d → ContMetric d} (hD : Measurable D) : Measurable (rho D) := by
  unfold rho ContMetric.smul
  exact ((continuous_const_smul _).measurable.comp (measurable_subtype_coe.comp hD)).subtype_mk

/-- `g ↦ (D g)(x, y)` is measurable for a measurable assignment. -/
theorem p2_measurable_contMetric_apply {D : DistRd d → ContMetric d} (hD : Measurable D) (p : Rd d × Rd d) :
    Measurable fun g => (D g).1 p :=
  (continuous_eval_const p).measurable.comp (measurable_subtype_coe.comp hD)

theorem measurable_log_rho_apply {D : DistRd d → ContMetric d} (hD : Measurable D) (p : Rd d × Rd d) :
    Measurable fun g => Real.log ((rho D g).1 p) :=
  Real.measurable_log.comp (p2_measurable_contMetric_apply (measurable_rho hD) p)

/-- `0 ≠ e₁` in dimension `d ≥ 1`. -/
theorem p2_zero_ne_e₁ (hd : 1 ≤ d) : (0 : Rd d) ≠ e₁ d :=
  (HigherDimLFPP.e₁_ne_zero (by omega)).symm

/-- `log ρ^D_g(x, y) = log D_g(x, y) - logMean D` for `x ≠ y`. -/
theorem log_rho_apply (D : DistRd d → ContMetric d) (g : DistRd d) {x y : Rd d} (hxy : x ≠ y) :
    Real.log ((rho D g).1 (x, y)) = Real.log ((D g).1 (x, y)) - logMean D := by
  rw [rho_apply, Real.log_mul (Real.exp_pos _).ne' ((D g).apply_pos hxy).ne', Real.log_exp]
  ring

/-! ## Deterministic multiples (`a:lem-rho` (a), (b)) -/

/-- `a:lem-rho` (b): if `D' = C D` almost surely with a deterministic `C > 0` and `log D(0, e₁)` is integrable, then
`log D'(0, e₁)` is integrable, `logMean D' = log C + logMean D`, and `ρ^{D'} = ρ^D` almost surely. -/
theorem rho_congr_ae (hd : 2 ≤ d) {D D' : DistRd d → ContMetric d} {C : ℝ} (hC : 0 < C)
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d))
    (h : ∀ᵐ g ∂(normLGFLaw d), ∀ x y : Rd d, (D' g).1 (x, y) = C * (D g).1 (x, y)) :
    Integrable (fun g => Real.log ((D' g).1 (0, e₁ d))) (normLGFLaw d) ∧
      logMean D' = Real.log C + logMean D ∧ ∀ᵐ g ∂(normLGFLaw d), rho D' g = rho D g := by
  have := (normLGFLaw_spec_holds d hd).1
  have h0 := p2_zero_ne_e₁ (d := d) (by omega)
  have hlog : (fun g => Real.log C + Real.log ((D g).1 (0, e₁ d))) =ᵐ[normLGFLaw d]
      fun g => Real.log ((D' g).1 (0, e₁ d)) := by
    filter_upwards [h] with g hg
    rw [hg, Real.log_mul hC.ne' ((D g).apply_pos h0).ne']
  have hint' : Integrable (fun g => Real.log ((D' g).1 (0, e₁ d))) (normLGFLaw d) :=
    ((integrable_const _).add hint).congr hlog
  have hmean : logMean D' = Real.log C + logMean D := by
    unfold logMean
    rw [← integral_congr_ae hlog, integral_add (integrable_const _) hint, integral_const, probReal_univ,
      one_smul]
  refine ⟨hint', hmean, ?_⟩
  filter_upwards [h] with g hg
  refine Subtype.ext (ContinuousMap.ext fun p => ?_)
  change (rho D' g).1 p = (rho D g).1 p
  rw [rho_apply, rho_apply, hmean, show p = (p.1, p.2) from rfl, hg, neg_add, Real.exp_add,
    Real.exp_neg (Real.log C), Real.exp_log hC]
  field_simp

/-- `a:lem-rho` (a): `logMean (C·D) = log C + logMean D`. -/
theorem logMean_smul (hd : 2 ≤ d) {D : DistRd d → ContMetric d}
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) {C : ℝ} (hC : 0 < C) :
    logMean (fun g => (D g).smul C hC) = Real.log C + logMean D :=
  (rho_congr_ae hd hC hint (ae_of_all _ fun _ _ _ => rfl)).2.1

/-- `a:lem-rho` (a): `ρ^{C·D} = ρ^D` (everywhere). -/
theorem rho_smul (hd : 2 ≤ d) {D : DistRd d → ContMetric d}
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) {C : ℝ} (hC : 0 < C) :
    rho (fun g => (D g).smul C hC) = rho D := by
  funext g
  refine Subtype.ext (ContinuousMap.ext fun p => ?_)
  change (rho (fun g => (D g).smul C hC) g).1 p = (rho D g).1 p
  rw [rho_apply, rho_apply, logMean_smul hd hint hC, ContMetric.smul_apply, neg_add, Real.exp_add,
    Real.exp_neg (Real.log C), Real.exp_log hC]
  field_simp

/-! ## The normalization (`a:lem-rho` (c)) -/

/-- `a:lem-rho` (c): `E log ρ^D(0, e₁) = 0` under `normLGFLaw d`. -/
theorem integral_log_rho (hd : 2 ≤ d) {D : DistRd d → ContMetric d}
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) :
    ∫ g, Real.log ((rho D g).1 (0, e₁ d)) ∂(normLGFLaw d) = 0 := by
  have := (normLGFLaw_spec_holds d hd).1
  have h0 := p2_zero_ne_e₁ (d := d) (by omega)
  simp only [log_rho_apply D _ h0]
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  exact sub_self _

/-- The log-integrability of `ρ^D(0, e₁)` follows from that of `D(0, e₁)`. -/
theorem integrable_log_rho (hd : 2 ≤ d) {D : DistRd d → ContMetric d}
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) :
    Integrable (fun g => Real.log ((rho D g).1 (0, e₁ d))) (normLGFLaw d) := by
  have := (normLGFLaw_spec_holds d hd).1
  have h0 := p2_zero_ne_e₁ (d := d) (by omega)
  simp only [log_rho_apply D _ h0]
  exact hint.sub (integrable_const _)

/-! ## Independence of the strong assignment (`a:lem-rho` (d)) -/

/-- Two strong assignments at `(ξ, Q(ξ))` (`ξ` subcritical, `d ≥ 3`) are almost surely deterministic multiples of each
other under `normLGFLaw d` ([8]'s `strongUniqueness` with the input `id`, `f = 0`). -/
theorem exists_ae_eq_mul_of_strong (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < distExp d ξ)
    {D D' : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hD' : IsStrongExpMetric d ξ (distExp d ξ) D') :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ g ∂(normLGFLaw d), ∀ x y : Rd d, (D' g).1 (x, y) = C * (D g).1 (x, y) := by
  have hspec := normLGFLaw_spec_holds d (by omega)
  have := hspec.1
  obtain ⟨C, hC, hU⟩ := strongUniqueness d ξ (distExp d ξ) hd hξ hQ D D' hD hD'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hU (normLGFLaw d) id hspec.2.1.1.isLGFPlusCont] with g hg x y
  have := hg 0 x y
  rwa [id, addFun_zero] at this

/-- `a:lem-rho` (d), integrability part: log-integrability of the unit distance transfers between strong assignments
at the same subcritical `(ξ, Q(ξ))`. -/
theorem integrable_log_of_strong (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < distExp d ξ)
    {D D' : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hD' : IsStrongExpMetric d ξ (distExp d ξ) D')
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) :
    Integrable (fun g => Real.log ((D' g).1 (0, e₁ d))) (normLGFLaw d) := by
  obtain ⟨C, hC, h⟩ := exists_ae_eq_mul_of_strong hd hξ hQ hD hD'
  exact (rho_congr_ae (by omega) hC hint h).1

/-- `a:lem-rho` (d): for `d ≥ 3`, `ξ` subcritical and `D, D'` strong at `(ξ, Q(ξ))` with `log D(0, e₁)` integrable,
`ρ^{D'} = ρ^D` almost surely under `normLGFLaw d`. -/
theorem rho_ae_eq_of_strong (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < distExp d ξ)
    {D D' : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hD' : IsStrongExpMetric d ξ (distExp d ξ) D')
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) :
    ∀ᵐ g ∂(normLGFLaw d), rho D' g = rho D g := by
  obtain ⟨C, hC, h⟩ := exists_ae_eq_mul_of_strong hd hξ hQ hD hD'
  exact (rho_congr_ae (by omega) hC hint h).2.2

end HigherDimLQGContinuity
