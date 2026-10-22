import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Sphere.Avg
import HigherDimLQGMetric.Sphere.Var

/-!
# Exact scaling and the radius-`s` pin (packet P2; blueprint Part A `a:lem-scaling`, `a:lem-pin`)

Source: [C] (2.5)–(2.6), p. 3, l. 145–156; NA1 items 11–12, R2(h); NA3 R7; NA4 A1 Step 8 (the per-pair representation
is `rho_scaling` at one point); ruling N8 (Part D's unit-pin scaling lemma is the case `s = s₀ = 1`).

* `rho_scaling` (`a:lem-scaling`, both identities of (2.6), under every global pin `s₀`): for fixed `(r, z)`, almost
  surely, simultaneously for all `x, y` and all sets `U`,
  `ρ_g(z + rx, z + ry) = S ρ_{g'}(x, y)` and `ρ_g(z + rx, z + ry; z + rU) = S ρ_{g'}(x, y; U)`, with
  `g' = recentre s r z g` and `S = scaleS d ξ s r z g`;
* `exists_variance_sphereAvg_le` and `hasGaussianLaw_sphereAvg_normLGFLaw`: `h_s(0)` is a centred Gaussian under
  `normLGFLaw d` with `Var h_s(0) ≤ |log s| + K_d`, `K_d` uniform in `s`;
* `rho_pin` (`a:lem-pin`): `ρ_h = e^{ξ h_s(0)} ρ_{pin s h}` almost surely, the Gaussian facts, and
  `∫ log ρ_g(0, e₁) dP_s(g) = 0`.

The hypothesis `s > 0` of `rho_scaling` (kept from the packet statement) is not used by the proof. The hypothesis
`ξ > 0` is used: `scaleS` has the exponent `ϕ(ξ)` with `ϕ(0) = 1` (ruling N21), and `ϕ(ξ) = ξ Q(ξ)` only for `ξ > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Exact scaling (`a:lem-scaling`) -/

/-- The recentred field is a whole-space LGF under every pin. -/
theorem isWholeSpaceLGF_recentre_pinLaw (hd : 2 ≤ d) {s s₀ r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) :
    IsWholeSpaceLGF (fun g => recentre s r z g) (pinLaw d s₀) :=
  let hlgf := (isWholeSpaceLGF_pinLaw hd hs₀).1
  (hlgf.affineComp hr z).addConst ((measurable_sphereAvg_left (s * r) z).comp hlgf.measurable).neg

/-- The unnormalized form of (2.6): for fixed `(r, z)`, a.s. under `pinLaw d s₀`, simultaneously for all `x, y`,
`D_g(z + rx, z + ry) = S D_{g'}(x, y)`. -/
theorem ae_apply_scaling (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) {s s₀ r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ x y : Rd d,
      (D g).1 (r • x + z, r • y + z) = scaleS d ξ s r z g * (D (recentre s r z g)).1 (x, y) := by
  have := isProbabilityMeasure_pinLaw hd s₀
  have hlgf := (isWholeSpaceLGF_pinLaw hd hs₀).1
  have hrec := isWholeSpaceLGF_recentre_pinLaw hd (s := s) hs₀ hr z
  filter_upwards [hD.coord (pinLaw d s₀) id hlgf.isLGFPlusCont r hr z,
    hD.ae_apply_addFun_const hrec.isLGFPlusCont] with g hc hw x y
  have hw' := hw (distExp d ξ * Real.log r + sphereAvg g (s * r) z) x y
  have he : addConst (recentre s r z g) (distExp d ξ * Real.log r + sphereAvg g (s * r) z) =
      addConst (affineComp r z g) (distExp d ξ * Real.log r) := by
    unfold recentre
    rw [addConst_addConst]
    congr 1
    ring
  rw [addFun_const, he] at hw'
  rw [show (D g).1 (r • x + z, r • y + z) = (D (id g)).1 (r • x + z, r • y + z) from rfl, hc x y, id, hw',
    scaleS_eq_exp_of_pos d hξ s hr]
  congr 2
  ring

/-- **Exact scaling (2.6)**, both identities, under every global pin `s₀` (form without the superfluous hypothesis
`s > 0`; `rho_scaling` is the packet statement). -/
theorem rho_scaling_of {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) {s s₀ r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) :
    ∀ᵐ g ∂(pinLaw d s₀),
      (∀ x y : Rd d, (rho D g).1 (r • x + z, r • y + z) =
         scaleS d ξ s r z g * (rho D (recentre s r z g)).1 (x, y)) ∧
      ∀ (U : Set (Rd d)) (x y : Rd d),
        (rho D g).internal ((fun w => r • w + z) '' U) (r • x + z) (r • y + z) =
          ENNReal.ofReal (scaleS d ξ s r z g) * (rho D (recentre s r z g)).internal U x y := by
  filter_upwards [ae_apply_scaling hd hξ hD (s := s) hs₀ hr z] with g hg
  have key : ∀ x y : Rd d, (rho D g).1 (r • x + z, r • y + z) =
      scaleS d ξ s r z g * (rho D (recentre s r z g)).1 (x, y) := by
    intro x y
    rw [rho_apply, rho_apply, hg x y]
    ring
  refine ⟨key, fun U x y => ?_⟩
  have hM : (rho D g).affine r hr.ne' z =
      (rho D (recentre s r z g)).smul (scaleS d ξ s r z g) (scaleS_pos d ξ s hr z g) :=
    Subtype.ext (ContinuousMap.ext fun p => key p.1 p.2)
  rw [← ContMetric.internal_affine hr.ne' z, hM, ContMetric.internal_smul]

/-- **Exact scaling (2.6)** (`a:lem-scaling`), both identities, under every global pin `s₀`. -/
theorem rho_scaling {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) {s s₀ r : ℝ} (_hs : 0 < s) (hs₀ : 0 < s₀) (hr : 0 < r)
    (z : Rd d) :
    ∀ᵐ g ∂(pinLaw d s₀),
      (∀ x y : Rd d, (rho D g).1 (r • x + z, r • y + z) =
         scaleS d ξ s r z g * (rho D (recentre s r z g)).1 (x, y)) ∧
      ∀ (U : Set (Rd d)) (x y : Rd d),
        (rho D g).internal ((fun w => r • w + z) '' U) (r • x + z) (r • y + z) =
          ENNReal.ofReal (scaleS d ξ s r z g) * (rho D (recentre s r z g)).internal U x y :=
  rho_scaling_of hd hξ hD hs₀ hr z

/-- The per-pair representation (NA4 A1 Step 8): for fixed `z`, `r > 0`, `u`, almost surely under `pinLaw d s₀`,
`ρ_g(z, z + r u) = S ρ_{g'}(0, u)`. -/
theorem rho_pair_scaling (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) {s s₀ r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (z u : Rd d) :
    ∀ᵐ g ∂(pinLaw d s₀),
      (rho D g).1 (z, z + r • u) = scaleS d ξ s r z g * (rho D (recentre s r z g)).1 (0, u) := by
  filter_upwards [rho_scaling_of hd hξ hD (s := s) hs₀ hr z] with g hg
  have := hg.1 0 u
  rwa [smul_zero, zero_add, add_comm (r • u)] at this

/-! ## The sphere average `h_s(0)` under the normalized law -/

/-- Under `normLGFLaw d`, `h_s(0)` is a centred Gaussian (`s > 0`). -/
theorem hasGaussianLaw_sphereAvg_normLGFLaw (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) :
    HasGaussianLaw (fun h : DistRd d => sphereAvg h s 0) (normLGFLaw d) ∧
      ∫ h, sphereAvg h s 0 ∂(normLGFLaw d) = 0 := by
  have hN := (normLGFLaw_spec_holds d hd).2.1
  obtain ⟨hG, h0⟩ := hN.1.hasGaussianLaw_sphereAvg_sub hd hs one_pos 0 0
  have e : (fun h : DistRd d => sphereAvg (id h) s 0 - sphereAvg (id h) 1 0) =ᵐ[normLGFLaw d]
      fun h => sphereAvg h s 0 := by
    filter_upwards [hN.2] with h hh
    rw [hh, sub_zero, id]
  exact ⟨hG.congr e, (integral_congr_ae e).symm.trans h0⟩

/-- `Var h_s(0) ≤ |log s| + K_d` under `normLGFLaw d`, with `K_d` (the constant of `exists_variance_sphereAvg_sub_le`)
uniform in `s > 0`. -/
theorem exists_variance_sphereAvg_le (hd : 2 ≤ d) :
    ∃ K : ℝ, ∀ s : ℝ, 0 < s → Var[fun h : DistRd d => sphereAvg h s 0; normLGFLaw d] ≤ |Real.log s| + K := by
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_sub_le (d := d) hd
  refine ⟨K, fun s hs => ?_⟩
  have hN := (normLGFLaw_spec_holds d hd).2.1
  have e : (fun h : DistRd d => sphereAvg (id h) s 0 - sphereAvg (id h) 1 0) =ᵐ[normLGFLaw d]
      fun h => sphereAvg h s 0 := by
    filter_upwards [hN.2] with h hh
    rw [hh, sub_zero, id]
  rw [← variance_congr e]
  obtain ⟨h1, h2⟩ := hK hN.1 hs one_pos (0 : Rd d) 0
  simp only [sub_self, norm_zero, zero_div, Real.log_zero, max_self, mul_zero, add_zero] at h1 h2
  rcases le_total s 1 with hs1 | hs1
  · refine (h1 hs1).trans (le_of_eq ?_)
    rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hs.le hs1)]
  · refine (h2 hs1).trans (le_of_eq ?_)
    rw [div_one, abs_of_nonneg (Real.log_nonneg hs1)]

/-! ## The radius-`s` pin (`a:lem-pin`) -/

/-- Weyl with the random constant `-h_s(0)`: a.s. under `normLGFLaw d`, `D_h = e^{ξ h_s(0)} D_{pin s h}`. -/
theorem ae_apply_pin (hd : 2 ≤ d) {ξ : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (s : ℝ) :
    ∀ᵐ h ∂(normLGFLaw d), ∀ x y : Rd d,
      (D h).1 (x, y) = Real.exp (ξ * sphereAvg h s 0) * (D (pin s h)).1 (x, y) := by
  have hspec := normLGFLaw_spec_holds d hd
  have := hspec.1
  filter_upwards [hD.ae_apply_addFun_const hspec.2.1.1.isLGFPlusCont] with h hw x y
  have hw' := hw (-sphereAvg h s 0) x y
  rw [addFun_const] at hw'
  rw [show pin s h = addConst (id h) (-sphereAvg h s 0) from rfl, hw', id, ← mul_assoc, ← Real.exp_add,
    mul_neg, add_neg_cancel, Real.exp_zero, one_mul]

/-- **The radius-`s` pin (2.5)** (`a:lem-pin`): for `D` strong at `(ξ, Q(ξ))` with `log D(0, e₁)` integrable and
`s > 0`: almost surely `ρ_h = e^{ξ h_s(0)} ρ_{pin s h}`; `h_s(0)` is a centred Gaussian with `Var h_s(0) ≤ |log s| + K_d`
(`K_d` uniform in the radius); and `∫ log ρ_g(0, e₁) dP_s(g) = 0`. -/
theorem rho_pin (hd : 2 ≤ d) {ξ : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) {s : ℝ} (hs : 0 < s) :
    (∀ᵐ h ∂(normLGFLaw d), (rho D h).1 = Real.exp (ξ * sphereAvg h s 0) • (rho D (pin s h)).1) ∧
      HasGaussianLaw (fun h : DistRd d => sphereAvg h s 0) (normLGFLaw d) ∧
      ∫ h, sphereAvg h s 0 ∂(normLGFLaw d) = 0 ∧
      (∃ K : ℝ, ∀ t : ℝ, 0 < t →
        Var[fun h : DistRd d => sphereAvg h t 0; normLGFLaw d] ≤ |Real.log t| + K) ∧
      ∫ g, Real.log ((rho D g).1 (0, e₁ d)) ∂(pinLaw d s) = 0 := by
  have hspec := normLGFLaw_spec_holds d hd
  have := hspec.1
  have h0 := p2_zero_ne_e₁ (d := d) (by omega)
  obtain ⟨hG, hmean⟩ := hasGaussianLaw_sphereAvg_normLGFLaw hd hs
  have hid : ∀ᵐ h ∂(normLGFLaw d),
      (rho D h).1 = Real.exp (ξ * sphereAvg h s 0) • (rho D (pin s h)).1 := by
    filter_upwards [ae_apply_pin hd hD s] with h hh
    refine ContinuousMap.ext fun p => ?_
    rw [ContinuousMap.smul_apply, smul_eq_mul, rho_apply, rho_apply, show p = (p.1, p.2) from rfl, hh]
    ring
  refine ⟨hid, hG, hmean, exists_variance_sphereAvg_le hd, ?_⟩
  -- change of variables to `normLGFLaw d`, then `log ρ_{pin s h} = log ρ_h - ξ h_s(0)`
  rw [pinLaw, integral_map (measurable_pin s).aemeasurable
    (measurable_log_rho_apply hD.measurable _).aestronglyMeasurable]
  have hlog : (fun h => Real.log ((rho D h).1 (0, e₁ d)) - ξ * sphereAvg h s 0) =ᵐ[normLGFLaw d]
      fun h => Real.log ((rho D (pin s h)).1 (0, e₁ d)) := by
    filter_upwards [hid] with h hh
    have hp : (rho D h).1 (0, e₁ d) = Real.exp (ξ * sphereAvg h s 0) * (rho D (pin s h)).1 (0, e₁ d) := by
      rw [hh, ContinuousMap.smul_apply, smul_eq_mul]
    rw [hp, Real.log_mul (Real.exp_pos _).ne' ((rho D (pin s h)).apply_pos h0).ne', Real.log_exp]
    ring
  rw [← integral_congr_ae hlog, integral_sub (integrable_log_rho hd hint) (hG.integrable.const_mul ξ),
    integral_log_rho hd hint, integral_const_mul, hmean, mul_zero, sub_zero]

end HigherDimLQGContinuity
