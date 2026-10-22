import HigherDimLQGContinuity.MarginalEuclid.PairBound
import GaussianLQG.LQG.Euclid.Basic
import GaussianLQG.LQG.Euclid.Pair
import GaussianLQG.LQG.Euclid.Moments

/-! The fixed-pair Euclidean error estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

private theorem n5_abs_scaled_pair_sub_le {r R ξ φ Z : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    |r ^ φ * Real.exp (ξ * Z) * R - r| ≤
      |ξ * Z + Real.log R + (φ - 1) * Real.log r| *
        (r + r ^ φ * Real.exp (ξ * Z) * R) := by
  let X := ξ * Z + Real.log R + (φ - 1) * Real.log r
  have hrep : r ^ φ * Real.exp (ξ * Z) * R = r * Real.exp X := by
    calc
      r ^ φ * Real.exp (ξ * Z) * R =
          Real.exp (Real.log r * φ) * Real.exp (ξ * Z) * Real.exp (Real.log R) := by
        rw [Real.rpow_def_of_pos hr, Real.exp_log hR]
      _ = Real.exp (Real.log r * φ + ξ * Z + Real.log R) := by
        rw [Real.exp_add, Real.exp_add]
      _ = r * Real.exp X := by
        rw [← Real.exp_log hr, ← Real.exp_add]
        simp only [Real.log_exp]
        congr 1
        dsimp [X]
        ring
  rw [hrep]
  have h := GaussianLQG.abs_exp_sub_one_le_mul X
  calc
    |r * Real.exp X - r| = r * |Real.exp X - 1| := by
      rw [← mul_sub_one, abs_mul, abs_of_pos hr]
    _ ≤ r * (|X| * (1 + Real.exp X)) :=
      mul_le_mul_of_nonneg_left h hr.le
    _ = |X| * (r + r * Real.exp X) := by ring

private theorem n5_variance_le_posLog {d : ℕ} {R K r : ℝ}
    (hR : 1 ≤ R) (hr : 0 < r) (hrR : r ≤ 2 * R) (x : Rd d) (hx : ‖x‖ ≤ R)
    (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K)) :
    Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
      Real.posLog r⁻¹ + max 0 (4 * R + K) := by
  have hc : 4 * R + K ≤ max 0 (4 * R + K) := le_max_right _ _
  by_cases hr1 : r ≤ 1
  · have hlog : max 0 (Real.log ‖x‖) ≤ R :=
      max_le (by linarith) ((Real.log_le_self (norm_nonneg x)).trans hx)
    have hvar := (hK hr x).1 hr1
    have hpos : Real.log (1 / r) ≤ Real.posLog r⁻¹ := by
      rw [one_div, Real.posLog_apply]
      exact le_max_right _ _
    linarith
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have hdiv : ‖x‖ / r ≤ R := by
      apply (div_le_iff₀ hr).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ R) (sub_nonneg.mpr hr1')]
    have hlog : max 0 (Real.log (‖x‖ / r)) ≤ R :=
      max_le (by linarith) ((Real.log_le_self (div_nonneg (norm_nonneg x) hr.le)).trans hdiv)
    have hvar := (hK hr x).2 hr1'
    have hlogr : Real.log r ≤ 2 * R :=
      (Real.log_le_self hr.le).trans hrR
    have hpos : 0 ≤ Real.posLog r⁻¹ := Real.posLog_nonneg
    linarith

/-- The log of the unit factor in the recentred field has the concentration norm. -/
theorem n5_eLpNorm_recentre_logRho_le {d : ℕ} (hd : 3 ≤ d)
    (hRot : StrongRotLaw d) {ξ : ℝ} (hξ : 0 < ξ)
    (hgap : Real.sqrt (2 * d) < distExp d ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) (hu : ‖u‖ = 1)
    {q C : ℝ}
    (hconc : eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d)))
      (ENNReal.ofReal q) (normLGFLaw d) ≤ ENNReal.ofReal (C * q * ξ)) :
    eLpNorm (fun g => Real.log ((rho D (recentre 1 r x g)).1 (0, u)))
      (ENNReal.ofReal q) (normLGFLaw d) ≤ ENNReal.ofReal (C * q * ξ) := by
  let Y : DistRd d → ℝ := fun g => Real.log ((rho D (recentre 1 r x g)).1 (0, u))
  let Y₀ : DistRd d → ℝ := fun g => Real.log ((rho D g).1 (0, e₁ d))
  have hunit : Measurable (fun g : DistRd d => (rho D (recentre 1 r x g)).1 (0, u)) :=
    (p2_measurable_contMetric_apply (measurable_rho hD.measurable) _).comp
      (measurable_recentre 1 r x)
  have hunit₀ : Measurable (fun g : DistRd d => (rho D g).1 (0, e₁ d)) :=
    p2_measurable_contMetric_apply (measurable_rho hD.measurable) _
  have hlaw := law_rho_pair_unit hd hRot hξ hgap hD hr x u hu
  have heq : eLpNorm Y (ENNReal.ofReal q) (normLGFLaw d) =
      eLpNorm Y₀ (ENNReal.ofReal q) (normLGFLaw d) := by
    calc
      eLpNorm Y (ENNReal.ofReal q) (normLGFLaw d) =
          eLpNorm Real.log (ENNReal.ofReal q)
            ((normLGFLaw d).map (fun g => (rho D (recentre 1 r x g)).1 (0, u))) := by
        simpa only [Y, Function.comp_def] using
          (eLpNorm_map_measure Real.measurable_log.aestronglyMeasurable hunit.aemeasurable).symm
      _ = eLpNorm Real.log (ENNReal.ofReal q)
            ((normLGFLaw d).map (fun g => (rho D g).1 (0, e₁ d))) := by rw [hlaw]
      _ = eLpNorm Y₀ (ENNReal.ofReal q) (normLGFLaw d) := by
        simpa only [Y₀, Function.comp_def] using
          (eLpNorm_map_measure Real.measurable_log.aestronglyMeasurable hunit₀.aemeasurable)
  exact heq.trans_le hconc

/-- Gaussian `L^q` norm of the spherical factor. -/
theorem n5_eLpNorm_sphereAvg {d : ℕ} (hd : 3 ≤ d)
    {r : ℝ} (hr : 0 < r) (x : Rd d) (q : ℝ) :
    eLpNorm (fun g : DistRd d => sphereAvg g r x)
      (ENNReal.ofReal q) (normLGFLaw d) =
      ENNReal.ofReal (Real.sqrt
        (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d])) *
        eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal q) (gaussianReal 0 1) := by
  let Z : DistRd d → ℝ := fun g => sphereAvg g r x
  have hG := (pair_sphereAvg_gaussian hd hr x).1
  have hmap := hG.map_eq_gaussianReal
  rw [(pair_sphereAvg_gaussian hd hr x).2] at hmap
  have hlaw : HasLaw Z (gaussianReal 0 (Var[Z; normLGFLaw d]).toNNReal)
      (normLGFLaw d) := ⟨hG.aemeasurable, hmap⟩
  have hh := GaussianLQG.eLpNorm_of_hasLaw_gaussianReal hlaw (ENNReal.ofReal q)
  rw [Real.coe_toNNReal _ (variance_nonneg Z (normLGFLaw d))] at hh
  simpa only [Z] using hh

/-- Convert a pairwise lower-integral moment into an `L^q` distance bound. -/
theorem n5_eLpNorm_rho_le {d : ℕ} {D : DistRd d → ContMetric d}
    {q α C r : ℝ} (hq : 0 < q) (hr : 0 < r) (x y : Rd d)
    (hpair : ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (C * r ^ (q * α))) :
    eLpNorm (fun g => (rho D g).1 (x, y)) (ENNReal.ofReal q) (normLGFLaw d) ≤
      ENNReal.ofReal C ^ (1 / q) * ENNReal.ofReal (r ^ α) := by
  have heq : ∀ g : DistRd d,
      ‖(rho D g).1 (x, y)‖ₑ ^ q = ENNReal.ofReal ((rho D g).1 (x, y) ^ q) := by
    intro g
    rw [Real.enorm_eq_ofReal ((rho D g).nonneg x y),
      ENNReal.ofReal_rpow_of_nonneg ((rho D g).nonneg x y) hq.le]
  rw [GaussianLQG.eLpNorm_ofReal_eq hq]
  simp_rw [heq]
  calc
    (∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d)) ^ (1 / q)
      ≤ ENNReal.ofReal (C * r ^ (q * α)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hpair (by positivity)
    _ ≤ ENNReal.ofReal C ^ (1 / q) * ENNReal.ofReal (r ^ (q * α * (1 / q))) :=
      GaussianLQG.ofReal_mul_rpow_rpow_le C hr.le (by positivity)
    _ = ENNReal.ofReal C ^ (1 / q) * ENNReal.ofReal (r ^ α) := by
      congr 1
      congr 1
      field_simp

private theorem n5_rpow_le_sqrt {r R α : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R)
    (hR : 1 ≤ R) (hα : 1 / 2 ≤ α) (hα0 : 0 ≤ α) :
    r ^ α ≤ max 1 ((2 * R) ^ α) * Real.sqrt r := by
  have hK : 1 ≤ max 1 ((2 * R) ^ α) := le_max_left _ _
  have hK0 : 0 ≤ max 1 ((2 * R) ^ α) := zero_le_one.trans hK
  by_cases hr1 : r ≤ 1
  · have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 hα
    rw [← Real.sqrt_eq_rpow] at hp
    exact hp.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) hK)
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have h2R : 0 ≤ 2 * R := by positivity
    have hp : r ^ α ≤ (2 * R) ^ α := Real.rpow_le_rpow hr.le hrR hα0
    have hK' : (2 * R) ^ α ≤ max 1 ((2 * R) ^ α) := le_max_right _ _
    have hs : 1 ≤ Real.sqrt r := by
      have hh := Real.sq_sqrt hr.le
      have hs0 := Real.sqrt_nonneg r
      nlinarith
    calc
      r ^ α ≤ (2 * R) ^ α := hp
      _ ≤ max 1 ((2 * R) ^ α) := hK'
      _ ≤ max 1 ((2 * R) ^ α) * Real.sqrt r :=
        le_mul_of_one_le_right hK0 hs

private theorem n5_eLpNorm_rho_le_sqrt {d : ℕ}
    {D : DistRd d → ContMetric d} {q α C r R : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hrR : r ≤ 2 * R) (hR : 1 ≤ R)
    (hα : 1 / 2 ≤ α) (hα0 : 0 ≤ α) (x y : Rd d)
    (hpair : ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (C * r ^ (q * α))) :
    eLpNorm (fun g => (rho D g).1 (x, y)) (ENNReal.ofReal q) (normLGFLaw d) ≤
      ENNReal.ofReal
        (((ENNReal.ofReal C ^ (1 / q)).toReal * max 1 ((2 * R) ^ α)) * Real.sqrt r) := by
  have h := n5_eLpNorm_rho_le hq hr x y hpair
  have hCfinite : ENNReal.ofReal C ^ (1 / q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hCr : 0 ≤ (ENNReal.ofReal C ^ (1 / q)).toReal := ENNReal.toReal_nonneg
  have hK : 0 ≤ max 1 ((2 * R) ^ α) := zero_le_one.trans (le_max_left _ _)
  have hrpow := n5_rpow_le_sqrt hr hrR hR hα hα0
  calc
    _ ≤ ENNReal.ofReal C ^ (1 / q) * ENNReal.ofReal (r ^ α) := h
    _ = ENNReal.ofReal ((ENNReal.ofReal C ^ (1 / q)).toReal) *
        ENNReal.ofReal (r ^ α) := by rw [ENNReal.ofReal_toReal hCfinite]
    _ ≤ ENNReal.ofReal ((ENNReal.ofReal C ^ (1 / q)).toReal) *
        ENNReal.ofReal (max 1 ((2 * R) ^ α) * Real.sqrt r) := by
      gcongr
    _ = ENNReal.ofReal
        (((ENNReal.ofReal C ^ (1 / q)).toReal * max 1 ((2 * R) ^ α)) * Real.sqrt r) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hCr hK), ENNReal.ofReal_mul hCr,
        ENNReal.ofReal_mul hK]
      ring

private theorem n5_eLpNorm_log_factor_le {d : ℕ} (hd : 3 ≤ d)
    (hRot : StrongRotLaw d) {ξ : ℝ} (hξ : 0 < ξ)
    (hgap : Real.sqrt (2 * d) < distExp d ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) (hu : ‖u‖ = 1)
    {p Cc A : ℝ} (hp : 1 ≤ p) (hCc : 0 ≤ Cc) (hA : 0 ≤ A)
    (hconc : eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d)))
      (ENNReal.ofReal (2 * p)) (normLGFLaw d) ≤ ENNReal.ofReal (Cc * (2 * p) * ξ))
    (hphi : |phiXi d ξ - 1| ≤ A * ξ) :
    let q := 2 * p
    let Z : DistRd d → ℝ := fun g => sphereAvg g r x
    let Y : DistRd d → ℝ := fun g => Real.log ((rho D (recentre 1 r x g)).1 (0, u))
    let X : DistRd d → ℝ := fun g => ξ * Z g + Y g + (phiXi d ξ - 1) * Real.log r
    let mN := eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal q) (gaussianReal 0 1)
    eLpNorm X (ENNReal.ofReal q) (normLGFLaw d) ≤
      ENNReal.ofReal (ξ *
        (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal + Cc * q + A * |Real.log r|)) := by
  let q : ℝ := 2 * p
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by dsimp [q]; linarith)
  let Z : DistRd d → ℝ := fun g => sphereAvg g r x
  let Y : DistRd d → ℝ := fun g => Real.log ((rho D (recentre 1 r x g)).1 (0, u))
  let X : DistRd d → ℝ := fun g => ξ * Z g + Y g + (phiXi d ξ - 1) * Real.log r
  let mN : ℝ≥0∞ := eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal q) (gaussianReal 0 1)
  have hmN : mN ≠ ⊤ :=
    (memLp_id_gaussianReal' (ENNReal.ofReal q) ENNReal.ofReal_ne_top).eLpNorm_ne_top
  have hZ : Measurable Z := measurable_sphereAvg_left r x
  have hY : Measurable Y :=
    (measurable_log_rho_apply hD.measurable _).comp (measurable_recentre 1 r x)
  have hT1 : eLpNorm (fun g => ξ * Z g) (ENNReal.ofReal q) (normLGFLaw d) =
      ENNReal.ofReal (ξ * (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal)) := by
    have he : (fun g => ξ * Z g) = ξ • Z := rfl
    rw [he, eLpNorm_const_smul, n5_eLpNorm_sphereAvg hd hr x q,
      Real.enorm_eq_ofReal hξ.le, ENNReal.ofReal_mul hξ.le,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hmN]
  have hT2 : eLpNorm Y (ENNReal.ofReal q) (normLGFLaw d) ≤
      ENNReal.ofReal (Cc * q * ξ) :=
    n5_eLpNorm_recentre_logRho_le hd hRot hξ hgap hD hr x u hu hconc
  have hT3 : eLpNorm (fun _ : DistRd d => (phiXi d ξ - 1) * Real.log r)
      (ENNReal.ofReal q) (normLGFLaw d) ≤
        ENNReal.ofReal (A * ξ * |Real.log r|) := by
    haveI : IsProbabilityMeasure (normLGFLaw d) :=
      (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
    rw [GaussianLQG.eLpNorm_const_prob _ (ENNReal.ofReal_pos.2 hq).ne',
      Real.enorm_eq_ofReal_abs, abs_mul]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hphi (abs_nonneg _))
  have hm1 : AEStronglyMeasurable (fun g => ξ * Z g) (normLGFLaw d) :=
    (hZ.const_mul _).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable Y (normLGFLaw d) := hY.aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun _ : DistRd d => (phiXi d ξ - 1) * Real.log r)
      (normLGFLaw d) := aestronglyMeasurable_const
  have hXeq : X = (fun g => ξ * Z g) + Y +
      (fun _ => (phiXi d ξ - 1) * Real.log r) := rfl
  change eLpNorm X (ENNReal.ofReal q) (normLGFLaw d) ≤ _
  rw [hXeq]
  calc
    eLpNorm ((fun g => ξ * Z g) + Y +
        (fun _ => (phiXi d ξ - 1) * Real.log r)) (ENNReal.ofReal q) (normLGFLaw d)
      ≤ eLpNorm ((fun g => ξ * Z g) + Y) (ENNReal.ofReal q) (normLGFLaw d) +
          eLpNorm (fun _ : DistRd d => (phiXi d ξ - 1) * Real.log r)
            (ENNReal.ofReal q) (normLGFLaw d) :=
        eLpNorm_add_le (hm1.add hm2) hm3 hq1
    _ ≤ eLpNorm (fun g => ξ * Z g) (ENNReal.ofReal q) (normLGFLaw d) +
          eLpNorm Y (ENNReal.ofReal q) (normLGFLaw d) +
          eLpNorm (fun _ : DistRd d => (phiXi d ξ - 1) * Real.log r)
            (ENNReal.ofReal q) (normLGFLaw d) := by
        gcongr
        exact eLpNorm_add_le hm1 hm2 hq1
    _ ≤ ENNReal.ofReal (ξ * (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal)) +
          ENNReal.ofReal (Cc * q * ξ) + ENNReal.ofReal (A * ξ * |Real.log r|) := by
        rw [hT1]
        gcongr
    _ = ENNReal.ofReal (ξ *
          (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal + Cc * q + A * |Real.log r|)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Fixed pair Euclidean error from the concentration and pair moments. -/
private theorem n5_eLpNorm_pair_error_le {d : ℕ} (hd : 3 ≤ d)
    (hRot : StrongRotLaw d) {ξ : ℝ} (hξ : 0 < ξ)
    (hgap : Real.sqrt (2 * d) < distExp d ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {R r : ℝ} (hR : 1 ≤ R) (hr : 0 < r) (hrR : r ≤ 2 * R)
    (x u : Rd d) (hu : ‖u‖ = 1)
    {p Cc A C5 α K : ℝ} (hp : 1 ≤ p) (hCc : 0 ≤ Cc) (hA : 0 ≤ A)
    (hα : 1 / 2 ≤ α) (hα0 : 0 ≤ α)
    (hconc : eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d)))
      (ENNReal.ofReal (2 * p)) (normLGFLaw d) ≤ ENNReal.ofReal (Cc * (2 * p) * ξ))
    (hphi : |phiXi d ξ - 1| ≤ A * ξ)
    (hpair : ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ (2 * p))
      ∂(normLGFLaw d) ≤ ENNReal.ofReal (C5 * r ^ ((2 * p) * α)))
    (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K))
    (hx : ‖x‖ ≤ R) :
    let q := 2 * p
    let c0 := max 0 (4 * R + K)
    let CA := (ENNReal.ofReal C5 ^ (1 / q)).toReal * max 1 ((2 * R) ^ α)
    let mN := eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal q) (gaussianReal 0 1)
    let C4 := (mN.toReal * Real.sqrt (1 + 2 * R * c0) +
        Cc * q * Real.sqrt (2 * R) + A * (2 + 4 * R ^ 2)) *
        (Real.sqrt (2 * R) + CA)
    eLpNorm (fun g => (rho D g).1 (x, x + r • u) - r)
      (ENNReal.ofReal p) (normLGFLaw d) ≤ ENNReal.ofReal (ξ * C4) := by
  let q : ℝ := 2 * p
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by dsimp [q]; linarith)
  letI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal q)
      (ENNReal.ofReal p) := by
    dsimp [q]
    exact GaussianLQG.holderTriple_two_mul hp0
  let Z : DistRd d → ℝ := fun g => sphereAvg g r x
  let Y : DistRd d → ℝ := fun g => Real.log ((rho D (recentre 1 r x g)).1 (0, u))
  let X : DistRd d → ℝ := fun g => ξ * Z g + Y g + (phiXi d ξ - 1) * Real.log r
  let G : DistRd d → ℝ := fun g => r + (rho D g).1 (x, x + r • u)
  let mN : ℝ≥0∞ := eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal q) (gaussianReal 0 1)
  let c0 : ℝ := max 0 (4 * R + K)
  let CA : ℝ := (ENNReal.ofReal C5 ^ (1 / q)).toReal * max 1 ((2 * R) ^ α)
  let C4 : ℝ := (mN.toReal * Real.sqrt (1 + 2 * R * c0) +
      Cc * q * Real.sqrt (2 * R) + A * (2 + 4 * R ^ 2)) *
      (Real.sqrt (2 * R) + CA)
  have hmZ : Measurable Z := measurable_sphereAvg_left r x
  have hmY : Measurable Y :=
    (measurable_log_rho_apply hD.measurable _).comp (measurable_recentre 1 r x)
  have hmX : Measurable X :=
    ((measurable_const.mul hmZ).add hmY).add_const _
  have hmD : Measurable (fun g : DistRd d => (rho D g).1 (x, x + r • u)) :=
    p2_measurable_contMetric_apply (measurable_rho hD.measurable) _
  have hmG : Measurable G := measurable_const.add hmD
  have hRpos (g : DistRd d) : 0 < (rho D (recentre 1 r x g)).1 (0, u) := by
    apply (rho D (recentre 1 r x g)).apply_pos
    intro he
    have : u = 0 := he.symm
    simp [this] at hu
  have hpoint : ∀ᵐ g ∂(normLGFLaw d),
      |(rho D g).1 (x, x + r • u) - r| ≤ |X g| * G g := by
    filter_upwards [rho_pair_repr hd hξ hD hr x u] with g hg
    dsimp [X, Y, Z, G]
    rw [hg]
    exact n5_abs_scaled_pair_sub_le hr (hRpos g)
  have step1 : eLpNorm (fun g => (rho D g).1 (x, x + r • u) - r)
      (ENNReal.ofReal p) (normLGFLaw d) ≤
      eLpNorm X (ENNReal.ofReal q) (normLGFLaw d) *
        eLpNorm G (ENNReal.ofReal q) (normLGFLaw d) := by
    calc
      eLpNorm (fun g => (rho D g).1 (x, x + r • u) - r)
          (ENNReal.ofReal p) (normLGFLaw d)
        ≤ eLpNorm (fun g => X g * G g) (ENNReal.ofReal p) (normLGFLaw d) := by
          apply eLpNorm_mono_ae
          filter_upwards [hpoint] with g hg
          have hG0 : 0 ≤ G g := by
            change 0 ≤ r + (rho D g).1 (x, x + r • u)
            exact add_nonneg hr.le ((rho D g).nonneg x (x + r • u))
          simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hG0] using hg
      _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm X (ENNReal.ofReal q) (normLGFLaw d) *
            eLpNorm G (ENNReal.ofReal q) (normLGFLaw d) :=
        eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hmX.aestronglyMeasurable
          hmG.aestronglyMeasurable (fun x y : ℝ => x * y) 1
          (ae_of_all _ fun g => by rw [norm_mul, NNReal.coe_one, one_mul])
      _ = _ := by rw [ENNReal.coe_one, one_mul]
  have hXnorm : eLpNorm X (ENNReal.ofReal q) (normLGFLaw d) ≤
      ENNReal.ofReal (ξ *
        (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal + Cc * q + A * |Real.log r|)) := by
    exact n5_eLpNorm_log_factor_le hd hRot hξ hgap hD hr x u hu hp hCc hA
      (by simpa only [q] using hconc) hphi
  have hDnorm : eLpNorm (fun g => (rho D g).1 (x, x + r • u))
      (ENNReal.ofReal q) (normLGFLaw d) ≤ ENNReal.ofReal (CA * Real.sqrt r) := by
    exact n5_eLpNorm_rho_le_sqrt hq0 hr hrR hR hα hα0 x (x + r • u)
      (by simpa only [q] using hpair)
  have hGnorm : eLpNorm G (ENNReal.ofReal q) (normLGFLaw d) ≤
      ENNReal.ofReal (r + CA * Real.sqrt r) := by
    haveI : IsProbabilityMeasure (normLGFLaw d) :=
      (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
    rw [show G = (fun _ => r) + fun g => (rho D g).1 (x, x + r • u) from rfl]
    calc
      _ ≤ eLpNorm (fun _ : DistRd d => r) (ENNReal.ofReal q) (normLGFLaw d) +
          eLpNorm (fun g => (rho D g).1 (x, x + r • u))
            (ENNReal.ofReal q) (normLGFLaw d) :=
        eLpNorm_add_le aestronglyMeasurable_const hmD.aestronglyMeasurable hq1
      _ = ENNReal.ofReal r + eLpNorm (fun g => (rho D g).1 (x, x + r • u))
          (ENNReal.ofReal q) (normLGFLaw d) := by
        rw [GaussianLQG.eLpNorm_const_prob _ (ENNReal.ofReal_pos.2 hq0).ne',
          Real.enorm_eq_ofReal hr.le]
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal (CA * Real.sqrt r) := by gcongr
      _ = ENNReal.ofReal (r + CA * Real.sqrt r) := by
        rw [← ENNReal.ofReal_add hr.le (by dsimp [CA]; positivity)]
  have hvar : Var[Z; normLGFLaw d] ≤ Real.posLog r⁻¹ + c0 :=
    n5_variance_le_posLog hR hr hrR x hx hK
  have hc0 : 0 ≤ c0 := le_max_left _ _
  have hCA : 0 ≤ CA := by dsimp [CA]; positivity
  have hdet :
      (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal + Cc * q + A * |Real.log r|) *
        (r + CA * Real.sqrt r) ≤ C4 := by
    have hh := GaussianLQG.pair_bound_le (v := Var[Z; normLGFLaw d]) (m := mN.toReal)
      (Cc := Cc * q) (C1 := A) (E := 1) (CA := CA) (ρ := R) (c0 := c0)
      hr hrR hc0 hvar ENNReal.toReal_nonneg (mul_nonneg hCc hq0.le)
      hA (by norm_num) hCA
    convert hh using 1 <;> simp only [one_mul] <;> ring
  change eLpNorm (fun g => (rho D g).1 (x, x + r • u) - r)
    (ENNReal.ofReal p) (normLGFLaw d) ≤ ENNReal.ofReal (ξ * C4)
  calc
    _ ≤ eLpNorm X (ENNReal.ofReal q) (normLGFLaw d) *
          eLpNorm G (ENNReal.ofReal q) (normLGFLaw d) := step1
    _ ≤ ENNReal.ofReal (ξ *
          (Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal + Cc * q + A * |Real.log r|)) *
          ENNReal.ofReal (r + CA * Real.sqrt r) := by gcongr
    _ = ENNReal.ofReal (ξ *
          ((Real.sqrt (Var[Z; normLGFLaw d]) * mN.toReal + Cc * q + A * |Real.log r|) *
            (r + CA * Real.sqrt r))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (ξ * C4) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hdet hξ.le)

/-- The fixed-pair Euclidean estimate (5.4), uniformly for a small parameter
window and all strong assignments. -/
theorem pairEuclid {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hC : ConcentrationStmt d)
    {R p : ℝ} (hR : 1 ≤ R) (hp : 1 ≤ p) :
    ∃ ξ₃ C₄ : ℝ, 0 < ξ₃ ∧ 0 ≤ C₄ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₃,
        ∀ D : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
            ∀ x y : Rd d, ‖x‖ ≤ R → ‖y‖ ≤ R →
              eLpNorm (fun g => (rho D g).1 (x, y) - dist x y)
                (ENNReal.ofReal p) (normLGFLaw d) ≤ ENNReal.ofReal (C₄ * ξ) := by
  obtain ⟨ξ₄, C5, hξ₄, hC5, hpair⟩ :=
    lintegral_rho_rpow_le_pair_radius hd hφ hRot hC hR
      (by linarith : 1 ≤ 2 * R) (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : 1 ≤ 2 * p)
  obtain ⟨ξ₂, Cc, hξ₂, hCc, hconc⟩ := hC
  obtain ⟨K, hK⟩ := exists_pair_sphereAvg_variance_le hd
  let q : ℝ := 2 * p
  let c0 : ℝ := max 0 (4 * R + K)
  let CA : ℝ := (ENNReal.ofReal C5 ^ (1 / q)).toReal * max 1 ((2 * R) ^ (7 / 8 : ℝ))
  let mN : ℝ≥0∞ := eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal q) (gaussianReal 0 1)
  let C4 : ℝ := (mN.toReal * Real.sqrt (1 + 2 * R * c0) +
      Cc * q * Real.sqrt (2 * R) + Real.sqrt (2 * d) * (2 + 4 * R ^ 2)) *
      (Real.sqrt (2 * R) + CA)
  have hC4 : 0 ≤ C4 := by
    dsimp [C4, CA, c0]
    have hq : 0 < q := by dsimp [q]; linarith
    have hCc0 : 0 ≤ Cc := hCc
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    positivity
  let ξ₃ := min ξ₂ (min ξ₄ (min hφ.choose (xiCrit d / 2)))
  have hξ₃ : 0 < ξ₃ := by
    dsimp [ξ₃]
    simp only [lt_min_iff]
    exact ⟨hξ₂, hξ₄, hφ.choose_spec.1, by
      have := xiCrit_pos (by omega : 2 ≤ d)
      positivity⟩
  refine ⟨ξ₃, C4, hξ₃, hC4, ?_⟩
  intro ξ hξ D hD x y hx hy
  have hξ0 : 0 < ξ := hξ.1
  have hξ₂' : ξ ≤ ξ₂ :=
    hξ.2.trans (by dsimp [ξ₃]; exact min_le_left _ _)
  have hξ₄' : ξ ≤ ξ₄ := by
    calc ξ ≤ ξ₃ := hξ.2
      _ ≤ ξ₄ := by dsimp [ξ₃]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hξφ : ξ ≤ hφ.choose := by
    calc ξ ≤ ξ₃ := hξ.2
      _ ≤ hφ.choose := by
        dsimp [ξ₃]
        exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hξc : ξ ≤ xiCrit d / 2 := by
    calc ξ ≤ ξ₃ := hξ.2
      _ ≤ xiCrit d / 2 := by
        dsimp [ξ₃]
        exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : Real.sqrt (2 * d) < distExp d ξ := by
    apply (sqrt_lt_distExp_iff (by omega : 2 ≤ d) hξ0).2
    have hc := xiCrit_pos (by omega : 2 ≤ d)
    linarith
  have hphi : |phiXi d ξ - 1| ≤ Real.sqrt (2 * d) * ξ := by
    rw [phiXi_of_pos hξ0]
    exact hφ.choose_spec.2 ξ ⟨hξ0, hξφ⟩
  by_cases hxy : x = y
  · subst y
    simp only [dist_self, sub_zero]
    have heq : (fun g : DistRd d => (rho D g).1 (x, x)) = fun _ => (0 : ℝ) :=
      funext fun g => (rho D g).apply_self x
    rw [heq, eLpNorm_zero']
    exact zero_le
  · let r := dist x y
    have hr : 0 < r := dist_pos.mpr hxy
    have hrR : r ≤ 2 * R := by
      have hn := norm_sub_le x y
      calc
        r = ‖x - y‖ := dist_eq_norm x y
        _ ≤ ‖x‖ + ‖y‖ := hn
        _ ≤ 2 * R := by linarith
    let u : Rd d := r⁻¹ • (y - x)
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ← dist_eq_norm,
        dist_comm y x]
      exact inv_mul_cancel₀ hr.ne'
    have hyu : x + r • u = y := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    have hpair' : ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ (2 * p))
        ∂(normLGFLaw d) ≤ ENNReal.ofReal (C5 * r ^ ((2 * p) * (7 / 8 : ℝ))) := by
      have hh := hpair ξ ⟨hξ0, hξ₄'⟩ D hD x y hx hrR
      simpa only [hyu, r, show (1 - (1 - (1 / 2 : ℝ)) / 4) = 7 / 8 by norm_num]
        using hh
    have hconc' := hconc ξ ⟨hξ0, hξ₂'⟩ D hD (2 * p) (by linarith)
    have hh := n5_eLpNorm_pair_error_le hd hRot hξ0 hgap hD hR hr hrR x u hu hp
      hCc (Real.sqrt_nonneg _) (by norm_num : (1 / 2 : ℝ) ≤ 7 / 8)
      (by norm_num : (0 : ℝ) ≤ 7 / 8) hconc' hphi hpair' hK hx
    simpa only [q, c0, CA, mN, C4, hyu, r, mul_comm] using hh

end HigherDimLQGContinuity
