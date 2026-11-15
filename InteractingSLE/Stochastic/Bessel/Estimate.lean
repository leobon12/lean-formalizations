/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.TestFunction
import QuantumZipper.Proofs.ItoLite.Increments

/-!
# The occupation estimate for regularized Bessel processes

Packet PROVE-BESSEL. Let `B` be a pre-Brownian motion with continuous paths, `c > 0`, `x ≥ 0`, and
let `U = regProc c ε x B` solve `U_t = x + B_t + ∫₀ᵗ c / max U_r ε dr` (`regProc_integralEq`).
With the cutoff `cut η y = min 1 (max 0 (2 - y/η))` (`= 1` on `y ≤ η`, `= 0` on `y ≥ 2η`) and
`J_η = ∫₀ᵗ cut η (U_r) · c / max U_r ε dr`, there are constants independent of `ε` such that

* `E ∫₀ᵗ c / max U_r ε dr ≤ K` for `ε ≤ η₀` (`integral_regA_le`), and
* `E J_η ≤ C (2η)^{1-p}` for `ε ≤ η` and `ε ≤ η₀` (`integral_regJ_le`),

where `p = 1 - min c 1 / 8` (`besselExp`). The proof applies QuantumZipper's Dynkin formula
(`QuantumZipper.Dynkin.dynkin_additive`, additive noise, Lipschitz bounded drift) to the test
function `testFun p ε` of `TestFunction.lean`: `E F(U_t) - F(x) = E ∫₀ᵗ LF(U_r) dr`, where
`LF ≥ (p/4)(2η)^{p-1} cut η · b` and `F(U_t) - F(x) ≤ 1 + U_t⁺ ≤ 1 + |x + B_t| + J_η + ct/η`.
At the level `η₀` with `(p/4)(2η₀)^{p-1} = 2` this bounds `E J_{η₀}`, hence `E ∫ b(U)`, and then
`E J_η` for every `η`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Bessel

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The natural filtration and the regularized process -/

/-- The natural filtration of `B`, `σ(B_r : r ≤ t)`, as a `Filtration`. -/
def natFilt (hBm : ∀ r, Measurable (B r)) : Filtration ℝ≥0 mΩ where
  seq := QuantumZipper.bmFiltration B
  mono' := fun _ t hst => iSup₂_le fun r hr =>
    le_iSup₂_of_le (f := fun r (_ : r ≤ t) => (inferInstance : MeasurableSpace ℝ).comap (B r))
      r (hr.trans hst) le_rfl
  le' := QuantumZipper.bmFiltration_le hBm

theorem natFilt_adapted (hBm : ∀ r, Measurable (B r)) (t : ℝ≥0) :
    Measurable[natFilt hBm t] (B t) :=
  measurable_iff_comap_le.2
    (le_iSup₂_of_le (f := fun r (_ : r ≤ t) => (inferInstance : MeasurableSpace ℝ).comap (B r))
      t le_rfl le_rfl)

theorem natFilt_le_past (hBm : ∀ r, Measurable (B r)) (t : ℝ≥0) :
    natFilt hBm t ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi :=
  QuantumZipper.bmFiltration_le_comap_restrict t

/-- The path of `B` in real time, `t ↦ B t⁺`. -/
def realPath (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ := B t.toNNReal ω

omit mΩ in
theorem continuous_realPath (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Continuous (realPath B ω) :=
  (hBc ω).comp continuous_real_toNNReal

/-- The regularized Bessel process `U_t = x + B_t + ∫₀ᵗ c / max U_r ε dr` driven by `B`. -/
def regProc (c ε x : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  regSol c ε x (realPath B ω) t

variable {c ε x : ℝ}

omit mΩ in
theorem integral_regDrift_regSol_eq (ω : Ω) (t : ℝ≥0) :
    ∫ r in (0 : ℝ)..t, regDrift c ε (regSol c ε x (realPath B ω) r)
      = ∫ r in (0 : ℝ)..t, regDrift c ε (regProc c ε x B r.toNNReal ω) := by
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le t.coe_nonneg] at hr
  simp only [regProc, Real.coe_toNNReal r hr.1]

omit mΩ in
/-- The regularized process solves the additive-noise equation of `QuantumZipper.Dynkin`. -/
theorem regProc_integralEq (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (ω : Ω)
    (t : ℝ≥0) :
    regProc c ε x B t ω
      = x + (∫ r in (0 : ℝ)..t, regDrift c ε (regProc c ε x B r.toNNReal ω)) + B t ω • (1 : ℝ) := by
  rw [← integral_regDrift_regSol_eq ω t, smul_eq_mul, mul_one]
  rw [regProc, regSol_eq (continuous_realPath hBc ω) hc hε x t.coe_nonneg]
  simp only [realPath, Real.toNNReal_coe]
  ring

theorem norm_regDrift_le (hc : 0 ≤ c) (hε : 0 < ε) (y : ℝ) : ‖regDrift c ε y‖ ≤ c / ε := by
  rw [Real.norm_eq_abs]; exact abs_regDrift_le hc hε y

theorem continuous_regProc (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (ω : Ω) :
    Continuous (regProc c ε x B · ω) :=
  QuantumZipper.Dynkin.continuous_of_integralEq hBc (continuous_regDrift hc hε)
    (norm_regDrift_le hc hε) (regProc_integralEq hBc hc hε) ω

/-- **Adaptedness** of the regularized process to any filtration to which `B` is adapted. -/
theorem regProc_measurable (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) :
    Measurable[𝓕 t] (regProc c ε x B t) :=
  QuantumZipper.Dynkin.measurable_of_integralEq 𝓕 hBad hBc (lipschitzWith_regDrift hc hε)
    (norm_regDrift_le hc hε) (regProc_integralEq hBc hc hε) (continuous_regProc hBc hc hε) t

/-! ### Cutoffs and drift integrals -/

/-- The cutoff `min 1 (max 0 (2 - y/η))`: `1` on `y ≤ η`, `0` on `y ≥ 2η`. -/
def cut (η y : ℝ) : ℝ := min 1 (max 0 (2 - y / η))

theorem cut_nonneg (η y : ℝ) : 0 ≤ cut η y := le_min zero_le_one (le_max_left _ _)

theorem cut_le_one (η y : ℝ) : cut η y ≤ 1 := min_le_left _ _

theorem cut_eq_one {η y : ℝ} (hη : 0 < η) (hy : y ≤ η) : cut η y = 1 := by
  have h1 : y / η ≤ 1 := (div_le_one hη).2 hy
  have : 1 ≤ 2 - y / η := by linarith
  exact min_eq_left (le_max_of_le_right this)

theorem cut_eq_zero {η y : ℝ} (hη : 0 < η) (hy : 2 * η ≤ y) : cut η y = 0 := by
  have : 2 - y / η ≤ 0 := by
    have : 2 ≤ y / η := by rw [le_div_iff₀ hη]; linarith
    linarith
  rw [cut, max_eq_left this, min_eq_right zero_le_one]

theorem continuous_cut (η : ℝ) : Continuous (cut η) :=
  continuous_const.min (continuous_const.max (continuous_const.sub (continuous_id.div_const η)))

/-- The drift integral `A_t = ∫₀ᵗ c / max U_r ε dr` of the regularized process. -/
def regA (c ε x : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t, regDrift c ε (regProc c ε x B r.toNNReal ω)

/-- The drift integral near zero, `J_η = ∫₀ᵗ cut η (U_r) · c / max U_r ε dr`. -/
def regJ (c ε x η : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t, cut η (regProc c ε x B r.toNNReal ω) * regDrift c ε (regProc c ε x B r.toNNReal ω)

omit mΩ in
theorem regProc_eq_add_regA (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (ω : Ω)
    (t : ℝ≥0) : regProc c ε x B t ω = x + B t ω + regA c ε x B t ω := by
  rw [regProc_integralEq hBc hc hε ω t, regA, smul_eq_mul, mul_one]; ring

theorem continuous_regDrift_regProc (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε)
    (ω : Ω) : Continuous fun r : ℝ => regDrift c ε (regProc c ε x B r.toNNReal ω) :=
  (continuous_regDrift hc hε).comp ((continuous_regProc hBc hc hε ω).comp continuous_real_toNNReal)

theorem continuous_cut_regDrift_regProc (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε)
    (η : ℝ) (ω : Ω) : Continuous fun r : ℝ =>
      cut η (regProc c ε x B r.toNNReal ω) * regDrift c ε (regProc c ε x B r.toNNReal ω) :=
  ((continuous_cut η).comp ((continuous_regProc hBc hc hε ω).comp continuous_real_toNNReal)).mul
    (continuous_regDrift_regProc hBc hc hε ω)

omit mΩ in
theorem regA_nonneg (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) (ω : Ω) : 0 ≤ regA c ε x B t ω :=
  intervalIntegral.integral_nonneg t.coe_nonneg fun _ _ => regDrift_nonneg hc hε _

omit mΩ in
theorem regJ_nonneg (hc : 0 ≤ c) (hε : 0 < ε) (η : ℝ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ regJ c ε x η B t ω :=
  intervalIntegral.integral_nonneg t.coe_nonneg fun _ _ =>
    mul_nonneg (cut_nonneg _ _) (regDrift_nonneg hc hε _)

theorem regJ_le (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (η : ℝ) (t : ℝ≥0)
    (ω : Ω) : regJ c ε x η B t ω ≤ c / ε * t := by
  have h := intervalIntegral.integral_mono_on t.coe_nonneg
    ((continuous_cut_regDrift_regProc hBc hc hε η ω).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := c / ε)) fun r _ => by
      calc cut η (regProc c ε x B r.toNNReal ω) * regDrift c ε (regProc c ε x B r.toNNReal ω)
          ≤ 1 * (c / ε) := mul_le_mul (cut_le_one _ _) (regDrift_le hc hε _)
            (regDrift_nonneg hc hε _) zero_le_one
        _ = c / ε := one_mul _
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  rw [regJ]; linarith

theorem regA_le (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) (ω : Ω) :
    regA c ε x B t ω ≤ c / ε * t := by
  have h := intervalIntegral.integral_mono_on t.coe_nonneg
    ((continuous_regDrift_regProc (x := x) hBc hc hε ω).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := c / ε)) fun _ _ => regDrift_le hc hε _
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  rw [regA]; linarith

/-- `A_t ≤ J_η + c t / η` for `ε ≤ η`. -/
theorem regA_le_regJ_add (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) {η : ℝ}
    (hεη : ε ≤ η) (t : ℝ≥0) (ω : Ω) :
    regA c ε x B t ω ≤ regJ c ε x η B t ω + c / η * t := by
  have hη : 0 < η := hε.trans_le hεη
  have hint1 := (continuous_regDrift_regProc (x := x) hBc hc hε ω).intervalIntegrable (μ := volume)
    0 (t : ℝ)
  have hint2 := ((continuous_cut_regDrift_regProc (x := x) hBc hc hε η ω).add
    (continuous_const (y := c / η))).intervalIntegrable (μ := volume) 0 (t : ℝ)
  have h := intervalIntegral.integral_mono_on t.coe_nonneg hint1 hint2 fun r _ => by
    set y := regProc c ε x B r.toNNReal ω
    show regDrift c ε y ≤ cut η y * regDrift c ε y + c / η
    rcases le_total y η with hy | hy
    · rw [cut_eq_one hη hy, one_mul]; linarith [div_nonneg hc hη.le]
    · have hb : regDrift c ε y ≤ c / η := by
        rw [regDrift_of_le (hεη.trans hy)]
        exact div_le_div_of_nonneg_left hc hη hy
      nlinarith [mul_nonneg (cut_nonneg η y) (regDrift_nonneg hc hε y)]
  simp only [Pi.add_apply] at h
  rw [intervalIntegral.integral_add ((continuous_cut_regDrift_regProc hBc hc hε η ω).intervalIntegrable
    0 t) (intervalIntegrable_const (μ := volume)), intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  rw [regA, regJ]; linarith

/-! ### Measurability and integrability -/

theorem regProc_measurable' (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) : Measurable (regProc c ε x B t) :=
  (regProc_measurable (natFilt hBm) (natFilt_adapted hBm) hBc hc hε t).mono ((natFilt hBm).le t)
    le_rfl

theorem regJ_measurable (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    (hc : 0 ≤ c) (hε : 0 < ε) (η : ℝ) (t : ℝ≥0) : Measurable (regJ c ε x η B t) :=
  QuantumZipper.Dynkin.measurable_intervalIntegral_of_continuous
    (Y := fun r ω => cut η (regProc c ε x B r.toNNReal ω) * regDrift c ε (regProc c ε x B r.toNNReal ω))
    (fun _ => ((continuous_cut η).measurable.comp (regProc_measurable' hBm hBc hc hε _)).mul
      ((continuous_regDrift hc hε).measurable.comp (regProc_measurable' hBm hBc hc hε _)))
    (fun ω => continuous_cut_regDrift_regProc hBc hc hε η ω) 0 t

theorem regA_measurable (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) : Measurable (regA c ε x B t) :=
  QuantumZipper.Dynkin.measurable_intervalIntegral_of_continuous
    (Y := fun r ω => regDrift c ε (regProc c ε x B r.toNNReal ω))
    (fun _ => (continuous_regDrift hc hε).measurable.comp (regProc_measurable' hBm hBc hc hε _))
    (fun ω => continuous_regDrift_regProc hBc hc hε ω) 0 t

theorem integrable_regJ [IsFiniteMeasure P] (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (η : ℝ) (t : ℝ≥0) :
    Integrable (regJ c ε x η B t) P :=
  Integrable.of_bound (regJ_measurable hBm hBc hc hε η t).aestronglyMeasurable (c / ε * t)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (regJ_nonneg hc hε η t ω)]
      exact regJ_le hBc hc hε η t ω)

theorem integrable_regA [IsFiniteMeasure P] (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) :
    Integrable (regA c ε x B t) P :=
  Integrable.of_bound (regA_measurable hBm hBc hc hε t).aestronglyMeasurable (c / ε * t)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (regA_nonneg hc hε t ω)]
      exact regA_le hBc hc hε t ω)

theorem integrable_abs_add_eval (hB : IsPreBrownianReal B P) (x : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => |x + B t ω|) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact ((integrable_const x).add (hB.integrable_eval t)).abs

omit mΩ in
/-- `U_t⁺ ≤ |x + B_t| + A_t`. -/
theorem max_regProc_le (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0)
    (ω : Ω) : max (regProc c ε x B t ω) 0 ≤ |x + B t ω| + regA c ε x B t ω := by
  rw [regProc_eq_add_regA hBc hc hε ω t]
  have h1 := regA_nonneg (x := x) (B := B) hc hε t ω
  have h2 := le_abs_self (x + B t ω)
  have h3 := abs_nonneg (x + B t ω)
  exact max_le (by linarith) (by linarith)

theorem integrable_max_regProc (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) :
    Integrable (fun ω => max (regProc c ε x B t ω) 0) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ((integrable_abs_add_eval hB x t).add (integrable_regA (x := x) hBm hBc hc hε t)).mono'
    ((regProc_measurable' hBm hBc hc hε t).max measurable_const).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_regProc_le hBc hc hε t ω

/-! ### The Dynkin step -/

/-- The generator of the test function dominates the localized drift. -/
theorem generator_ge_cut {p η : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c) (hpc : 1 - p ≤ c / 8)
    (hε : 0 < ε) (hεη : ε ≤ η) (y : ℝ) :
    p / 4 * (2 * η) ^ (p - 1) * (cut η y * regDrift c ε y)
      ≤ QuantumZipper.dynkinGen (regDrift c ε) (1 : ℝ) (testFun p ε) y := by
  rw [dynkinGen_testFun_eq hε]
  have hgen := le_testFun_generator hp0 hp1 hc hpc hε y
  have hη : 0 < η := hε.trans_le hεη
  have hb := regDrift_nonneg hc.le hε y
  have hM : 0 < max y ε := hε.trans_le (le_max_right _ _)
  have hMp : 0 ≤ max y ε ^ (p - 1) := (Real.rpow_pos_of_pos hM _).le
  rcases le_total y (2 * η) with hy | hy
  · have hmax : max y ε ≤ 2 * η := max_le hy (by linarith)
    have hpow : (2 * η) ^ (p - 1) ≤ max y ε ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos hM hmax (by linarith)
    have h2 : 0 ≤ (2 * η) ^ (p - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
    have hcb : cut η y * regDrift c ε y ≤ regDrift c ε y := by
      have := cut_le_one η y
      nlinarith [cut_nonneg η y]
    calc p / 4 * (2 * η) ^ (p - 1) * (cut η y * regDrift c ε y)
        ≤ p / 4 * (2 * η) ^ (p - 1) * regDrift c ε y :=
          mul_le_mul_of_nonneg_left hcb (by positivity)
      _ ≤ p / 4 * max y ε ^ (p - 1) * regDrift c ε y := by
          apply mul_le_mul_of_nonneg_right _ hb
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := hgen
  · rw [cut_eq_zero hη hy, zero_mul, mul_zero]
    have h0 : 0 ≤ p / 4 * max y ε ^ (p - 1) * regDrift c ε y := by positivity
    exact h0.trans hgen

/-- **Dynkin step.** `(p/4)(2η)^{p-1} E J_η ≤ 1 + E U_t⁺` for `ε ≤ η`. -/
theorem dynkin_regJ_le (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x) {p η : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpc : 1 - p ≤ c / 8) (hε : 0 < ε) (hεη : ε ≤ η) (t : ℝ≥0) :
    p / 4 * (2 * η) ^ (p - 1) * ∫ ω, regJ c ε x η B t ω ∂P
      ≤ 1 + ∫ ω, max (regProc c ε x B t ω) 0 ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := QuantumZipper.Dynkin.dynkin_additive hB hBc (natFilt hBm) (natFilt_adapted hBm)
    (natFilt_le_past hBm) (lipschitzWith_regDrift hc.le hε) (norm_regDrift_le hc.le hε)
    (regProc_integralEq (x := x) hBc hc.le hε) (contDiff_testFun (p := p) hε)
    (norm_derivs_testFun_le hp0 hp1 hε)
  set M := fun (t : ℝ≥0) ω => testFun p ε (regProc c ε x B t ω) - testFun p ε x
    - ∫ r in (0 : ℝ)..t, QuantumZipper.dynkinGen (regDrift c ε) (1 : ℝ) (testFun p ε)
        (regProc c ε x B r.toNNReal ω) with hMdef
  -- `E M_t = 0`
  have hE : ∫ ω, M t ω ∂P = 0 := by
    have h := hM.setIntegral_eq (by simp : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [← h]
    have h0 : M 0 =ᵐ[P] 0 := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      have hU0 : regProc c ε x B 0 ω = x := by
        rw [regProc_eq_add_regA hBc hc.le hε ω 0, regA]
        simp [hω]
      simp [hMdef, hU0]
    rw [integral_congr_ae h0]
    simp
  -- pointwise bound
  set k := p / 4 * (2 * η) ^ (p - 1) with hk
  have hk0 : 0 ≤ k := by
    have : 0 < 2 * η := by linarith [hε.trans_le hεη]
    positivity
  have hgc : ∀ ω, Continuous fun r : ℝ => QuantumZipper.dynkinGen (regDrift c ε) (1 : ℝ)
      (testFun p ε) (regProc c ε x B r.toNNReal ω) := fun ω =>
    (QuantumZipper.Dynkin.continuous_dynkinGen (contDiff_testFun hε) (continuous_regDrift hc.le hε)
      1).comp ((continuous_regProc hBc hc.le hε ω).comp continuous_real_toNNReal)
  have hpt : ∀ ω, k * regJ c ε x η B t ω ≤ 1 + max (regProc c ε x B t ω) 0 - M t ω := by
    intro ω
    have hI : k * regJ c ε x η B t ω ≤ ∫ r in (0 : ℝ)..t, QuantumZipper.dynkinGen (regDrift c ε)
        (1 : ℝ) (testFun p ε) (regProc c ε x B r.toNNReal ω) := by
      rw [regJ, ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on t.coe_nonneg
        ((continuous_const.mul (continuous_cut_regDrift_regProc hBc hc.le hε η ω)).intervalIntegrable
          0 t) ((hgc ω).intervalIntegrable 0 t)
        fun r _ => generator_ge_cut hp0 hp1 hc hpc hε hεη _
    have hF1 : testFun p ε (regProc c ε x B t ω) ≤ 1 + max (regProc c ε x B t ω) 0 :=
      (testFun_le hp0 hp1 hε _).trans (rpow_le_one_add (le_max_right _ _) hp0.le hp1)
    have hF0 : 0 ≤ testFun p ε x := testFun_nonneg hp0 hε hx
    simp only [hMdef]
    linarith
  have hint_l : Integrable (fun ω => k * regJ c ε x η B t ω) P :=
    (integrable_regJ hBm hBc hc.le hε η t).const_mul k
  have hint_r : Integrable (fun ω => 1 + max (regProc c ε x B t ω) 0 - M t ω) P :=
    ((integrable_const (1 : ℝ)).add (integrable_max_regProc hB hBm hBc hc.le hε t)).sub
      (hM.integrable t)
  calc k * ∫ ω, regJ c ε x η B t ω ∂P = ∫ ω, k * regJ c ε x η B t ω ∂P :=
        (integral_const_mul k _).symm
    _ ≤ ∫ ω, (1 + max (regProc c ε x B t ω) 0 - M t ω) ∂P := integral_mono hint_l hint_r hpt
    _ = 1 + ∫ ω, max (regProc c ε x B t ω) 0 ∂P := by
        have hA : Integrable (fun ω => 1 + max (regProc c ε x B t ω) 0) P :=
          (integrable_const (1 : ℝ)).add (integrable_max_regProc hB hBm hBc hc.le hε t)
        have h1 : ∫ ω, (1 + max (regProc c ε x B t ω) 0 - M t ω) ∂P
            = ∫ ω, (1 + max (regProc c ε x B t ω) 0) ∂P - ∫ ω, M t ω ∂P :=
          integral_sub hA (hM.integrable t)
        have h2 : ∫ ω, (1 + max (regProc c ε x B t ω) 0) ∂P
            = ∫ ω, (1 : ℝ) ∂P + ∫ ω, max (regProc c ε x B t ω) 0 ∂P :=
          integral_add (integrable_const (1 : ℝ)) (integrable_max_regProc hB hBm hBc hc.le hε t)
        rw [h1, h2, hE, sub_zero]
        simp

/-! ### The bootstrap -/

/-- The exponent `p = 1 - min c 1 / 8` of the test function. -/
def besselExp (c : ℝ) : ℝ := 1 - min c 1 / 8

theorem besselExp_pos (c : ℝ) : 0 < besselExp c := by
  have := min_le_right c 1; unfold besselExp; linarith

theorem besselExp_le_one (hc : 0 < c) : besselExp c ≤ 1 := by
  have : 0 ≤ min c 1 := le_min hc.le zero_le_one
  unfold besselExp; linarith

theorem besselExp_lt_one (hc : 0 < c) : besselExp c < 1 := by
  have : 0 < min c 1 := lt_min hc zero_lt_one
  unfold besselExp; linarith

theorem one_sub_besselExp_le (c : ℝ) : 1 - besselExp c ≤ c / 8 := by
  have := min_le_left c 1; unfold besselExp; linarith

/-- The level `η₀ = (p/8)^{1/(1-p)} / 2`, at which `(p/4)(2η₀)^{p-1} = 2`. -/
def besselLevel (c : ℝ) : ℝ := (besselExp c / 8) ^ (1 / (1 - besselExp c)) / 2

theorem besselLevel_pos (c : ℝ) : 0 < besselLevel c := by
  have := besselExp_pos c
  unfold besselLevel; positivity

theorem coeff_besselLevel (hc : 0 < c) :
    besselExp c / 4 * (2 * besselLevel c) ^ (besselExp c - 1) = 2 := by
  have hp := besselExp_pos c
  have hp1 := besselExp_lt_one hc
  have h1p : 1 - besselExp c ≠ 0 := by linarith
  have h2 : 2 * besselLevel c = (besselExp c / 8) ^ (1 / (1 - besselExp c)) := by
    unfold besselLevel; ring
  rw [h2, ← Real.rpow_mul (by positivity)]
  have : 1 / (1 - besselExp c) * (besselExp c - 1) = -1 := by field_simp; ring
  rw [this, Real.rpow_neg_one]
  field_simp
  norm_num

/-- `E U_t⁺ ≤ E |x + B_t| + E A_t`. -/
theorem integral_max_regProc_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) (t : ℝ≥0) :
    ∫ ω, max (regProc c ε x B t ω) 0 ∂P
      ≤ ∫ ω, |x + B t ω| ∂P + ∫ ω, regA c ε x B t ω ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← integral_add (integrable_abs_add_eval hB x t) (integrable_regA (P := P) hBm hBc hc hε t)]
  exact integral_mono (integrable_max_regProc hB hBm hBc hc hε t)
    ((integrable_abs_add_eval hB x t).add (integrable_regA (P := P) hBm hBc hc hε t))
    fun ω => max_regProc_le hBc hc hε t ω

/-- `E A_t ≤ E J_η + c t / η`. -/
theorem integral_regA_le_regJ (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 ≤ c) (hε : 0 < ε) {η : ℝ} (hεη : ε ≤ η) (t : ℝ≥0) :
    ∫ ω, regA c ε x B t ω ∂P ≤ ∫ ω, regJ c ε x η B t ω ∂P + c / η * t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := integral_mono (integrable_regA (P := P) (x := x) hBm hBc hc hε t)
    ((integrable_regJ (P := P) hBm hBc hc hε η t).add (integrable_const (c / η * t)))
    fun ω => regA_le_regJ_add hBc hc hε hεη t ω
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_regJ (P := P) hBm hBc hc hε η t) (integrable_const _)] at h
  simpa using h

/-- **Uniform drift bound.** For `ε ≤ η₀`, `E ∫₀ᵗ c / max U_r ε dr ≤ 1 + E|x + B_t| + 2 c t / η₀`. -/
theorem integral_regA_le (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x) (hε : 0 < ε)
    (hε0 : ε ≤ besselLevel c) (t : ℝ≥0) :
    ∫ ω, regA c ε x B t ω ∂P
      ≤ 1 + ∫ ω, |x + B t ω| ∂P + 2 * (c / besselLevel c * t) := by
  have hD := dynkin_regJ_le (P := P) hB hBc hBm hc hx (besselExp_pos c) (besselExp_le_one hc)
    (one_sub_besselExp_le c) hε hε0 t
  rw [coeff_besselLevel hc] at hD
  have hM := integral_max_regProc_le (x := x) hB hBm hBc hc.le hε t
  have hA := integral_regA_le_regJ (x := x) hB hBm hBc hc.le hε hε0 t
  linarith

/-- **Occupation estimate.** For `ε ≤ η` and `ε ≤ η₀`,
`E J_η ≤ (4/p) (2η)^{1-p} (2 + 2 E|x + B_t| + 2 c t / η₀)`. -/
theorem integral_regJ_le (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ r, Measurable (B r)) (hc : 0 < c) (hx : 0 ≤ x) (hε : 0 < ε) {η : ℝ}
    (hεη : ε ≤ η) (hε0 : ε ≤ besselLevel c) (t : ℝ≥0) :
    ∫ ω, regJ c ε x η B t ω ∂P
      ≤ 4 / besselExp c * (2 * η) ^ (1 - besselExp c)
          * (2 + 2 * ∫ ω, |x + B t ω| ∂P + 2 * (c / besselLevel c * t)) := by
  set p := besselExp c with hpdef
  have hp := besselExp_pos c
  have hη : 0 < 2 * η := by linarith [hε.trans_le hεη]
  have hD := dynkin_regJ_le (P := P) hB hBc hBm hc hx hp (besselExp_le_one hc)
    (one_sub_besselExp_le c) hε hεη t
  have hM := integral_max_regProc_le (x := x) hB hBm hBc hc.le hε t
  have hA := integral_regA_le (P := P) hB hBc hBm hc hx hε hε0 t
  have hβ : 0 ≤ ∫ ω, |x + B t ω| ∂P := integral_nonneg fun _ => abs_nonneg _
  set R := 2 + 2 * ∫ ω, |x + B t ω| ∂P + 2 * (c / besselLevel c * t)
  have hkR : p / 4 * (2 * η) ^ (p - 1) * ∫ ω, regJ c ε x η B t ω ∂P ≤ R := by linarith
  have hpow : (2 * η) ^ (p - 1) * (2 * η) ^ (1 - p) = 1 := by
    rw [← Real.rpow_add hη]; norm_num
  have hpos : 0 < (2 * η) ^ (1 - p) := Real.rpow_pos_of_pos hη _
  have hJ : 0 ≤ ∫ ω, regJ c ε x η B t ω ∂P :=
    integral_nonneg fun ω => regJ_nonneg (x := x) (B := B) hc.le hε η t ω
  have h1 : 4 / p * (2 * η) ^ (1 - p) * (p / 4 * (2 * η) ^ (p - 1)) = 1 := by
    have hp0 : p ≠ 0 := hp.ne'
    have h4 : 4 / p * (p / 4) = 1 := by field_simp
    calc 4 / p * (2 * η) ^ (1 - p) * (p / 4 * (2 * η) ^ (p - 1))
        = (4 / p * (p / 4)) * ((2 * η) ^ (p - 1) * (2 * η) ^ (1 - p)) := by ring
      _ = 1 := by rw [h4, hpow, one_mul]
  calc ∫ ω, regJ c ε x η B t ω ∂P
      = 4 / p * (2 * η) ^ (1 - p) * (p / 4 * (2 * η) ^ (p - 1) * ∫ ω, regJ c ε x η B t ω ∂P) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ 4 / p * (2 * η) ^ (1 - p) * R := mul_le_mul_of_nonneg_left hkR (by positivity)

end Bessel

end InteractingSLE
