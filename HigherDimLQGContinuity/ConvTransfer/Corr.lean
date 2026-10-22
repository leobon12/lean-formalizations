import HigherDimLQGContinuity.ConvTransfer.Moments

/-!
# Correction factor in the real-cutoff white-noise model
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd WN)

/-- A single correction bound for the scalar sphere mean, top band, and
centered infrared field. The box contains the balls needed downstream. -/
def convModelGamma {d : ℕ} {Ω : Type*} (R : ℝ)
    (T I : Rd d → Ω → ℝ) (m : Ω → ℝ) (ω : Ω) : ℝ :=
  |m ω| + (⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) (2 * R + 12), |T z ω|) +
    (⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) (2 * R + 12), |I z ω|)

/-- The model correction is bounded pointwise on the ball needed for path
comparison. -/
theorem convModelGamma_bound {d : ℕ} {Ω : Type*}
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {T I : Rd d → Ω → ℝ} (hTc : ∀ ω, Continuous fun z => T z ω)
    (hIc : ∀ ω, Continuous fun z => I z ω) (m : Ω → ℝ)
    (ω : Ω) {z : Rd d} (hz : z ∈ Metric.closedBall (0 : Rd d) (2 * R + 12)) :
    |T z ω + I (r • z) ω - m ω| ≤ convModelGamma R T I m ω := by
  let S : ℝ := 2 * R + 12
  let B : Set (Rd d) := HigherDimLFPP.Osc.box 0 S
  have hS : 0 ≤ S := by dsimp [S]; linarith
  have hnorm : ‖z‖ ≤ S := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, S] using hz
  have hzB : z ∈ B := by
    intro i
    simpa only [B, HigherDimLFPP.Osc.box, PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm z i).trans hnorm
  have hrnorm : ‖r • z‖ ≤ S := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    nlinarith [mul_nonneg hr (sub_nonneg.2 hnorm)]
  have hrzB : r • z ∈ B := by
    intro i
    simpa only [B, HigherDimLFPP.Osc.box, PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm (r • z) i).trans hrnorm
  have : CompactSpace B := isCompact_iff_compactSpace.1
    (HigherDimLFPP.Osc.isCompact_box 0 S)
  have hbT : BddAbove (range fun x : B => |T x ω|) :=
    (isCompact_range (((hTc ω).comp continuous_subtype_val).abs)).bddAbove
  have hbI : BddAbove (range fun x : B => |I x ω|) :=
    (isCompact_range (((hIc ω).comp continuous_subtype_val).abs)).bddAbove
  have hT : |T z ω| ≤ ⨆ x : B, |T x ω| := le_ciSup hbT ⟨z, hzB⟩
  have hI : |I (r • z) ω| ≤ ⨆ x : B, |I x ω| := le_ciSup hbI ⟨r • z, hrzB⟩
  calc
    |T z ω + I (r • z) ω - m ω| ≤
        |m ω| + |T z ω| + |I (r • z) ω| := by
          have h1 : |T z ω + I (r • z) ω - m ω| ≤
              |T z ω + I (r • z) ω| + |m ω| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le (T z ω + I (r • z) ω) (-m ω))
          linarith [abs_add_le (T z ω) (I (r • z) ω)]
    _ ≤ |m ω| + (⨆ x : B, |T x ω|) + (⨆ x : B, |I x ω|) := by linarith
    _ = convModelGamma R T I m ω := rfl

/-- The correction supremum is measurable modulo null sets. -/
theorem convModelGamma_aemeasurable {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {r : ℝ} (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W₀ W' : WN d → Ω → ℝ}
    (hW₀ : HigherDimLFPP.IsWhiteNoise P W₀)
    (hW' : HigherDimLFPP.IsWhiteNoise P W')
    {T I : Rd d → Ω → ℝ}
    (hT : HigherDimLFPP.IsBandVersion P W' κ 1 (1 / r) T)
    (hIc : ∀ ω, Continuous fun x => I x ω)
    (hIeq : ∀ x, I x =ᵐ[P] W₀ (HigherDimLFPP.bandVecM κ (Ioi 1)
      (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d)))
    (m : Ω → ℝ) (hmm : Measurable m)
    {R : ℝ} (hR : 1 ≤ R) :
    AEMeasurable (convModelGamma R T I m) P := by
  let S : ℝ := 2 * R + 12
  obtain ⟨L, hL, htailT⟩ := convEnv_topBand_box_tail hd hκ
  have hTi := (htailT hr hr1 hW' hT (by dsimp [S]; linarith : 0 ≤ S)).1
  obtain ⟨L', C', hL', hC', htailI⟩ := convEnv_infrared_box_tail hd hκ
  have hIi := (htailI hW₀ hIc hIeq (by dsimp [S]; linarith : 1 ≤ S)).1
  exact ((continuous_abs.measurable.comp hmm).aemeasurable.add hTi.aemeasurable).add
    hIi.aemeasurable

/-- The three correction factors have a polynomial exponential moment. -/
theorem convModelGamma_poly_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {l : ℝ} (hl : 0 < l) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ {ε r : ℝ}, ε ∈ Ioo (0 : ℝ) 1 → 1 / 2 < r → r ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        {W₀ W' : WN d → Ω → ℝ},
        HigherDimLFPP.IsWhiteNoise P W₀ → HigherDimLFPP.IsWhiteNoise P W' →
      ∀ {T I : Rd d → Ω → ℝ},
        HigherDimLFPP.IsBandVersion P W' κ 1 (1 / r) T →
        (∀ ω, Continuous fun x => I x ω) →
        (∀ x, I x =ᵐ[P] W₀ (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d))) →
      ∀ (m : Ω → ℝ), Measurable m →
        (∀ ω, m ω = W₀ (HigherDimLFPP.bandVecM κ (Ioo ε 1)
          (HigherDimLQGMetric.unitSphereProb d) 0) ω) →
      ∀ {R : ℝ}, 1 ≤ R →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * convModelGamma R T I m ω)) ∂P ≤
        ENNReal.ofReal (C * (1 + R) ^ A) := by
  obtain ⟨Vₘ, hVₘ, hmom⟩ := convEnv_sphereBand_exp_moment hd hκ
  obtain ⟨Cₜ, Aₜ, hCₜ, hAₜ, hTmom⟩ :=
    convEnv_topBand_box_poly_moment hd hκ (show 0 < 4 * l by positivity)
  obtain ⟨Cᵢ, Aᵢ, hCᵢ, hAᵢ, hImom⟩ :=
    convEnv_infrared_box_poly_moment hd hκ (show 0 < 2 * l by positivity)
  let Rfactor : ℝ := 8
  let A : ℝ := Aₜ + Aᵢ
  let Cₘ : ℝ := 2 * Real.exp (Vₘ * (4 * l) ^ 2 / 2)
  let C : ℝ := Cₘ + Cₜ * Rfactor ^ Aₜ + Cᵢ * Rfactor ^ Aᵢ
  have hA : 0 ≤ A := add_nonneg hAₜ hAᵢ
  have hCₘ : 0 ≤ Cₘ := by dsimp [Cₘ]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, A, hC, hA, ?_⟩
  intro ε r hε hr hr1 Ω _ P W₀ W' hW₀ hW' T I hT hIc hIeq m hmm hm R hR
  letI : IsProbabilityMeasure P := hW₀.isProbabilityMeasure
  let S : ℝ := 2 * R + 12
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hS8 : 1 + S ≤ Rfactor * (1 + R) := by dsimp [S, Rfactor]; linarith
  let XT : Ω → ℝ := fun ω => ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) S, |T z ω|
  let XI : Ω → ℝ := fun ω => ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) S, |I z ω|
  obtain ⟨hTintegrable, _⟩ :=
    (convEnv_topBand_box_tail hd hκ).choose_spec.2 hr hr1 hW' hT (by linarith : 0 ≤ S)
  obtain ⟨Lᵢ, Cᵢ', _, _, hItail⟩ := convEnv_infrared_box_tail hd hκ
  have hIintegrable : Integrable XI P := (hItail hW₀ hIc hIeq hS).1
  have hsplit := convEnv_lintegral_exp_sum3_le
    (fun ω => |m ω|) XT XI (continuous_abs.measurable.comp hmm).aemeasurable
      hTintegrable.aemeasurable l
  have hₘ : ∫⁻ ω, ENNReal.ofReal (Real.exp (4 * l * |m ω|)) ∂P ≤
      ENNReal.ofReal Cₘ := by
    simpa only [Cₘ, hm] using hmom hε P W₀ hW₀ (4 * l)
  have hₜ : ∫⁻ ω, ENNReal.ofReal (Real.exp (4 * l * XT ω)) ∂P ≤
      ENNReal.ofReal (Cₜ * (1 + S) ^ Aₜ) :=
    hTmom hr hr1 hW' hT hS
  have hᵢ : ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * l * XI ω)) ∂P ≤
      ENNReal.ofReal (Cᵢ * (1 + S) ^ Aᵢ) :=
    hImom hW₀ hIc hIeq hS
  have hfirst : (1 + S) ^ Aₜ ≤ Rfactor ^ Aₜ * (1 + R) ^ A := by
    have h1 : (1 + S) ^ Aₜ ≤ (Rfactor * (1 + R)) ^ Aₜ :=
      Real.rpow_le_rpow (by linarith) hS8 hAₜ
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ Rfactor) (by linarith : 0 ≤ 1 + R)] at h1
    have h2 : (1 + R) ^ Aₜ ≤ (1 + R) ^ A :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [A]; linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _))
  have hsecond : (1 + S) ^ Aᵢ ≤ Rfactor ^ Aᵢ * (1 + R) ^ A := by
    have h1 : (1 + S) ^ Aᵢ ≤ (Rfactor * (1 + R)) ^ Aᵢ :=
      Real.rpow_le_rpow (by linarith) hS8 hAᵢ
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ Rfactor) (by linarith : 0 ≤ 1 + R)] at h1
    have h2 : (1 + R) ^ Aᵢ ≤ (1 + R) ^ A :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [A]; linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _))
  have hbase : 1 ≤ (1 + R) ^ A := Real.one_le_rpow (by linarith) hA
  have hreal : Cₘ + Cₜ * (1 + S) ^ Aₜ + Cᵢ * (1 + S) ^ Aᵢ ≤
      C * (1 + R) ^ A := by
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hfirst hCₜ.le,
      mul_le_mul_of_nonneg_left hsecond hCᵢ.le,
      mul_nonneg hCₘ (sub_nonneg.2 hbase)]
  have hsum : ENNReal.ofReal Cₘ + ENNReal.ofReal (Cₜ * (1 + S) ^ Aₜ) +
      ENNReal.ofReal (Cᵢ * (1 + S) ^ Aᵢ) =
        ENNReal.ofReal (Cₘ + Cₜ * (1 + S) ^ Aₜ + Cᵢ * (1 + S) ^ Aᵢ) := by
    rw [← ENNReal.ofReal_add hCₘ (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * convModelGamma R T I m ω)) ∂P ≤
        (∫⁻ ω, ENNReal.ofReal (Real.exp (4 * l * |m ω|)) ∂P) +
        (∫⁻ ω, ENNReal.ofReal (Real.exp (4 * l * XT ω)) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * l * XI ω)) ∂P := by
        simpa only [convModelGamma, S, XT, XI] using hsplit
    _ ≤ ENNReal.ofReal Cₘ + ENNReal.ofReal (Cₜ * (1 + S) ^ Aₜ) +
          ENNReal.ofReal (Cᵢ * (1 + S) ^ Aᵢ) := by
        exact add_le_add (add_le_add hₘ hₜ) hᵢ
    _ = ENNReal.ofReal (Cₘ + Cₜ * (1 + S) ^ Aₜ + Cᵢ * (1 + S) ^ Aᵢ) := hsum
    _ ≤ ENNReal.ofReal (C * (1 + R) ^ A) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGContinuity
