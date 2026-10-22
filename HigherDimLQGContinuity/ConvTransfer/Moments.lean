import HigherDimLQGContinuity.ConvTransfer.Sup
import LQGMetric.Papers.DDDF.FieldExpTail
import LQGMetric.Papers.LM.L3_4N1
import HigherDimLQGMetric.LfppTight.SphereMeanVariance

/-!
# Exponential moments from the box supremum tails
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace HigherDimLQGContinuity

/-- The absolute exponential moment of a centered Gaussian is controlled by
its variance, without assuming the chosen version is everywhere measurable. -/
theorem convEnv_lintegral_exp_abs_gauss
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (hY0 : ∫ ω, Y ω ∂P = 0) {V : ℝ} (hV : Var[Y; P] ≤ V) (l : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * |Y ω|)) ∂P ≤
      ENNReal.ofReal (2 * Real.exp (V * l ^ 2 / 2)) := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (l * Y ω))) P :=
    (Real.measurable_exp.comp_aemeasurable (hY.aemeasurable.const_mul l)).ennreal_ofReal
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * |Y ω|)) ∂P ≤
        ∫⁻ ω, (ENNReal.ofReal (Real.exp (l * Y ω)) +
          ENNReal.ofReal (Real.exp (-l * Y ω))) ∂P := by
        apply lintegral_mono
        intro ω
        change ENNReal.ofReal (Real.exp (l * |Y ω|)) ≤
          ENNReal.ofReal (Real.exp (l * Y ω)) +
            ENNReal.ofReal (Real.exp (-l * Y ω))
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        rcases abs_cases (Y ω) with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]
          linarith [Real.exp_pos (-l * Y ω)]
        · rw [h, mul_neg, ← neg_mul]
          linarith [Real.exp_pos (l * Y ω)]
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (l * Y ω)) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-l * Y ω)) ∂P :=
        lintegral_add_left' hm _
    _ = 2 * ENNReal.ofReal (Real.exp (Var[Y; P] * l ^ 2 / 2)) := by
      rw [LQGMetric.LM.lintegral_exp_gauss hY hY0 l,
        show (fun ω => ENNReal.ofReal (Real.exp (-l * Y ω))) =
          (fun ω => ENNReal.ofReal (Real.exp ((-l) * Y ω))) by funext ω; ring]
      rw [LQGMetric.LM.lintegral_exp_gauss hY hY0 (-l), neg_sq, two_mul]
    _ ≤ ENNReal.ofReal (2 * Real.exp (V * l ^ 2 / 2)) := by
      calc
        2 * ENNReal.ofReal (Real.exp (Var[Y; P] * l ^ 2 / 2)) =
          ENNReal.ofReal (2 * Real.exp (Var[Y; P] * l ^ 2 / 2)) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr)

/-- Uniform exponential moment for the scalar subtracted in the real-cutoff model. -/
theorem convEnv_sphereBand_exp_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : HigherDimLFPP.WN d → Ω → ℝ),
      HigherDimLFPP.IsWhiteNoise P W → ∀ l : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * |W (HigherDimLFPP.bandVecM κ
        (Ioo ε 1) (HigherDimLQGMetric.unitSphereProb d) 0) ω|)) ∂P ≤
        ENNReal.ofReal (2 * Real.exp (V * l ^ 2 / 2)) := by
  obtain ⟨V, hV0, hV⟩ := HigherDimLQGMetric.l6a_uniform_sphereBand_var hd hκ
  refine ⟨V, hV0, ?_⟩
  intro ε hε Ω _ P _ W hW l
  let v := HigherDimLFPP.bandVecM κ (Ioo ε 1)
    (HigherDimLQGMetric.unitSphereProb d) 0
  have hG : HasGaussianLaw (W v) P := (hW.hasLaw_single v).hasGaussianLaw
  have h0 : ∫ ω, W v ω ∂P = 0 := hW.integral_eq_zero v
  have hv : Var[W v; P] ≤ V := (hW.variance_eq v).le.trans (hV ε hε)
  exact convEnv_lintegral_exp_abs_gauss hG h0 hv l

/-- Uniform exponential moment of the convolution field's unit-sphere mean. -/
theorem convEnv_sphereMean_exp_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → HigherDimLQGMetric.DistRd d)
    (hh : HigherDimLQGMetric.IsNormalizedLGF h P) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ {ε : ℝ}, ε ∈ Ioo (0 : ℝ) 1 → ∀ l : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l *
        |HigherDimLQGMetric.l6a_convSphereMean κ ε (h ω)|)) ∂P ≤
          ENNReal.ofReal (2 * Real.exp (V * l ^ 2 / 2)) := by
  obtain ⟨V, hV0, hV⟩ := HigherDimLQGMetric.l6a_uniform_sphereMean_variance hd κ hκ P h hh
  refine ⟨V, hV0, ?_⟩
  intro ε hε l
  obtain ⟨hG, h0⟩ := HigherDimLQGMetric.l6a_hasGaussianLaw_sphereMean
    hd κ hκ P h hh hε.1
  exact convEnv_lintegral_exp_abs_gauss hG h0 (hV ε hε) l

/-- A Gaussian upper tail about `M` gives an exponential moment. -/
theorem convEnv_lintegral_exp_of_gaussian_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) (hXm : AEMeasurable X P)
    {M V l : ℝ} (hM : 0 ≤ M) (hV : 0 < V) (hl : 0 < l)
    (htail : ∀ u : ℝ, 0 ≤ u →
      P {ω | M + u ≤ X ω} ≤ ENNReal.ofReal (2 * exp (-u ^ 2 / (2 * V)))) :
    ∫⁻ ω, ENNReal.ofReal (exp (l * X ω)) ∂P ≤
      ENNReal.ofReal (exp (l * (M + 4 * l * V)) +
        2 * exp (2 * l * M) * exp (-l * (M + 4 * l * V))) := by
  let x₀ := M + 4 * l * V
  have hx₀ : 0 ≤ x₀ := by dsimp [x₀]; positivity
  have hB : 0 ≤ 2 * l * exp (2 * l * M) := by positivity
  have htb : ∀ t, x₀ < t →
      l * exp (l * t) * P.real {ω | t ≤ X ω} ≤
        (2 * l * exp (2 * l * M)) * exp (-l * t) := by
    intro t ht
    let u := t - M
    have hu : 0 ≤ u := by dsimp [u, x₀] at *; nlinarith
    have hu4 : 4 * l * V ≤ u := by dsimp [u, x₀] at *; linarith
    have htail' := htail u hu
    have hset : {ω | M + u ≤ X ω} = {ω | t ≤ X ω} := by
      ext ω
      change (M + u ≤ X ω) ↔ (t ≤ X ω)
      dsimp [u]
      ring
    rw [hset] at htail'
    have hprob : P.real {ω | t ≤ X ω} ≤ 2 * exp (-u ^ 2 / (2 * V)) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) htail'
    have hexp : exp (-u ^ 2 / (2 * V)) ≤ exp (-2 * l * u) := by
      apply exp_le_exp.mpr
      apply (div_le_iff₀ (by positivity : 0 < 2 * V)).2
      nlinarith [mul_nonneg hu (sub_nonneg.2 hu4)]
    calc
      l * exp (l * t) * P.real {ω | t ≤ X ω} ≤
          l * exp (l * t) * (2 * exp (-u ^ 2 / (2 * V))) := by gcongr
      _ ≤ l * exp (l * t) * (2 * exp (-2 * l * u)) := by gcongr
      _ = (2 * l * exp (2 * l * M)) * exp (-l * t) := by
        calc
          l * exp (l * t) * (2 * exp (-2 * l * u)) =
              2 * l * exp (l * t + -2 * l * u) := by rw [exp_add]; ring
          _ = 2 * l * exp (2 * l * M + -l * t) := by
            congr 1
            dsimp [u]
            ring
          _ = (2 * l * exp (2 * l * M)) * exp (-l * t) := by rw [exp_add]; ring
  convert LQGMetric.DDDF.lintegral_exp_le_of_tail hX0 hXm hl hx₀ hl hB htb using 1
  congr 1
  dsimp [x₀]
  field_simp

/-- Exponential moments for the centered infrared field, with explicit
radius-dependent Gaussian parameters. -/
theorem convEnv_infrared_box_exp_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ L C : ℝ, 0 < L ∧ 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : HigherDimLFPP.WN d → Ω → ℝ},
        HigherDimLFPP.IsWhiteNoise P W →
      ∀ {I : HigherDimLFPP.Rd d → Ω → ℝ},
        (∀ ω, Continuous fun x => I x ω) →
        (∀ x, I x =ᵐ[P] W (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d))) →
      ∀ {R : ℝ}, 1 ≤ R → ∀ {l : ℝ}, 0 < l →
      let V := C * (1 + Real.log (√(d : ℝ) * R))
      let M := HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R + 1))
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (⨆ z : HigherDimLFPP.Osc.box
        (0 : HigherDimLFPP.Rd d) R, |I z ω|))) ∂P ≤
        ENNReal.ofReal (Real.exp (l * (M + 4 * l * V)) +
          2 * Real.exp (2 * l * M) * Real.exp (-l * (M + 4 * l * V))) := by
  obtain ⟨L, C, hL, hC, hbound⟩ := convEnv_infrared_box_tail hd hκ
  refine ⟨L, C, hL, hC, ?_⟩
  intro Ω _ P W hW I hIc hIeq R hR l hl
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let B := HigherDimLFPP.Osc.box (0 : HigherDimLFPP.Rd d) R
  let X : Ω → ℝ := fun ω => ⨆ z : B, |I z ω|
  let V := C * (1 + Real.log (√(d : ℝ) * R))
  let M := HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R + 1))
  have hV : 0 < V := by
    have hdge : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hroot : 1 ≤ √(d : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hdge
    have hρ : 1 ≤ √(d : ℝ) * R := by nlinarith
    have := Real.log_nonneg hρ
    dsimp [V]
    positivity
  have hℓ : 0 ≤ (d : ℝ) * Real.log (2 * R + 1) := by
    apply mul_nonneg (Nat.cast_nonneg d)
    exact Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := by
    dsimp [M, HigherDimLFPP.SupB.supMean]
    have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
      (Real.sqrt_nonneg (d : ℝ))
    positivity
  obtain ⟨hXi, htail⟩ := hbound hW hIc hIeq hR
  have hX0 : ∀ ω, 0 ≤ X ω := by
    intro ω
    have : CompactSpace B := isCompact_iff_compactSpace.1
      (HigherDimLFPP.Osc.isCompact_box 0 R)
    have hzero : (0 : HigherDimLFPP.Rd d) ∈ B :=
      fun i => by simpa only [sub_self, abs_zero] using (show 0 ≤ R by linarith)
    have hbdd : BddAbove (range fun z : B => |I z ω|) :=
      (isCompact_range ((hIc ω).comp continuous_subtype_val |>.abs)).bddAbove
    exact (abs_nonneg (I 0 ω)).trans (le_ciSup hbdd ⟨0, hzero⟩)
  have hXm : AEMeasurable X P := hXi.aemeasurable
  simpa only [X, B, M, V] using
    convEnv_lintegral_exp_of_gaussian_tail hX0 hXm hM hV hl
      (fun u hu => htail hu)

/-- Uniform Gaussian box tails for the bounded-width top band in the model. -/
theorem convEnv_topBand_box_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {r : ℝ}, 1 / 2 < r → r ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : HigherDimLFPP.WN d → Ω → ℝ},
      HigherDimLFPP.IsWhiteNoise P W →
      ∀ {T : HigherDimLFPP.Rd d → Ω → ℝ},
        HigherDimLFPP.IsBandVersion P W κ 1 (1 / r) T →
      ∀ {R : ℝ}, 0 ≤ R →
      Integrable (fun ω => ⨆ z : HigherDimLFPP.Osc.box
        (0 : HigherDimLFPP.Rd d) R, |T z ω|) P ∧
      ∀ {u : ℝ}, 0 ≤ u →
        P {ω | HigherDimLFPP.SupB.supMean d L 1
          (d * Real.log (2 * R + 1)) + u ≤
            ⨆ z : HigherDimLFPP.Osc.box (0 : HigherDimLFPP.Rd d) R, |T z ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-u ^ 2 / 2)) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨L₀, hL₀, hLinc⟩ := HigherDimLFPP.exists_norm_bandVec_sub_sq_le hκ
  let L := L₀ + 1
  have hLp : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hLp, ?_⟩
  intro r hrhalf hr1 Ω _ P W hW T hT R hR
  have hr : 0 < r := by linarith
  have hbr : (1 : ℝ) ≤ 1 / r := by
    rw [le_div_iff₀ hr]
    linarith
  have hlog : Real.log ((1 / r) / 1) ≤ (1 : ℝ) := by
    have hupper : 1 / r ≤ 2 := by
      rw [div_le_iff₀ hr]
      linarith
    simpa only [div_one] using
      (Real.log_le_log (by positivity : (0 : ℝ) < 1 / r) hupper).trans
        (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)])
  have hinc : ∀ z w : HigherDimLFPP.Rd d,
      ‖HigherDimLFPP.bandVec κ 1 (1 / r) z -
        HigherDimLFPP.bandVec κ 1 (1 / r) w‖ ^ 2 ≤
          L * ‖z - w‖ ^ 2 / 1 ^ 2 := by
    intro z w
    exact (hLinc 1 one_pos (1 / r) z w).trans (by gcongr; dsimp [L]; linarith)
  obtain ⟨_, _, hsup, htail⟩ := HigherDimLFPP.SupB.bandSup_bounds
    hκ hW one_pos hbr hT hLp hinc one_pos hlog 0 hR le_rfl
  refine ⟨hsup, ?_⟩
  intro u hu
  simpa only [div_one, mul_one] using htail hu

/-- Elementary arithmetic bound for the grid expectation. -/
theorem convEnv_supMean_le_linear (d : ℕ) {L V ℓ : ℝ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hℓ : 0 ≤ ℓ) :
    HigherDimLFPP.SupB.supMean d L V ℓ ≤
      2 * (1 + ℓ) + V / 2 +
        (π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) +
        HigherDimLFPP.Osc.blockConst d L (√(d : ℝ)) := by
  let a : ℝ := √(1 + ℓ)
  let b : ℝ := √(V / 2)
  let c : ℝ := √(π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8)
  have ha2 : a ^ 2 = 1 + ℓ := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = V / 2 := Real.sq_sqrt (by linarith)
  have hc2 : c ^ 2 = π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 :=
    Real.sq_sqrt (by positivity)
  change 2 * a * b + HigherDimLFPP.Osc.blockConst d L (√(d : ℝ)) +
      2 * a * c ≤ _
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c)]

/-- The box grid logarithm grows at most linearly with `log R`. -/
theorem convEnv_log_grid_le {R : ℝ} (hR : 1 ≤ R) :
    Real.log (2 * R + 1) ≤ 2 * (1 + Real.log R) := by
  have hR0 : 0 < R := by linarith
  have harg : 0 < 2 * R + 1 := by linarith
  have hcmp : 2 * R + 1 ≤ 3 * R := by linarith
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog := Real.log_le_log harg hcmp
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hR0.ne'] at hlog
  linarith

/-- The infrared variance logarithm grows at most linearly with `log R`. -/
theorem convEnv_log_radius_le {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    Real.log (√(d : ℝ) * R) ≤ √(d : ℝ) * (1 + Real.log R) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : 1 ≤ √(d : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hd'
  have hroot0 : 0 < √(d : ℝ) := by linarith
  have hR0 : 0 < R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlogroot := Real.log_le_sub_one_of_pos hroot0
  rw [Real.log_mul hroot0.ne' hR0.ne']
  nlinarith [mul_nonneg (sub_nonneg.2 hroot) hlogR]

/-- The expected-supremum bound is logarithmic in the observation radius. -/
theorem convEnv_ir_supMean_le_log {d : ℕ} (hd : 1 ≤ d)
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) {R : ℝ} (hR : 1 ≤ R) :
    HigherDimLFPP.SupB.supMean d L
      (C * (1 + Real.log (√(d : ℝ) * R)))
      (d * Real.log (2 * R + 1)) ≤
        (4 + 4 * (d : ℝ) + C * (1 + √(d : ℝ)) +
          π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 +
          HigherDimLFPP.Osc.blockConst d L (√(d : ℝ))) *
          (1 + Real.log R) := by
  let t : ℝ := 1 + Real.log R
  let V : ℝ := C * (1 + Real.log (√(d : ℝ) * R))
  let ℓ : ℝ := d * Real.log (2 * R + 1)
  let D : ℝ := π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 +
    HigherDimLFPP.Osc.blockConst d L (√(d : ℝ))
  have ht : 1 ≤ t := by dsimp [t]; linarith [Real.log_nonneg hR]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hroot : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have hlograd : 0 ≤ Real.log (√(d : ℝ) * R) := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hroot1 : 1 ≤ √(d : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hd'
    apply Real.log_nonneg
    nlinarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hℓ : 0 ≤ ℓ := by
    dsimp [ℓ]
    exact mul_nonneg hd0 (Real.log_nonneg (by linarith))
  have hD : 0 ≤ D := by
    dsimp [D]
    have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L) hroot
    positivity
  have hℓb : ℓ ≤ 2 * (d : ℝ) * t := by
    have h := mul_le_mul_of_nonneg_left (convEnv_log_grid_le hR) hd0
    calc
      ℓ = (d : ℝ) * Real.log (2 * R + 1) := rfl
      _ ≤ (d : ℝ) * (2 * t) := h
      _ = 2 * (d : ℝ) * t := by ring
  have hVb : V ≤ C * (1 + √(d : ℝ)) * t := by
    have hrad := convEnv_log_radius_le hd hR
    have h1 : 1 + Real.log (√(d : ℝ) * R) ≤ (1 + √(d : ℝ)) * t := by
      dsimp [t]
      nlinarith [Real.log_nonneg hR]
    simpa only [V, mul_assoc] using mul_le_mul_of_nonneg_left h1 hC
  have hmean := convEnv_supMean_le_linear d hL hV hℓ
  change HigherDimLFPP.SupB.supMean d L V ℓ ≤ _
  dsimp [D] at hD
  dsimp [t, V, ℓ, D] at *
  nlinarith

/-- Turn linear-log bounds on Gaussian mean and variance into a polynomial
bound on the exponential-moment expression. -/
theorem convEnv_exp_poly_of_log_bounds {R M V l A B : ℝ}
    (hR : 1 ≤ R) (hM0 : 0 ≤ M) (hV0 : 0 ≤ V)
    (hl : 0 < l) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : M ≤ A * (1 + Real.log R))
    (hV : V ≤ B * (1 + Real.log R)) :
    ENNReal.ofReal (Real.exp (l * (M + 4 * l * V)) +
      2 * Real.exp (2 * l * M) * Real.exp (-l * (M + 4 * l * V))) ≤
        ENNReal.ofReal (3 * Real.exp (3 * l * A + 4 * l ^ 2 * B) *
          (1 + R) ^ (3 * l * A + 4 * l ^ 2 * B)) := by
  let t := 1 + Real.log R
  let K := 3 * l * A + 4 * l ^ 2 * B
  have ht : 1 ≤ t := by dsimp [t]; linarith [Real.log_nonneg hR]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM' : l * M ≤ l * A * t := by
    simpa only [t, mul_assoc] using mul_le_mul_of_nonneg_left hM hl.le
  have hV' : 4 * l ^ 2 * V ≤ 4 * l ^ 2 * B * t := by
    simpa only [t, mul_assoc] using mul_le_mul_of_nonneg_left hV
      (show 0 ≤ 4 * l ^ 2 by positivity)
  have hfirst : l * (M + 4 * l * V) ≤ K * t := by
    dsimp [K]
    nlinarith [mul_nonneg (mul_nonneg hl.le hA) (sub_nonneg.2 ht)]
  have hsecond : 2 * l * M ≤ K * t := by
    dsimp [K]
    nlinarith [mul_nonneg (mul_nonneg hl.le hA) (sub_nonneg.2 ht),
      mul_nonneg (sq_nonneg l) hB, mul_nonneg hK (sub_nonneg.2 ht)]
  have hneg : Real.exp (-l * (M + 4 * l * V)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hbound : Real.exp (l * (M + 4 * l * V)) +
      2 * Real.exp (2 * l * M) * Real.exp (-l * (M + 4 * l * V)) ≤
      3 * Real.exp (K * t) := by
    have h1 := Real.exp_le_exp.mpr hfirst
    have h2 := Real.exp_le_exp.mpr hsecond
    have hp : 0 ≤ 2 * Real.exp (2 * l * M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hneg hp]
  have hexp : Real.exp (K * t) = Real.exp K * R ^ K := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < R), ← Real.exp_add]
    dsimp [t]
    congr 1
    ring
  have hrpow : R ^ K ≤ (1 + R) ^ K :=
    Real.rpow_le_rpow (by linarith) (by linarith) hK
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (l * (M + 4 * l * V)) +
        2 * Real.exp (2 * l * M) * Real.exp (-l * (M + 4 * l * V)) ≤
      3 * Real.exp (K * t) := hbound
    _ = 3 * Real.exp K * R ^ K := by rw [hexp]; ring
    _ ≤ 3 * Real.exp K * (1 + R) ^ K := by gcongr
    _ = _ := rfl

/-- Every fixed exponential moment of the infrared box supremum grows at most
polynomially with the box radius. -/
theorem convEnv_infrared_box_poly_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {l : ℝ} (hl : 0 < l) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : HigherDimLFPP.WN d → Ω → ℝ},
        HigherDimLFPP.IsWhiteNoise P W →
      ∀ {I : HigherDimLFPP.Rd d → Ω → ℝ},
        (∀ ω, Continuous fun x => I x ω) →
        (∀ x, I x =ᵐ[P] W (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d))) →
      ∀ {R : ℝ}, 1 ≤ R →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (⨆ z : HigherDimLFPP.Osc.box
        (0 : HigherDimLFPP.Rd d) R, |I z ω|))) ∂P ≤
          ENNReal.ofReal (C * (1 + R) ^ A) := by
  obtain ⟨L, C₀, hL, hC₀, hExp⟩ :=
    convEnv_infrared_box_exp_moment hd hκ
  let A₀ := 4 + 4 * (d : ℝ) + C₀ * (1 + √(d : ℝ)) +
    π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 +
    HigherDimLFPP.Osc.blockConst d L (√(d : ℝ))
  let B := C₀ * (1 + √(d : ℝ))
  let A := 3 * l * A₀ + 4 * l ^ 2 * B
  let C := 3 * Real.exp A
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
      (Real.sqrt_nonneg (d : ℝ))
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, A, hC, hA, ?_⟩
  intro Ω _ P W hW I hIc hIeq R hR
  let V := C₀ * (1 + Real.log (√(d : ℝ) * R))
  let M := HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R + 1))
  have hV0 : 0 ≤ V := by
    dsimp [V]
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hroot : 1 ≤ √(d : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hd'
    have hρ : 1 ≤ √(d : ℝ) * R := by nlinarith
    have hlogρ : 0 ≤ Real.log (√(d : ℝ) * R) := Real.log_nonneg hρ
    positivity
  have hM0 : 0 ≤ M := by
    dsimp [M, HigherDimLFPP.SupB.supMean]
    have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
      (Real.sqrt_nonneg (d : ℝ))
    positivity
  have hMb : M ≤ A₀ * (1 + Real.log R) :=
    convEnv_ir_supMean_le_log (by omega : 1 ≤ d) hL.le hC₀.le hR
  have hVb : V ≤ B * (1 + Real.log R) := by
    have hr := convEnv_log_radius_le (by omega : 1 ≤ d) hR
    have ht : 1 ≤ 1 + Real.log R := by linarith [Real.log_nonneg hR]
    have hinner : 1 + Real.log (√(d : ℝ) * R) ≤
        (1 + √(d : ℝ)) * (1 + Real.log R) := by nlinarith
    simpa only [V, B, mul_assoc] using mul_le_mul_of_nonneg_left hinner hC₀.le
  have hraw := hExp hW hIc hIeq hR hl
  exact hraw.trans (by simpa only [A, C, A₀, B, M, V] using
    convEnv_exp_poly_of_log_bounds hR hM0 hV0 hl hA₀ hB hMb hVb)

/-- Every fixed exponential moment of the bounded-width top band is
polynomial in the observation radius, uniformly in the cutoff ratio. -/
theorem convEnv_topBand_box_poly_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : HigherDimLFPP.Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {l : ℝ} (hl : 0 < l) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ {r : ℝ}, 1 / 2 < r → r ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : HigherDimLFPP.WN d → Ω → ℝ},
        HigherDimLFPP.IsWhiteNoise P W →
      ∀ {T : HigherDimLFPP.Rd d → Ω → ℝ},
        HigherDimLFPP.IsBandVersion P W κ 1 (1 / r) T →
      ∀ {R : ℝ}, 1 ≤ R →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (⨆ z : HigherDimLFPP.Osc.box
          (0 : HigherDimLFPP.Rd d) R, |T z ω|))) ∂P ≤
            ENNReal.ofReal (C * (1 + R) ^ A) := by
  obtain ⟨L, hL, htail⟩ := convEnv_topBand_box_tail hd hκ
  let A₀ := 4 + 4 * (d : ℝ) +
    π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 +
    HigherDimLFPP.Osc.blockConst d L (√(d : ℝ))
  let A := 3 * l * A₀ + 4 * l ^ 2
  let C := 3 * Real.exp A
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
      (Real.sqrt_nonneg (d : ℝ))
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, A, hC, hA, ?_⟩
  intro r hr hr1 Ω _ P W hW T hT R hR
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let B := HigherDimLFPP.Osc.box (0 : HigherDimLFPP.Rd d) R
  let X : Ω → ℝ := fun ω => ⨆ z : B, |T z ω|
  let M := HigherDimLFPP.SupB.supMean d L 1 (d * Real.log (2 * R + 1))
  obtain ⟨hXi, htail'⟩ := htail hr hr1 hW hT (by linarith : 0 ≤ R)
  have hX0 : ∀ ω, 0 ≤ X ω := by
    intro ω
    have : CompactSpace B := isCompact_iff_compactSpace.1
      (HigherDimLFPP.Osc.isCompact_box 0 R)
    have hzero : (0 : HigherDimLFPP.Rd d) ∈ B :=
      fun i => by simpa only [sub_self, abs_zero] using (show 0 ≤ R by linarith)
    have hbdd : BddAbove (range fun z : B => |T z ω|) :=
      (isCompact_range (((hT.continuous ω).comp continuous_subtype_val).abs)).bddAbove
    exact (abs_nonneg (T 0 ω)).trans (le_ciSup hbdd ⟨0, hzero⟩)
  have hM0 : 0 ≤ M := by
    dsimp [M, HigherDimLFPP.SupB.supMean]
    have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
      (Real.sqrt_nonneg (d : ℝ))
    positivity
  have hMb : M ≤ A₀ * (1 + Real.log R) := by
    have hlog : 0 ≤ Real.log (2 * R + 1) := Real.log_nonneg (by linarith)
    have hℓ : 0 ≤ (d : ℝ) * Real.log (2 * R + 1) :=
      mul_nonneg (Nat.cast_nonneg d) hlog
    have hm := convEnv_supMean_le_linear d hL.le (by norm_num : (0 : ℝ) ≤ 1) hℓ
    have hgrid := mul_le_mul_of_nonneg_left (convEnv_log_grid_le hR)
      (Nat.cast_nonneg d)
    have ht : 1 ≤ 1 + Real.log R := by linarith [Real.log_nonneg hR]
    have hD0 : 0 ≤ π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 +
        HigherDimLFPP.Osc.blockConst d L (√(d : ℝ)) := by
      have hb := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
        (Real.sqrt_nonneg (d : ℝ))
      positivity
    dsimp [M, A₀]
    nlinarith [mul_nonneg hD0 (sub_nonneg.2 ht),
      mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.2 ht)]
  have hVb : (1 : ℝ) ≤ 1 * (1 + Real.log R) := by
    linarith [Real.log_nonneg hR]
  have hraw := convEnv_lintegral_exp_of_gaussian_tail hX0 hXi.aemeasurable
    hM0 (by norm_num : (0 : ℝ) < 1) hl
      (fun u hu => by simpa only [X, B, M, mul_one] using htail' hu)
  have h10 : (0 : ℝ) ≤ 1 := by norm_num
  have hpoly := convEnv_exp_poly_of_log_bounds hR hM0 h10 hl hA₀ h10 hMb hVb
  simp only [mul_one] at hpoly
  exact hraw.trans (by simpa only [A, C, A₀, X, B, M, mul_one] using hpoly)

/-- An elementary three-factor moment bound. The exponents `4,4,2` are
chosen to avoid any independence assumption. -/
theorem convEnv_lintegral_exp_sum3_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A B C : Ω → ℝ) (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (l : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (A ω + B ω + C ω))) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp (4 * l * A ω)) ∂P) +
      (∫⁻ ω, ENNReal.ofReal (Real.exp (4 * l * B ω)) ∂P) +
        ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * l * C ω)) ∂P := by
  have hpt (ω : Ω) : Real.exp (l * (A ω + B ω + C ω)) ≤
      Real.exp (4 * l * A ω) + Real.exp (4 * l * B ω) +
        Real.exp (2 * l * C ω) := by
    let a := Real.exp (l * A ω)
    let b := Real.exp (l * B ω)
    let c := Real.exp (l * C ω)
    have habc : Real.exp (l * (A ω + B ω + C ω)) = a * b * c := by
      dsimp [a, b, c]
      rw [show l * (A ω + B ω + C ω) = l * A ω + l * B ω + l * C ω by ring,
        Real.exp_add, Real.exp_add]
    have ha4 : a ^ 4 = Real.exp (4 * l * A ω) := by
      dsimp [a]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hb4 : b ^ 4 = Real.exp (4 * l * B ω) := by
      dsimp [b]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hc2 : c ^ 2 = Real.exp (2 * l * C ω) := by
      dsimp [c]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [habc, ← ha4, ← hb4, ← hc2]
    have h1 := sq_nonneg (a * b - c)
    have h2 := sq_nonneg (a ^ 2 - b ^ 2)
    have ha : 0 ≤ a := (Real.exp_pos _).le
    have hb : 0 ≤ b := (Real.exp_pos _).le
    have hc : 0 ≤ c := (Real.exp_pos _).le
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hmA : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (4 * l * A ω))) P :=
    (Real.measurable_exp.comp_aemeasurable (hA.const_mul (4 * l))).ennreal_ofReal
  have hmB : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (4 * l * B ω))) P :=
    (Real.measurable_exp.comp_aemeasurable (hB.const_mul (4 * l))).ennreal_ofReal
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (A ω + B ω + C ω))) ∂P ≤
        ∫⁻ ω, (ENNReal.ofReal (Real.exp (4 * l * A ω)) +
          ENNReal.ofReal (Real.exp (4 * l * B ω)) +
          ENNReal.ofReal (Real.exp (2 * l * C ω))) ∂P := by
        apply lintegral_mono
        intro ω
        change ENNReal.ofReal (Real.exp (l * (A ω + B ω + C ω))) ≤
          ENNReal.ofReal (Real.exp (4 * l * A ω)) +
          ENNReal.ofReal (Real.exp (4 * l * B ω)) +
          ENNReal.ofReal (Real.exp (2 * l * C ω))
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = _ := by
      let f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (4 * l * A ω))
      let g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (4 * l * B ω))
      let h : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (2 * l * C ω))
      have hf : AEMeasurable f P := hmA
      have hg : AEMeasurable g P := hmB
      change (∫⁻ ω, f ω + g ω + h ω ∂P) =
        (∫⁻ ω, f ω ∂P) + (∫⁻ ω, g ω ∂P) + ∫⁻ ω, h ω ∂P
      have hs1 : (∫⁻ ω, f ω + g ω + h ω ∂P) =
          (∫⁻ ω, f ω + g ω ∂P) + ∫⁻ ω, h ω ∂P := by
        simpa only [Pi.add_apply] using lintegral_add_left' (hf.add hg) h
      have hs2 : (∫⁻ ω, f ω + g ω ∂P) =
          (∫⁻ ω, f ω ∂P) + ∫⁻ ω, g ω ∂P := by
        simpa only [Pi.add_apply] using lintegral_add_left' hf g
      rw [hs1, hs2]

end HigherDimLQGContinuity
