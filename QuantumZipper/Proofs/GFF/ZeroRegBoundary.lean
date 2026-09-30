import QuantumZipper.Proofs.GFF.ZeroRegularization
import QuantumZipper.Proofs.GFF.FoldBound
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# RG-2 (REG-BDRY): regularization of the zero-boundary GFF at measures touching `ℝ`

Blueprint `THM11_BLUEPRINT.md` §7, node RG-2. Let `X` satisfy `IsZeroBoundaryGFFH X P` and let
`μ` be an admissible measure (`IsAdmissibleH`: finite, compact support in `Hbar`, bounded
singular log potential) with

* a bounded zero-boundary Green potential `∫⁻ G⁺(x,·) dμ ≤ U` on `ℍ`;
* a Frostman bound `μ(B(x,s)) ≤ M h^{-p} s^α` for `Im x ≥ h > 0`, `s ≤ h/2`;
* the log-log strip decay `μ{Im < exp(-exp t)} ≤ C t^{-(1+η)}` for `t ≥ 1`
  (i.e. `μ{Im < δ} ≤ C (log log 1/δ)^{-1-η}`).

Then (`evalReg_ae_eq_zeroGFF_bdry`) `evalReg (X ω) μ = X ω μ` almost surely.

Proof. Let `νk = μ.bind (foldedCircle · 2^{-k})`. Stochastic Fubini (RG-0) gives
`∫ avgReg (X ω) k dμ = X ω νk`. `X νk − X μ` is a centered Gaussian of variance
`𝓔_G(νk − μ)`, which RG-1 bounds, with `h = e^{-γk}/2`, `γ = α/(4(p+α))`, by
`v_k = A C (log γk)^{-(1+η)} + B' e^{-αk/4}`. Since `v_k log k → 0`, the Gaussian tails
`2 exp(−ε²/(2 v_k))` are eventually `≤ 2k^{-2}`, and Borel–Cantelli gives `X νk → X μ` a.s.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace QuantumZipper
namespace ZeroRegBdry

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Gaussian increments and tails -/

/-- The difference of two admissible coordinates of the zero-boundary GFF is a centered
Gaussian with variance `𝓔_G(a − b)`. -/
theorem zrb_map_sub_eq_gaussianReal (hX : IsZeroBoundaryGFFH X P) {a b : Measure ℂ}
    (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) :
    P.map (fun ω => X ω a - X ω b) =
      gaussianReal 0 (kernelCov2 greenH (a, b) (a, b)).toNNReal := by
  have := ZeroReg.isProbabilityMeasure_of_zeroGFF hX
  have hG : HasGaussianLaw (fun ω => X ω a - X ω b) P :=
    hX.gaussian.hasGaussianLaw_fun_sub (s := ⟨_, ha⟩) (t := ⟨_, hb⟩)
  have hm : AEMeasurable (fun ω => X ω a - X ω b) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hA := ZeroReg.zg_memLp hX ha
  have hB := ZeroReg.zg_memLp hX hb
  have hc : P[fun ω => X ω a - X ω b] = 0 := by
    show ∫ ω, (X ω a - X ω b) ∂P = 0
    rw [integral_sub (hA.integrable one_le_two) (hB.integrable one_le_two), hX.centered _ ha,
      hX.centered _ hb, sub_zero]
  have hcov : cov[fun ω => X ω a - X ω b, fun ω => X ω a - X ω b; P] =
      kernelCov2 greenH (a, b) (a, b) := by
    rw [covariance_fun_sub_fun_sub hA hB hA hB, hX.covariance_eq _ _ ha ha,
      hX.covariance_eq _ _ ha hb, hX.covariance_eq _ _ hb ha, hX.covariance_eq _ _ hb hb]
    rfl
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- Two-sided Gaussian tail: if `Y ∼ N(0, V)` and `V ≤ c`, then
`P(|Y| ≥ ε) ≤ 2 exp(−ε²/(2c))`. -/
theorem zrb_measureReal_abs_ge_le [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y)
    {V c : ℝ≥0} (hlaw : P.map Y = gaussianReal 0 V) (hVc : V ≤ c) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |Y ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hVc' : (V : ℝ) ≤ c := hVc
  have hg : HasSubgaussianMGF id c (gaussianReal 0 V) :=
    { integrable_exp_mul := fun t => by
        simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := V) t
      mgf_le := fun t => by
        rw [mgf_id_gaussianReal]
        simp only [zero_mul, zero_add]
        exact Real.exp_le_exp.2 (by gcongr) }
  have hS : HasSubgaussianMGF Y c P := by
    rw [← HasSubgaussianMGF.id_map_iff hY.aemeasurable, hlaw]; exact hg
  have h1 := hS.measure_ge_le hε
  have h2 := hS.neg.measure_ge_le hε
  have hsub : {ω | ε ≤ |Y ω|} ⊆ {ω | ε ≤ Y ω} ∪ {ω | ε ≤ (-Y) ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, Pi.neg_apply] at hω ⊢
    exact le_abs.1 hω
  calc P.real {ω | ε ≤ |Y ω|} ≤ P.real ({ω | ε ≤ Y ω} ∪ {ω | ε ≤ (-Y) ω}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ε ≤ Y ω} + P.real {ω | ε ≤ (-Y) ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by linarith

/-! ## Summability and Borel–Cantelli -/

/-- If `v_k > 0` eventually and `v_k log k → 0`, then `∑ exp(−ε²/(2 v_k)) < ∞` for `ε > 0`. -/
theorem zrb_summable_exp {v : ℕ → ℝ} (hpos : ∀ᶠ k in atTop, 0 < v k)
    (hlim : Tendsto (fun k : ℕ => v k * Real.log k) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Summable fun k => Real.exp (-ε ^ 2 / (2 * v k)) := by
  have h1 : ∀ᶠ k : ℕ in atTop, v k * Real.log k < ε ^ 2 / 4 :=
    hlim.eventually (gt_mem_nhds (by positivity))
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
    (Real.summable_nat_pow_inv.2 one_lt_two) ?_
  filter_upwards [h1, hpos, eventually_ge_atTop 1] with k hk hv hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have e : ((k : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log k)) := by
    rw [Real.exp_neg, show 2 * Real.log k = Real.log ((k : ℝ) ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  rw [e, Real.exp_le_exp, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  have : 2 * Real.log k * (2 * v k) = 4 * (v k * Real.log k) := by ring
  linarith

/-- Borel–Cantelli with Gaussian-type tails: if `P(|D_k| ≥ ε) ≤ 2 exp(−ε²/(2 v_k))` eventually,
for every `ε > 0`, with `v_k > 0` eventually and `v_k log k → 0`, then `D_k → 0` a.s. -/
theorem zrb_ae_tendsto_zero [IsFiniteMeasure P] {D : ℕ → Ω → ℝ} {v : ℕ → ℝ}
    (hpos : ∀ᶠ k in atTop, 0 < v k)
    (hlim : Tendsto (fun k : ℕ => v k * Real.log k) atTop (𝓝 0))
    (hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      P.real {ω | ε ≤ |D k ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * v k))) :
    ∀ᵐ ω ∂P, Tendsto (fun k => D k ω) atTop (𝓝 0) := by
  have hj : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ {ω | 1 / ((j : ℝ) + 1) ≤ |D k ω|} := by
    intro j
    have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    refine ae_eventually_notMem ?_
    have hsum : Summable fun k => P.real {ω | 1 / ((j : ℝ) + 1) ≤ |D k ω|} := by
      refine Summable.of_norm_bounded_eventually_nat
        ((zrb_summable_exp hpos hlim hε).mul_left 2) ?_
      filter_upwards [hb _ hε] with k hk
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact hk
    have e : ∀ k, P {ω | 1 / ((j : ℝ) + 1) ≤ |D k ω|} =
        ENNReal.ofReal (P.real {ω | 1 / ((j : ℝ) + 1) ≤ |D k ω|}) := fun k =>
      (ofReal_measureReal (measure_ne_top _ _)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_all_iff.2 hj] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j, hjε⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with k hk
  simp only [not_le] at hk
  rw [Real.dist_eq, sub_zero]
  exact hk.trans hjε

/-- The rate: `(a (log γk)^{-(1+η)} + b e^{-ck}) log k → 0`. -/
theorem zrb_tendsto_rate {a b γ η c : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hc : 0 < c) :
    Tendsto (fun k : ℕ =>
      (a * Real.log (γ * k) ^ (-(1 + η)) + b * Real.exp (-c * k)) * Real.log k)
      atTop (𝓝 0) := by
  have hu : Tendsto (fun k : ℕ => Real.log (γ * k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hγ)
  have h1 : Tendsto (fun k : ℕ => Real.log (γ * k) ^ (-η) -
      Real.log γ * Real.log (γ * k) ^ (-(1 + η))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hη).comp hu).sub
      (((tendsto_rpow_neg_atTop (by linarith : 0 < 1 + η)).comp hu).const_mul (Real.log γ))
    simpa using this
  have h1' : Tendsto (fun k : ℕ => Real.log (γ * k) ^ (-(1 + η)) * Real.log k) atTop
      (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [hu.eventually_gt_atTop 0, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hl : Real.log k = Real.log (γ * k) - Real.log γ := by
      rw [Real.log_mul hγ.ne' hk0.ne']; ring
    have e := Real.rpow_add_one hk.ne' (-(1 + η))
    rw [show -(1 + η) + 1 = -η by ring] at e
    rw [hl, e]; ring
  have h2 : Tendsto (fun k : ℕ => Real.exp (-c * k) * Real.log k) atTop (𝓝 0) := by
    have h3 : Tendsto (fun k : ℕ => (c * k) ^ 1 * Real.exp (-(c * k))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    have h4 : Tendsto (fun k : ℕ => c⁻¹ * ((c * k) ^ 1 * Real.exp (-(c * k)))) atTop
        (𝓝 0) := by simpa using h3.const_mul c⁻¹
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h4 ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with k hk1
      exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg (by exact_mod_cast hk1))
    · filter_upwards [eventually_ge_atTop 1] with k hk1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hlk : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
      have e : c⁻¹ * ((c * k) ^ 1 * Real.exp (-(c * k))) = Real.exp (-c * k) * k := by
        rw [neg_mul, pow_one]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hlk (Real.exp_pos _).le
  have h5 := (h1'.const_mul a).add (h2.const_mul b)
  rw [mul_zero, mul_zero, add_zero] at h5
  exact h5.congr fun k => by ring

/-! ## The energy bound along the dyadic scales -/

/-- A strip decay bound forces `μ{Im ≤ 0} = 0`. -/
theorem zrb_measure_im_nonpos {μ : Measure ℂ} {C η : ℝ} (hη : 0 < η)
    (hS : ∀ t : ℝ, 1 ≤ t →
      μ {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + η)))) :
    μ {z | z.im ≤ 0} = 0 := by
  have ht : Tendsto (fun t : ℝ => ENNReal.ofReal (C * t ^ (-(1 + η)))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 + η)).const_mul C)
    simpa using this
  refine nonpos_iff_eq_zero.1 (ge_of_tendsto ht ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht1
  refine (measure_mono fun z hz => ?_).trans (hS t ht1)
  exact (show z.im ≤ 0 from hz).trans_lt (Real.exp_pos _)

/-- **RG-1 along the dyadic scales.** With `γ = α/(4(p+α))`, for `k ≥ 8` and `γk ≥ 3`,
`𝓔_G(νk − μ) ≤ A·C (log γk)^{-(1+η)} + B e^{-αk/4}`, where `A = 2U + 8μ(ℂ)` and
`B = (1/α + 4·2^α) M 2^p μ(ℂ)`. -/
theorem zrb_energy_le {μ : Measure ℂ} [IsFiniteMeasure μ] {U : ℝ≥0}
    (hH : μ {z | z.im ≤ 0} = 0)
    (hU : ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂μ ≤ U)
    {M p α : ℝ} (hM : 0 ≤ M) (hp : 0 ≤ p) (hα : 0 < α)
    (hF : ∀ h' : ℝ, 0 < h' → ∀ x : ℂ, h' ≤ x.im → ∀ s : ℝ, 0 < s → s ≤ h' / 2 →
      μ (Metric.ball x s) ≤ ENNReal.ofReal (M * h' ^ (-p) * s ^ α))
    {C η : ℝ} (hC : 0 ≤ C)
    (hS : ∀ t : ℝ, 1 ≤ t →
      μ {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + η))))
    {k : ℕ} (hk8 : 8 ≤ k) (hk3 : 3 ≤ α / (4 * (p + α)) * k) :
    kernelCov2 greenH (μ.bind fun w => foldedCircle w (radius k), μ)
        (μ.bind fun w => foldedCircle w (radius k), μ) ≤
      (2 * (U : ℝ) + 8 * (μ univ).toReal) *
          (C * Real.log (α / (4 * (p + α)) * k) ^ (-(1 + η))) +
        (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) * (μ univ).toReal *
          Real.exp (-(α / 4) * k) := by
  set γ := α / (4 * (p + α)) with hγ_def
  have hpa : 0 < p + α := by linarith
  have hγ : 0 < γ := by positivity
  have hγ4 : γ ≤ 1 / 4 := by
    rw [hγ_def, div_le_iff₀ (by positivity)]; linarith
  have hγp : γ * p ≤ α / 4 := by
    rw [hγ_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hk0 : (0 : ℝ) ≤ k := by linarith
  set h : ℝ := Real.exp (-(γ * k + Real.log 2)) with hh_def
  have hr : 0 < radius k := radius_pos k
  have hrad : radius k = Real.exp (-(k * Real.log 2)) := by
    rw [radius, ← Real.exp_log (by norm_num : (0 : ℝ) < 2⁻¹), ← Real.exp_nat_mul,
      Real.log_inv]
    congr 1; ring
  have h4r : 4 * radius k ≤ h := by
    have e4 : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
      rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
        Real.exp_log (by norm_num)]
    rw [hrad, hh_def, e4, ← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right hγ4 hk0
    have := mul_le_mul_of_nonneg_left hl2.le hk0
    linarith
  have hrg := FoldBound.abs_energy_foldSmooth_le_blueprint hH hU hM hα hr h4r hF
  -- the strip term
  have hγk : 0 < γ * k := mul_pos hγ (by linarith)
  have e2 : 2 * h = Real.exp (-Real.exp (Real.log (γ * k))) := by
    rw [Real.exp_log hγk, hh_def, show -(γ * k + Real.log 2) = -(γ * k) - Real.log 2 by ring,
      Real.exp_sub, Real.exp_log two_pos]
    ring
  have hlog1 : 1 ≤ Real.log (γ * k) := by
    rw [Real.le_log_iff_exp_le hγk]
    linarith [Real.exp_one_lt_d9]
  have hstrip : (μ {z | z.im < 2 * h}).toReal ≤ C * Real.log (γ * k) ^ (-(1 + η)) := by
    rw [e2]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
      (hS _ hlog1)
  -- the Frostman term
  have key : h ^ (-p) * radius k ^ α ≤ Real.exp (p * Real.log 2) * Real.exp (-(α / 4) * k) := by
    rw [hh_def, hrad, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add,
      Real.exp_le_exp]
    have ha : γ * p * k ≤ α / 4 * k := mul_le_mul_of_nonneg_right hγp hk0
    have hb : α * k * (1 / 2) ≤ α * k * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hα.le hk0)
    nlinarith
  set m := (μ univ).toReal with hm_def
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hA : 0 ≤ 2 * (U : ℝ) + 8 * m := by positivity
  have hcoef : 0 ≤ (1 / α + 4 * 2 ^ α) * M * m := by positivity
  have hfrost : (1 / α + 4 * 2 ^ α) * (M * h ^ (-p)) * radius k ^ α * m ≤
      (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) * m * Real.exp (-(α / 4) * k) := by
    have := mul_le_mul_of_nonneg_left key hcoef
    calc (1 / α + 4 * 2 ^ α) * (M * h ^ (-p)) * radius k ^ α * m
        = (1 / α + 4 * 2 ^ α) * M * m * (h ^ (-p) * radius k ^ α) := by ring
      _ ≤ (1 / α + 4 * 2 ^ α) * M * m *
          (Real.exp (p * Real.log 2) * Real.exp (-(α / 4) * k)) := this
      _ = _ := by ring
  have hs2 := mul_le_mul_of_nonneg_left hstrip hA
  linarith [le_abs_self (kernelCov2 greenH (μ.bind fun w => foldedCircle w (radius k), μ)
        (μ.bind fun w => foldedCircle w (radius k), μ))]

/-! ## RG-2 -/

end ZeroRegBdry
end QuantumZipper
