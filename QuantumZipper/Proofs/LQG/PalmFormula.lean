import QuantumZipper.LQG.Measures
import QuantumZipper.Proofs.Probability.CameronMartin
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Blueprint D1: the Palm formula ("quantum typical points"), abstract form

See `blueprint/SECTION5_BLUEPRINT.md`, node D1. Setting: `Y = ofFun m + Z` with `Z` a centered
Gaussian field (`IsCenteredGaussianField`) and `m` continuous; `ν` a random measure on `ℝ`.

Main results:
* `palm_formula` (and `palm_formula_qBoundaryMeasure` for `ν = qBoundaryMeasure γ Y`):
  `E ∫_{[a,b]} φ((Y μ_j)_j, x) ν(dx) = ∫_{[a,b]} ρ(x) E φ(((Y + ofFun((γ/2)c(x,·))) μ_j)_j, x) dx`,
  `ρ(x) = exp(γ m(x)/2 + γ² c̃(x,x)/8)`, for bounded measurable `φ`.

Hypotheses (besides Gaussianity): `L¹` convergence of `bdryApprox γ Y k` to `ν` on `[a,b]`
(blueprint B3(a), in the integrated form `BdryL1Conv`), `E ν[a,b] < ∞`, a.s. identification of the
regularized average `avgReg Y k x` with the coordinate `Y(fcK x k)` (true for the fields of B3 by
M4), and the covariance asymptotics defining `c̃(x,x)` (`Var Z(fcK x k) + 2 log 2^{-k} → c̃(x,x)`,
boundedly on `[a,b]`, the content of B3(f)) and `c(x,·)`
(`Cov(Z μ_j, Z(fcK x k)) → ∫ c(x,·) dμ_j`).

Route: at level `k`, `bdryApprox` has density `2^{-kγ²/4} e^{γ Y(fcK x k)/2}`, and Cameron–Martin
(A9, `CameronMartin.integral_mul_tiltDensity`) gives the exact identity `palm_levelK` with shift
`(γ/2) Cov(·, Z(fcK x k))`. Letting `k → ∞` (`tendsto_lhs`, `tendsto_rhs`) gives the identity for
products `g(coords) h(x)` of bounded continuous functions (`palm_core`); two finite measures on
`(ℕ → ℝ) × ℝ` agreeing on such products are equal
(`Measure.ext_of_integral_mul_boundedContinuousFunction`), which gives all bounded measurable `φ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace Palm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The level-`k` folded (semi)circle at a real point `x`, radius `2^{-k}`. -/
abbrev fcK (x : ℝ) (k : ℕ) : Measure ℂ := foldedCircle (x : ℂ) (radius k)

/-! ## 1. Cameron–Martin for a single index -/

section Tilt
variable {X : Measure ℂ → Ω → ℝ}

lemma comb_single (a : Measure ℂ) (b : ℝ) (ω : Ω) :
    CameronMartin.comb X (Finsupp.single a b) ω = b * X a ω := by
  unfold CameronMartin.comb
  rw [Finset.sum_subset Finsupp.support_single_subset
    (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
  simp

lemma covShift_single (a : Measure ℂ) (b : ℝ) (j : Measure ℂ) :
    CameronMartin.covShift X P (Finsupp.single a b) j = b * CameronMartin.covK X P j a := by
  unfold CameronMartin.covShift
  rw [Finset.sum_subset Finsupp.support_single_subset
    (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
  simp

lemma covNorm_single (a : Measure ℂ) (b : ℝ) :
    CameronMartin.covNorm X P (Finsupp.single a b) = b * (b * CameronMartin.covK X P a a) := by
  unfold CameronMartin.covNorm
  rw [Finset.sum_subset Finsupp.support_single_subset
    (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
  simp [covShift_single]

end Tilt

/-! ## 2. Folded circles at real points -/

lemma norm_foldH_sub_ofReal (w : ℂ) (x : ℝ) : ‖foldH w - x‖ = ‖w - x‖ := by
  unfold foldH
  split_ifs
  · rfl
  · calc ‖(starRingEnd ℂ) w - x‖ = ‖(starRingEnd ℂ) (w - x)‖ := by
          rw [map_sub, Complex.conj_ofReal]
      _ = ‖w - x‖ := Complex.norm_conj _

lemma radius_le_one' (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma ae_fcK (x : ℝ) (k : ℕ) : ∀ᵐ z ∂fcK x k, ‖z - (x : ℂ)‖ ≤ radius k := by
  have hmeas : ∀ c : ℂ, MeasurableSet {z : ℂ | ‖z - c‖ ≤ radius k} := fun c =>
    measurableSet_le (by fun_prop) measurable_const
  show ∀ᵐ z ∂((circleUnif (x : ℂ) (radius k)).map foldH), ‖z - (x : ℂ)‖ ≤ radius k
  rw [ae_map_iff measurable_foldH.aemeasurable (hmeas _)]
  simp_rw [norm_foldH_sub_ofReal]
  unfold circleUnif
  refine Measure.ae_smul_measure ?_ _
  rw [ae_map_iff (measurable_circleMap _ _).aemeasurable (hmeas _)]
  refine ae_of_all _ fun θ => ?_
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos (radius_pos k)]

lemma exists_bound_fcK {m : ℂ → ℝ} (hm : Continuous m) (a b : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ k, ∀ x ∈ Icc a b, (∀ᵐ z ∂fcK x k, ‖m z‖ ≤ M) ∧ ‖m x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (|a| + |b| + 1)).exists_bound_of_continuousOn
    hm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun k x hx => ⟨?_, ?_⟩⟩
  · filter_upwards [ae_fcK x k] with z hz
    refine (hC z ?_).trans (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right]
    have hxa : |x| ≤ |a| + |b| := (abs_le_max_abs_abs hx.1 hx.2).trans
      (max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
    calc ‖z‖ ≤ ‖z - x‖ + ‖(x : ℂ)‖ := norm_le_norm_sub_add z x
      _ ≤ 1 + |x| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith [radius_le_one' k]
      _ ≤ |a| + |b| + 1 := by linarith
  · refine (hC x ?_).trans (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have := (abs_le_max_abs_abs hx.1 hx.2).trans
      (max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
    linarith

lemma integrable_fcK {m : ℂ → ℝ} (hm : Continuous m) (x : ℝ) (k : ℕ) :
    Integrable m (fcK x k) := by
  obtain ⟨M, -, hM⟩ := exists_bound_fcK hm x x
  exact Integrable.of_bound hm.aestronglyMeasurable M (hM k x ⟨le_rfl, le_rfl⟩).1

/-- The level-`k` mean `∫ m d(fcK x k)`. -/
def meanK (m : ℂ → ℝ) (x : ℝ) (k : ℕ) : ℝ := ∫ z, m z ∂(fcK x k)

lemma tendsto_meanK {m : ℂ → ℝ} (hm : Continuous m) (x : ℝ) :
    Tendsto (fun k => meanK m x k) atTop (𝓝 (m x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδm⟩ := Metric.continuousAt_iff.mp (hm.continuousAt (x := (x : ℂ))) (ε := ε / 2) (by positivity)
  have hr : Tendsto radius atTop (𝓝 0) := by
    unfold radius; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (hr.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨N, fun k hk => ?_⟩
  have hint := integrable_fcK hm x k
  have heq : meanK m x k - m x = ∫ z, (m z - m x) ∂(fcK x k) := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]; rfl
  rw [Real.dist_eq, heq]
  have hb : ‖∫ z, (m z - m x) ∂(fcK x k)‖ ≤ ε / 2 * (fcK x k).real univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [ae_fcK x k] with z hz
    have : dist z x < δ := by rw [dist_eq_norm]; exact lt_of_le_of_lt hz (hN k hk)
    have := hδm this
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]; exact this.le
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at hb
  linarith

/-! ## 3. The setting -/

/-- A centered Gaussian field: `(Z ω ν)_ν` is a centered Gaussian process with measurable
coordinates. -/
structure IsCenteredGaussianField (P : Measure Ω) (Z : Ω → FieldSample) : Prop where
  gauss : IsGaussianProcess (fun ν ω => Z ω ν) P
  meas : ∀ ν, Measurable fun ω => Z ω ν
  cent : ∀ ν, ∫ ω, Z ω ν ∂P = 0

/-- The countably many coordinates `j ↦ Y ω (μ j)` of `Y = ofFun m + Z`. -/
def coords (m : ℂ → ℝ) (Z : Ω → FieldSample) (μ : ℕ → Measure ℂ) (ω : Ω) : ℕ → ℝ :=
  fun j => (ofFun m + Z ω) (μ j)

/-- Level-`k` variance `Var Z(fcK x k)`. -/
def varK (Z : Ω → FieldSample) (P : Measure Ω) (x : ℝ) (k : ℕ) : ℝ :=
  Var[fun ω => Z ω (fcK x k); P]

/-- Level-`k` first-moment density `exp(γ m_k(x)/2 + γ²(Var_k(x) + 2 log 2^{-k})/8)`. -/
def rhoK (γ : ℝ) (m : ℂ → ℝ) (Z : Ω → FieldSample) (P : Measure Ω) (x : ℝ) (k : ℕ) : ℝ :=
  Real.exp (γ * meanK m x k / 2 + γ ^ 2 / 8 * (varK Z P x k + 2 * Real.log (radius k)))

/-- Level-`k` Cameron–Martin shift of the coordinates: `(γ/2) Cov(Z(μ j), Z(fcK x k))`. -/
def shiftK (γ : ℝ) (Z : Ω → FieldSample) (P : Measure Ω) (μ : ℕ → Measure ℂ) (x : ℝ) (k : ℕ) :
    ℕ → ℝ :=
  fun j => γ / 2 * cov[fun ω => Z ω (μ j), fun ω => Z ω (fcK x k); P]

/-- The density of `bdryApprox γ (ofFun m + Z ω) k` at `x`. -/
def dens (γ : ℝ) (m : ℂ → ℝ) (Z : Ω → FieldSample) (k : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg (ofFun m + Z ω) k (x : ℂ))

/-- The limiting shift `(γ/2) ∫ c(x,·) dμ_j`. -/
def shiftLim (γ : ℝ) (c : ℝ → ℂ → ℝ) (μ : ℕ → Measure ℂ) (x : ℝ) : ℕ → ℝ :=
  fun j => γ / 2 * ∫ z, c x z ∂(μ j)

/-- The first-moment density `ρ(x) = exp(γ m(x)/2 + γ² c̃(x,x)/8)`. -/
def rhoLim (γ : ℝ) (m : ℂ → ℝ) (ctil : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (γ * m x / 2 + γ ^ 2 * ctil x / 8)

variable {Z : Ω → FieldSample} {m : ℂ → ℝ} {μ : ℕ → Measure ℂ} {γ : ℝ}

lemma measurable_field (hZ : IsCenteredGaussianField P Z) :
    Measurable fun ω => ofFun m + Z ω :=
  measurable_pi_iff.mpr fun ν => (hZ.meas ν).const_add _

lemma measurable_coords (hZ : IsCenteredGaussianField P Z) : Measurable (coords m Z μ) :=
  measurable_pi_iff.mpr fun j => (hZ.meas (μ j)).const_add _

lemma measurable_dens (hZ : IsCenteredGaussianField P Z) (k : ℕ) :
    Measurable fun p : Ω × ℝ => dens γ m Z k p.1 p.2 := by
  unfold dens
  have h1 : Measurable fun p : Ω × ℝ => avgReg (ofFun m + Z p.1) k (p.2 : ℂ) :=
    (measurable_avgReg k).comp (((measurable_field hZ).comp measurable_fst).prodMk
      (Complex.measurable_ofReal.comp measurable_snd))
  exact measurable_const.mul ((h1.const_mul _).exp)

lemma dens_nonneg (k : ℕ) (ω : Ω) (x : ℝ) : 0 ≤ dens γ m Z k ω x :=
  mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le

/-- The Cameron–Martin index used at level `k`. -/
abbrev sig (γ : ℝ) (x : ℝ) (k : ℕ) : Measure ℂ →₀ ℝ := Finsupp.single (fcK x k) (γ / 2)

lemma dens_ae_eq (hZ : IsCenteredGaussianField P Z) {x : ℝ} {k : ℕ}
    (hreg : ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k)) :
    ∀ᵐ ω ∂P, dens γ m Z k ω x = rhoK γ m Z P x k *
      CameronMartin.tiltDensity (fun ν ω => Z ω ν) P (sig γ x k) ω := by
  filter_upwards [hreg] with ω hω
  unfold dens rhoK CameronMartin.tiltDensity varK
  rw [hω, comb_single, covNorm_single]
  simp only [CameronMartin.covK]
  rw [covariance_self (hZ.meas _).aemeasurable, Real.rpow_def_of_pos (radius_pos k),
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, ofFun, meanK]
  ring

lemma integral_mul_dens (hZ : IsCenteredGaussianField P Z) {x : ℝ} {k : ℕ}
    (hreg : ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (G : (ℕ → ℝ) → ℝ) (hG : Measurable G) :
    ∫ ω, G (coords m Z μ ω) * dens γ m Z k ω x ∂P =
      rhoK γ m Z P x k * ∫ ω, G (coords m Z μ ω + shiftK γ Z P μ x k) ∂P := by
  rw [integral_congr_ae ((dens_ae_eq hZ hreg).mono fun ω h => by
    rw [h, mul_left_comm])]
  rw [integral_const_mul]
  congr 1
  have hΦ : Measurable fun y : Measure ℂ → ℝ => G (fun j => ofFun m (μ j) + y (μ j)) :=
    hG.comp (measurable_pi_iff.mpr fun j => (measurable_pi_apply (μ j)).const_add _)
  have key := CameronMartin.integral_mul_tiltDensity (X := fun ν ω => Z ω ν) hZ.gauss hZ.meas
    hZ.cent (sig γ x k) _ hΦ
  have e1 : ∀ ω, coords m Z μ ω = fun j => ofFun m (μ j) + Z ω (μ j) := fun ω => rfl
  have e2 : ∀ ω, coords m Z μ ω + shiftK γ Z P μ x k = fun j => ofFun m (μ j) +
      (Z ω (μ j) + CameronMartin.covShift (fun ν ω => Z ω ν) P (sig γ x k) (μ j)) := by
    intro ω; funext j
    simp only [coords, shiftK, covShift_single, CameronMartin.covK, Pi.add_apply]
    ring
  simp_rw [e2, e1]
  exact key

lemma integrable_dens (hZ : IsCenteredGaussianField P Z) {x : ℝ} {k : ℕ}
    (hreg : ∀ᵐ ω ∂P, avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k)) :
    Integrable (fun ω => dens γ m Z k ω x) P ∧ ∫ ω, dens γ m Z k ω x ∂P = rhoK γ m Z P x k := by
  have := hZ.gauss.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · exact ((CameronMartin.tiltDensity_integral hZ.gauss hZ.meas hZ.cent (sig γ x k)).1.const_mul
      (rhoK γ m Z P x k)).congr ((dens_ae_eq hZ hreg).mono fun ω h => h.symm)
  · have := integral_mul_dens (γ := γ) (μ := fun _ => 0) hZ hreg (fun _ => 1) measurable_const
    simpa using this

/-! ## 4. Uniform bounds -/

lemma exists_bound_rho (hm : Continuous m) {a b Cv : ℝ} {ctil : ℝ → ℝ}
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x))) :
    ∃ B, 0 < B ∧ ∀ x ∈ Icc a b, (∀ k, rhoK γ m Z P x k ≤ B) ∧ rhoLim γ m ctil x ≤ B := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fcK hm a b
  refine ⟨Real.exp (|γ| * M / 2 + γ ^ 2 / 8 * Cv), Real.exp_pos _, fun x hx => ⟨fun k => ?_, ?_⟩⟩
  · have hmk : |meanK m x k| ≤ M := by
      have := norm_integral_le_of_norm_le_const (hM k x hx).1
      rwa [probReal_univ, mul_one] at this
    unfold rhoK
    refine Real.exp_le_exp.mpr (add_le_add ?_ ?_)
    · have : γ * meanK m x k ≤ |γ| * M :=
        (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hmk (abs_nonneg _))
      linarith
    · exact mul_le_mul_of_nonneg_left (hvarbd k x hx) (by positivity)
  · have hc : ctil x ≤ Cv := le_of_tendsto' (hvar x hx) fun k => hvarbd k x hx
    have hmx : |m x| ≤ M := by have := (hM 0 x hx).2; rwa [Real.norm_eq_abs] at this
    unfold rhoLim
    refine Real.exp_le_exp.mpr ?_
    have : γ * m x ≤ |γ| * M :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hmx (abs_nonneg _))
    have : γ ^ 2 * ctil x ≤ γ ^ 2 * Cv := mul_le_mul_of_nonneg_left hc (by positivity)
    linarith

/-! ## 5. The level-`k` Palm identity -/

lemma setIntegral_bdryApprox (y : FieldSample) (k : ℕ) {I : Set ℝ} (hI : MeasurableSet I)
    (f : ℝ → ℝ) :
    ∫ x in I, f x ∂(bdryApprox γ y k) =
      ∫ x in I, f x * (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k (x : ℂ))) := by
  have hm : Measurable (fun t : ℝ => avgReg y k (t : ℂ)) :=
    (measurable_avgReg k).comp (measurable_const.prodMk Complex.continuous_ofReal.measurable)
  have hg : Measurable (fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k (t : ℂ)))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hm.const_mul _).exp))
  unfold bdryApprox
  rw [restrict_withDensity hI,
    integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (radius_pos k).le _)
    (Real.exp_pos _).le)]
  ring

section LevelK

variable {a b : ℝ} {F : (ℕ → ℝ) → ℝ → ℝ} {CF : ℝ}

lemma integrable_prod_F_dens (hZ : IsCenteredGaussianField P Z) (hm : Continuous m) {Cv : ℝ}
    {ctil : ℝ → ℝ}
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x)))
    (hF : Measurable (Function.uncurry F)) (hFb : ∀ y x, |F y x| ≤ CF) (k : ℕ) :
    Integrable (Function.uncurry fun ω x => F (coords m Z μ ω) x * dens γ m Z k ω x)
      (P.prod (volume.restrict (Icc a b))) := by
  have := hZ.gauss.isProbabilityMeasure
  obtain ⟨B, -, hB⟩ := exists_bound_rho (γ := γ) hm hvarbd hvar
  have hmeas : Measurable (Function.uncurry fun ω x => F (coords m Z μ ω) x * dens γ m Z k ω x) :=
    (hF.comp (((measurable_coords hZ).comp measurable_fst).prodMk measurable_snd)).mul
      (measurable_dens hZ k)
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (integrable_dens (γ := γ) hZ (hreg k x hx)).1.bdd_mul
      ((hF.comp ((measurable_coords hZ).prodMk measurable_const)).aestronglyMeasurable)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFb _ _)
  · refine Integrable.of_bound ?_ (CF * B) ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left (μ := P)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      obtain ⟨hi, hv⟩ := integrable_dens (γ := γ) hZ (hreg k x hx)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ ω, ‖F (coords m Z μ ω) x * dens γ m Z k ω x‖ ∂P
          ≤ ∫ ω, CF * dens γ m Z k ω x ∂P := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (hi.const_mul CF) (ae_of_all _ fun ω => ?_)
            simp only
            rw [norm_mul, Real.norm_of_nonneg (dens_nonneg k ω x), Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hFb _ _) (dens_nonneg k ω x)
        _ = CF * rhoK γ m Z P x k := by rw [integral_const_mul, hv]
        _ ≤ CF * B := mul_le_mul_of_nonneg_left ((hB x hx).1 k)
            ((abs_nonneg _).trans (hFb 0 0))

/-- **Level-`k` Palm identity** (exact Cameron–Martin computation). -/
lemma palm_levelK (hZ : IsCenteredGaussianField P Z) (hm : Continuous m) {Cv : ℝ}
    {ctil : ℝ → ℝ}
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x)))
    (hF : Measurable (Function.uncurry F)) (hFb : ∀ y x, |F y x| ≤ CF) (k : ℕ) :
    ∫ ω, ∫ x in Icc a b, F (coords m Z μ ω) x ∂(bdryApprox γ (ofFun m + Z ω) k) ∂P =
      ∫ x in Icc a b, rhoK γ m Z P x k *
        ∫ ω, F (coords m Z μ ω + shiftK γ Z P μ x k) x ∂P := by
  have := hZ.gauss.isProbabilityMeasure
  simp_rw [setIntegral_bdryApprox _ k measurableSet_Icc]
  change ∫ ω, (∫ x in Icc a b, F (coords m Z μ ω) x * dens γ m Z k ω x) ∂P = _
  rw [integral_integral_swap (integrable_prod_F_dens hZ hm hreg hvarbd hvar hF hFb k)]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  exact integral_mul_dens hZ (hreg k x hx) (fun y => F y x)
    (hF.comp (measurable_id.prodMk measurable_const))

lemma measurable_F_dens (hZ : IsCenteredGaussianField P Z) (hF : Measurable (Function.uncurry F))
    (k : ℕ) :
    Measurable (Function.uncurry fun ω x => F (coords m Z μ ω) x * dens γ m Z k ω x) :=
  (hF.comp (((measurable_coords hZ).comp measurable_fst).prodMk measurable_snd)).mul
    (measurable_dens hZ k)

/-- The right-hand sides converge as `k → ∞`. -/
lemma tendsto_rhs (hZ : IsCenteredGaussianField P Z) (hm : Continuous m) {Cv : ℝ}
    {ctil : ℝ → ℝ} {c : ℝ → ℂ → ℝ}
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x)))
    (hcov : ∀ x ∈ Icc a b, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcK x k); P]) atTop
      (𝓝 (∫ z, c x z ∂(μ j))))
    (hF : Measurable (Function.uncurry F)) (hFb : ∀ y x, |F y x| ≤ CF)
    (hFc : ∀ x, Continuous fun y => F y x) :
    Tendsto (fun k => ∫ x in Icc a b, rhoK γ m Z P x k *
        ∫ ω, F (coords m Z μ ω + shiftK γ Z P μ x k) x ∂P) atTop
      (𝓝 (∫ x in Icc a b, rhoLim γ m ctil x *
        ∫ ω, F (coords m Z μ ω + shiftLim γ c μ x) x ∂P)) := by
  have := hZ.gauss.isProbabilityMeasure
  obtain ⟨B, hB0, hB⟩ := exists_bound_rho (γ := γ) hm hvarbd hvar
  replace hB0 := hB0.le
  have hIa : ∀ᵐ x ∂(volume.restrict (Icc a b)), x ∈ Icc a b := ae_restrict_mem measurableSet_Icc
  have hnorm : ∀ (x : ℝ) (v : ℕ → ℝ), ‖∫ ω, F (coords m Z μ ω + v) x ∂P‖ ≤ CF := by
    intro x v
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => F (coords m Z μ ω + v) x)
      (C := CF) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFb _ _)
    rwa [probReal_univ, mul_one] at this
  refine tendsto_integral_of_dominated_convergence (fun _ => B * CF) (fun k => ?_)
    (integrable_const _) (fun k => ?_) ?_
  · have hsm := (measurable_F_dens (m := m) (μ := μ) (γ := γ) hZ hF k).stronglyMeasurable.integral_prod_left
      (μ := P)
    refine hsm.aestronglyMeasurable.congr ?_
    filter_upwards [hIa] with x hx
    exact integral_mul_dens hZ (hreg k x hx) (fun y => F y x)
      (hF.comp (measurable_id.prodMk measurable_const))
  · filter_upwards [hIa] with x hx
    rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ rhoK γ m Z P x k from (Real.exp_pos _).le)]
    exact mul_le_mul ((hB x hx).1 k) (hnorm x _) (norm_nonneg _) hB0
  · filter_upwards [hIa] with x hx
    refine Tendsto.mul ?_ ?_
    · unfold rhoK rhoLim
      refine (Real.continuous_exp.tendsto _).comp ?_
      have h1 := ((tendsto_meanK hm x).const_mul γ).div_const 2
      have h2 := (hvar x hx).const_mul (γ ^ 2 / 8)
      convert h1.add h2 using 2
      ring
    · refine tendsto_integral_of_dominated_convergence (fun _ => CF) (fun k => ?_)
        (integrable_const _) (fun k => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
      · exact ((hF.comp (measurable_id.prodMk measurable_const)).comp
          ((measurable_coords hZ).add_const _)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hFb _ _
      · have hs : Tendsto (fun k => shiftK γ Z P μ x k) atTop (𝓝 (shiftLim γ c μ x)) :=
          tendsto_pi_nhds.mpr fun j => by
            simpa only [shiftK, shiftLim] using (hcov x hx j).const_mul (γ / 2)
        exact ((hFc x).tendsto _).comp (tendsto_const_nhds.add hs)

end LevelK

/-! ## 6. s-finiteness of pointwise finite kernels, and a measurable version of `ν` -/

lemma isSFiniteKernel_of_ne_top {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) (h : ∀ a, κ a univ ≠ ∞) : IsSFiniteKernel κ := by
  classical
  have hm : Measurable fun a => ⌊(κ a univ).toReal⌋₊ :=
    (κ.measurable_coe MeasurableSet.univ).ennreal_toReal.nat_floor
  have hE : ∀ n : ℕ, MeasurableSet {a | ⌊(κ a univ).toReal⌋₊ = n} := fun n =>
    hm (measurableSet_singleton n)
  refine ⟨⟨fun n => Kernel.piecewise (hE n) κ 0, fun n => ⟨⟨n + 1,
    ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top n, ENNReal.one_lt_top⟩, fun a => ?_⟩⟩, ?_⟩⟩
  · rw [Kernel.piecewise_apply]
    split_ifs with ha
    · have hlt : (κ a univ).toReal < n + 1 := by
        have := Nat.lt_floor_add_one (κ a univ).toReal
        rwa [show ⌊(κ a univ).toReal⌋₊ = n from ha] at this
      rw [← ENNReal.ofReal_toReal (h a)]
      calc ENNReal.ofReal (κ a univ).toReal ≤ ENNReal.ofReal ((n : ℝ) + 1) :=
            ENNReal.ofReal_le_ofReal hlt.le
        _ = n + 1 := by rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
    · simp
  · ext a s hs
    rw [Kernel.sum_apply' _ _ hs]
    have key : ∀ n : ℕ, (Kernel.piecewise (hE n) κ 0) a s =
        if n = ⌊(κ a univ).toReal⌋₊ then κ a s else 0 := by
      intro n
      rw [Kernel.piecewise_apply]
      by_cases hn : n = ⌊(κ a univ).toReal⌋₊
      · rw [ite_eq_left (show a ∈ {a | ⌊(κ a univ).toReal⌋₊ = n} from hn.symm), ite_eq_left hn]
      · rw [ite_eq_right (show a ∉ {a | ⌊(κ a univ).toReal⌋₊ = n} from fun h' => hn h'.symm),
          ite_eq_right hn, zero_apply, Measure.coe_zero, Pi.zero_apply]
    simp_rw [key]
    rw [tsum_ite_eq]

section RandomMeasure

variable {ν : Ω → Measure ℝ} {I : Set ℝ}

open Classical in
/-- A measurable version of `ν`, finite on `I` everywhere. -/
def nuMod (hν : AEMeasurable ν P) (I : Set ℝ) (ω : Ω) : Measure ℝ :=
  if hν.mk ν ω I < ∞ then hν.mk ν ω else 0

lemma measurable_nuMod (hν : AEMeasurable ν P) (hI : MeasurableSet I) :
    Measurable (nuMod hν I) := by
  classical
  unfold nuMod
  exact Measurable.ite (measurableSet_lt ((Measure.measurable_coe hI).comp hν.measurable_mk)
    measurable_const) hν.measurable_mk measurable_const

lemma nuMod_ae_eq (hν : AEMeasurable ν P) (hI : MeasurableSet I)
    (hfin : ∫⁻ ω, ν ω I ∂P < ∞) : ∀ᵐ ω ∂P, nuMod hν I ω = ν ω := by
  have h2 : ∀ᵐ ω ∂P, ν ω I < ∞ :=
    ae_lt_top' ((Measure.measurable_coe hI).comp_aemeasurable hν) hfin.ne
  filter_upwards [hν.ae_eq_mk, h2] with ω h1 h2
  unfold nuMod
  rw [← h1, ite_eq_left h2]

lemma nuMod_lt_top (hν : AEMeasurable ν P) (ω : Ω) : nuMod hν I ω I < ∞ := by
  unfold nuMod
  split_ifs with h
  · exact h
  · simp

/-- The kernel `ω ↦ (nuMod ω)|_I`. -/
def kerI (hν : AEMeasurable ν P) (hI : MeasurableSet I) : Kernel Ω ℝ where
  toFun ω := (nuMod hν I ω).restrict I
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [Measure.restrict_apply hs]
    exact (Measure.measurable_coe (hs.inter hI)).comp (measurable_nuMod hν hI)

lemma kerI_apply (hν : AEMeasurable ν P) (hI : MeasurableSet I) (ω : Ω) :
    kerI hν hI ω = (nuMod hν I ω).restrict I := rfl

instance (hν : AEMeasurable ν P) (hI : MeasurableSet I) : IsSFiniteKernel (kerI hν hI) :=
  isSFiniteKernel_of_ne_top _ fun ω => by
    rw [kerI_apply, Measure.restrict_apply_univ]; exact (nuMod_lt_top hν ω).ne

lemma isFiniteMeasure_kerI (hν : AEMeasurable ν P) (hI : MeasurableSet I) (ω : Ω) :
    IsFiniteMeasure (kerI hν hI ω) := by
  rw [kerI_apply]; exact isFiniteMeasure_restrict.mpr (nuMod_lt_top hν ω).ne

lemma lintegral_kerI (hν : AEMeasurable ν P) (hI : MeasurableSet I)
    (hfin : ∫⁻ ω, ν ω I ∂P < ∞) : ∫⁻ ω, kerI hν hI ω univ ∂P < ∞ := by
  simp_rw [kerI_apply, Measure.restrict_apply_univ]
  rwa [lintegral_congr_ae ((nuMod_ae_eq hν hI hfin).mono fun ω h => by rw [h])]

end RandomMeasure

/-! ## 7. The left-hand sides converge -/

section Limits

variable {a b : ℝ} {ν : Ω → Measure ℝ}

lemma integrable_setIntegral_nu (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ∞)
    (h : ℝ →ᵇ ℝ) : Integrable (fun ω => ∫ x in Icc a b, h x ∂(ν ω)) P := by
  set κ := kerI hν (measurableSet_Icc (a := a) (b := b))
  have hsm : StronglyMeasurable fun ω => ∫ x, h x ∂(κ ω) :=
    h.continuous.stronglyMeasurable.integral_kernel
  have hbd : Integrable (fun ω => ‖h‖ * (κ ω univ).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top ((κ.measurable_coe MeasurableSet.univ).aemeasurable)
      (lintegral_kerI hν measurableSet_Icc hfin).ne).const_mul _
  have hA' : Integrable (fun ω => ∫ x, h x ∂(κ ω)) P := by
    refine hbd.mono' hsm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := isFiniteMeasure_kerI hν (measurableSet_Icc (a := a) (b := b)) ω
    have := norm_integral_le_of_norm_le_const (μ := κ ω) (f := fun x => h x)
      (ae_of_all _ fun x => h.norm_coe_le_norm x)
    rwa [measureReal_def] at this
  refine hA'.congr ((nuMod_ae_eq hν measurableSet_Icc hfin).mono fun ω hω => ?_)
  simp only [κ, kerI_apply, hω]

end Limits

/-! ## 8. The Palm formula -/

end Palm
end QuantumZipper
