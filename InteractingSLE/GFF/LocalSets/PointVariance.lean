import InteractingSLE.GFF.LocalSets.GreenBound
import InteractingSLE.GFF.LocalSets.AbsCont
import QuantumZipper.Proofs.Complex.KoebeDistortion
import LQGMetric.Field.ZeroBoundaryVar
import LQGMetric.Papers.GM.S2.SpatialIndepRad
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Pointwise exponential moments of the harmonic projection (Proposition 3.3, first step)

Source: `source/ig1-specification.pdf`, §3.1, proof of Proposition 3.3 (p. 45; transcription
`source/spec/p001-048.md#prop-3.3-proof`): the harmonic Gaussian projection `h₁` has
`Var h₁(z) = Q(z, z) ≤ 4 √(d(z)/R)` near `∂D`, `d(z) = dist(z, ∂D)`, `R = dist(z, K)`, by Koebe's
estimates for the conformal map `f : 𝔻 → D`, `f(0) = z`. Here (non-sharp Koebe constants of
QuantumZipper, ruling R21) the bound is `Q(z, z) ≤ 4 t`, `t = (2 d(z)/(c R))^(1/C₂)`, proved by
monotonicity and the explicit disc Green functions of `GreenBound.lean`, and it is turned into the
exponential moment `E e^{λ h₁(z)} ≤ e^{2 λ² t}` (independence of the Markov decomposition and the
Gaussian moment generating function).

## Main results

* `exists_riemannMap_bounds`: Schwarz and Koebe bounds for the normalized Riemann map at a point;
* `zeroGFFTestCov_sub_le_of_dist`: `Var_D(ρ) − Var_V(ρ) ≤ 4 t (∫ ρ)²` for `ρ ≥ 0` near `x`;
* `lintegral_exp_sub_markov`: `E e^{t (h − h_U)(ρ)} = e^{t² (Var_D ρ − Var_U ρ)/2}`;
* `bumpTest`, `integral_mul_bumpFun_of_harmonic`: radial test functions and the mean value property;
* `lintegral_exp_bump_le`: the exponential moment bound at a point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric TopologicalSpace MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InteractingSLE
namespace GFF

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open QuantumZipper (zeroGFFTestCov)


lemma le_infDist_of_ball_subset {D : Set ℂ} (hne : D ≠ univ) {x : ℂ} {ρ : ℝ}
    (h : ball x ρ ⊆ D) : ρ ≤ infDist x Dᶜ := by
  by_contra hlt
  push Not at hlt
  have hc : (Dᶜ).Nonempty := nonempty_compl.2 hne
  obtain ⟨z, hz, hxz⟩ := (infDist_lt_iff hc).1 hlt
  exact hz (h (mem_ball'.2 hxz))

/-- **Schwarz and Koebe bounds for the Riemann map at a point.** For `x` in a simply connected
domain `D ≠ ℂ`, with `d = dist(x, ∂D)`, the normalized Riemann map `φ : D → 𝔻`, `φ x = 0`, satisfies
`‖φ y‖ ≤ |y − x| / d` on `B(x, d)` (Schwarz) and, for `‖φ y‖ < r < 1`,
`|y − x| ≤ (d / c) (1 − r)^(−C₂)` (Koebe covering with `c = 1/48` and growth with exponent `C₂`). -/
theorem exists_riemannMap_bounds {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (hDs : IsSimplyConnected D) (hDne : D ≠ univ) {x : ℂ} (hx : x ∈ D) :
    ∃ φ : ℂ → ℂ, IsConformalBijection φ D (ball 0 1) ∧ φ x = 0 ∧
      (∀ y, dist y x < infDist x Dᶜ → ‖φ y‖ ≤ dist y x / infDist x Dᶜ) ∧
      (∀ y ∈ D, ∀ r : ℝ, r < 1 → ‖φ y‖ < r →
        dist y x ≤ infDist x Dᶜ / koebeCovConst * (1 - r) ^ (-koebeDistExp)) := by
  obtain ⟨φ, hφ, hφx, -, -⟩ := exists_isConformalBijection_ball hDo hDc hDs hDne hx
  set d := infDist x Dᶜ with hd
  have hd0 : 0 < d := by
    have hc : (Dᶜ).Nonempty := nonempty_compl.2 hDne
    exact (IsClosed.notMem_iff_infDist_pos hDo.isClosed_compl hc).1 (fun h => h hx)
  have hball : ball x d ⊆ D := by
    intro y hy
    by_contra hyD
    have := infDist_le_dist_of_mem (x := x) (show y ∈ Dᶜ from hyD)
    rw [mem_ball, dist_comm] at hy
    linarith
  refine ⟨φ, hφ, hφx, fun y hy => ?_, fun y hy r hr hφy => ?_⟩
  · have hmaps : MapsTo φ (ball x d) (closedBall (φ x) 1) := fun z hz => by
      rw [hφx]; exact ball_subset_closedBall (hφ.2.mapsTo (hball hz))
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hφ.1.mono hball) hmaps (mem_ball.2 hy)
    rw [hφx, dist_zero_right] at this
    calc ‖φ y‖ ≤ 1 / d * dist y x := this
      _ = dist y x / d := by ring
  · set ψ := Function.invFunOn φ D with hψdef
    have hψφ : ∀ z ∈ D, ψ (φ z) = z := fun z hz => hφ.2.injOn.leftInvOn_invFunOn hz
    have himg : φ '' D = ball 0 1 := hφ.2.image_eq
    have hψd : DifferentiableOn ℂ ψ (ball 0 1) := by
      have := SmallGammaGeodesics.CC.differentiableOn_leftInv hDo hφ.1 hφ.2.injOn hψφ
      rwa [himg] at this
    have hψi : InjOn ψ (ball 0 1) := by
      have := SmallGammaGeodesics.CC.injOn_leftInv hψφ
      rwa [himg] at this
    have hψimg : ψ '' ball 0 1 = D := by
      rw [← himg]; exact SmallGammaGeodesics.CC.image_leftInv_image hψφ subset_rfl
    have hψ0 : ψ 0 = x := by rw [← hφx]; exact hψφ x hx
    have hζ : φ y ∈ ball (0 : ℂ) 1 := hφ.2.mapsTo hy
    -- Koebe covering: `c ‖ψ'(0)‖ ≤ d`
    have hcov := QuantumZipper.CA.Koebe.ball_subset_image_koebe hψd hψi
    rw [hψimg, hψ0, mul_one] at hcov
    have hK : koebeCovConst * ‖deriv ψ 0‖ ≤ d := le_infDist_of_ball_subset hDne hcov
    -- growth
    have hg := QuantumZipper.CA.Koebe.norm_sub_le_growth_global hψd hψi hζ
    rw [hψφ y hy, hψ0, div_one, dist_zero_right, ← dist_eq_norm] at hg
    have hn1 : ‖φ y‖ ≤ 1 := (mem_ball_zero_iff.1 hζ).le
    have hpow : (1 - ‖φ y‖) ^ (-koebeDistExp) ≤ (1 - r) ^ (-koebeDistExp) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith [koebeDistExp_pos])
    have hderiv : ‖deriv ψ 0‖ ≤ d / koebeCovConst := by
      rw [le_div_iff₀ koebeCovConst_pos]; linarith
    have hP : 0 ≤ (1 - r) ^ (-koebeDistExp) := Real.rpow_nonneg (by linarith) _
    calc dist y x ≤ ‖φ y‖ * (‖deriv ψ 0‖ * (1 - ‖φ y‖) ^ (-koebeDistExp)) := hg
      _ ≤ 1 * (d / koebeCovConst * (1 - r) ^ (-koebeDistExp)) := by
          have : 0 ≤ d / koebeCovConst := div_nonneg hd0.le koebeCovConst_pos.le
          gcongr
      _ = d / koebeCovConst * (1 - r) ^ (-koebeDistExp) := one_mul _


/-- `log(1 + t²) − log(1 − t²/(1 − t)²) − log(1 − t) ≤ 4t` for `0 ≤ t ≤ 1/4`. -/
lemma logDelta_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    Real.log (1 + t ^ 2) - Real.log (1 - t ^ 2 / (1 - t) ^ 2) - Real.log (1 - t) ≤ 4 * t := by
  have h1 : Real.log (1 + t ^ 2) ≤ t ^ 2 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2); linarith
  have hq : (9 : ℝ) / 16 ≤ (1 - t) ^ 2 := by nlinarith
  set u := t ^ 2 / (1 - t) ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 16 / 9 * t ^ 2 := by
    rw [hu, div_le_iff₀ (by positivity)]; nlinarith
  have hu2 : u ≤ 1 / 9 := by nlinarith
  have hlog : ∀ v : ℝ, v < 1 → -Real.log (1 - v) ≤ v / (1 - v) := by
    intro v hv
    have hpos : (0 : ℝ) < 1 - v := by linarith
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at this
    have e : (1 - v)⁻¹ - 1 = v / (1 - v) := by field_simp; ring
    linarith
  have h2 : -Real.log (1 - u) ≤ 2 * t ^ 2 := by
    refine (hlog u (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : -Real.log (1 - t) ≤ 4 / 3 * t := by
    refine (hlog t (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  nlinarith

/-- **Diagonal bound for the harmonic projection** (specification Proposition 3.3, first step,
without Brownian motion). Let `D ≠ ℂ` be a simply connected domain, `V ⊆ D` open, `x ∈ D` with
`D ∩ B(x, R) ⊆ V`, `d = dist(x, ∂D)` and `t = (2d/(cR))^(1/C₂) ≤ 1/4` (`c`, `C₂` the Koebe
constants).
For every test function `ρ ≥ 0` supported in `B(x, t d)`:
`Var_D(ρ) − Var_V(ρ) ≤ 4 t (∫ ρ)²`. -/
theorem zeroGFFTestCov_sub_le_of_dist {D V : Opens ℂ} (hVD : V ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {x : ℂ} (hx : x ∈ D) {R : ℝ} (hR : 0 < R)
    (hRV : ∀ y ∈ D, dist y x < R → y ∈ V)
    (ht : (2 * infDist x (D : Set ℂ)ᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4)
    (ρ : LQGMetric.TestOn D) (ρV : LQGMetric.TestOn V) (hρV : ⇑ρV = ⇑ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρs : ∀ y, ρ y ≠ 0 →
      dist y x < (2 * infDist x (D : Set ℂ)ᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ *
        infDist x (D : Set ℂ)ᶜ) :
    zeroGFFTestCov D ρ ρ - zeroGFFTestCov V ρV ρV ≤
      4 * (2 * infDist x (D : Set ℂ)ᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ *
        (∫ y, ρ y) ^ 2 := by
  obtain ⟨φ, hφ, hφx, hS, hG⟩ := exists_riemannMap_bounds D.isOpen hDc hDs hDne hx
  set d := infDist x (D : Set ℂ)ᶜ with hd
  set a := 2 * d / (koebeCovConst * R) with ha
  set t := a ^ koebeDistExp⁻¹ with htdef
  have hd0 : 0 < d := by
    have hc : ((D : Set ℂ)ᶜ).Nonempty := nonempty_compl.2 hDne
    exact (IsClosed.notMem_iff_infDist_pos D.isOpen.isClosed_compl hc).1 (fun h => h hx)
  have ha0 : 0 < a := by have := koebeCovConst_pos; positivity
  have ht0 : 0 < t := Real.rpow_pos_of_pos ha0 _
  have hC := koebeDistExp_pos
  -- the conformal disc `W = {‖φ‖ < 1 − t}`
  have hWo : IsOpen {y | y ∈ (D : Set ℂ) ∧ ‖φ y‖ < 1 - t} := by
    have := hφ.1.continuousOn.isOpen_inter_preimage D.isOpen
      (isOpen_lt continuous_norm (continuous_const (y := 1 - t)) : IsOpen {w : ℂ | ‖w‖ < 1 - t})
    exact this
  let W : TopologicalSpace.Opens ℂ := ⟨_, hWo⟩
  have htpow : t ^ (-koebeDistExp) = a⁻¹ := by
    rw [htdef, ← Real.rpow_mul ha0.le, mul_neg, inv_mul_cancel₀ hC.ne', Real.rpow_neg_one]
  have hWV : (W : Set ℂ) ⊆ V := by
    rintro y ⟨hyD, hy⟩
    refine hRV y hyD ?_
    have := hG y hyD (1 - t) (by linarith) hy
    rw [sub_sub_cancel, htpow, ha] at this
    have e : d / koebeCovConst * (2 * d / (koebeCovConst * R))⁻¹ = R / 2 := by
      have := koebeCovConst_pos; field_simp
    rw [e] at this
    linarith
  -- the support of `ρ` lies in `W`
  have hclos : closedBall x (t * d) ⊆ (W : Set ℂ) := by
    intro y hy
    have hyd : dist y x < d := lt_of_le_of_lt (mem_closedBall.1 hy) (by nlinarith)
    refine ⟨?_, ?_⟩
    · by_contra hyD
      have := infDist_le_dist_of_mem (x := x) (show y ∈ (D : Set ℂ)ᶜ from hyD)
      rw [dist_comm] at this; linarith
    · have h1 := hS y hyd
      have h2 : dist y x / d ≤ t := by
        rw [div_le_iff₀ hd0]; exact mem_closedBall.1 hy
      linarith
  have hsuppW : tsupport ρ ⊆ (W : Set ℂ) := by
    refine (closure_minimal (fun y hy => ?_) isClosed_closedBall).trans hclos
    exact mem_closedBall.2 (hρs y hy).le
  let ρW : LQGMetric.TestOn W := ⟨ρ, ρ.contDiff, ρ.hasCompactSupport, hsuppW⟩
  have hρWf : ⇑ρW = ⇑ρ := rfl
  have hD : LQGMetric.ZBAdmissible D := zbAdmissible_of_isSimplyConnected hDc hDs hDne
  have hWD : W ≤ D := fun y hy => hy.1
  have hmono := LQGMetric.zeroGFFTestCov_self_mono (U := W) (U' := V) hWV
    (zbAdmissible_mono hWD hD) (zbAdmissible_mono hVD hD) ρW ρV (hρV.trans hρWf.symm)
  have hmain := zeroGFFTestCov_sub_le_of_isConformalBijection_ball hφ ht0.le (by linarith)
    (by linarith) (W := W) rfl ρ ρW hρWf hρ0 (fun y hy => by
      have hy' := hρs y hy
      have hyd : dist y x < d := lt_of_lt_of_le hy' (by nlinarith)
      have h1 := hS y hyd
      have h2 : dist y x / d < t := by rw [div_lt_iff₀ hd0]; exact hy'
      linarith)
  have hΔ := logDelta_le ht0.le ht
  have hI : 0 ≤ (∫ y, ρ y) ^ 2 := sq_nonneg _
  calc zeroGFFTestCov D ρ ρ - zeroGFFTestCov V ρV ρV
      ≤ zeroGFFTestCov D ρ ρ - zeroGFFTestCov W ρW ρW := by linarith
    _ ≤ _ := hmain
    _ ≤ 4 * t * (∫ y, ρ y) ^ 2 := mul_le_mul_of_nonneg_right hΔ hI


/-! ### Exponential moments of the harmonic part -/

section MGF

open LQGMetric


/-- The exponential moment of a centred Gaussian: `E e^{tX} = e^{t² Var X / 2}` (in `ℝ≥0∞`). -/
lemma lintegral_ofReal_exp_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P) (h0 : ∫ ω, X ω ∂P = 0)
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P =
      ENNReal.ofReal (Real.exp (t ^ 2 * Var[X; P] / 2)) := by
  have hmap := hX.map_eq_gaussianReal
  rw [h0] at hmap
  have hXm : AEMeasurable X P := hX.aemeasurable
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (t * x)) := by fun_prop
  rw [← lintegral_map' hm.aemeasurable hXm, hmap,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := Var[X; P].toNNReal)) t
  simp only [mgf, id] at this
  rw [this, Real.coe_toNNReal _ (variance_nonneg X P)]
  ring_nf

/-- **Exponential moments of the harmonic part of the Markov decomposition.** If
`h = h_U + (h − h_U)` is the Markov decomposition of a zero-boundary GFF `h` on `D` and `ρ` is a
test function supported in `U`, then `E e^{t (h − h_U)(ρ)} = e^{t² (Var_D ρ − Var_U ρ)/2}`. -/
theorem lintegral_exp_sub_markov {U D : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition U D h hU P) (ρ : TestOn D) (hρU : tsupport ρ ⊆ (U : Set ℂ))
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (h ω ρ - hU ω ρ))) ∂P =
      ENNReal.ofReal (Real.exp (t ^ 2 * (zeroGFFTestCov D ρ ρ - zeroGFFTestCov U ρ ρ) / 2)) := by
  have hind : (U : Set ℂ).indicator (ρ : ℂ → ℝ) = ρ := by
    refine indicator_eq_self.2 fun y hy => hρU (subset_closure hy)
  have hX := hh.process.gaussian.hasGaussianLaw_eval ρ
  have hZ := hd.isZBGFFExtOn.gaussian.hasGaussianLaw_eval ρ
  have hXv : Var[fun ω => h ω ρ; P] = zeroGFFTestCov D ρ ρ := by
    rw [← covariance_self hX.aemeasurable]; exact hh.process.covariance_eq ρ ρ
  have hZv : Var[fun ω => hU ω ρ; P] = zeroGFFTestCov U ρ ρ := by
    rw [← covariance_self hZ.aemeasurable, hd.isZBGFFExtOn.covariance_eq ρ ρ, hind]
  have eX := lintegral_ofReal_exp_of_hasGaussianLaw hX (hh.process.centered ρ) t
  have eZ := lintegral_ofReal_exp_of_hasGaussianLaw hZ (hd.isZBGFFExtOn.centered ρ) t
  rw [hXv] at eX
  rw [hZv] at eZ
  -- independence
  have hφm : Measurable fun T : DistOn D => ENNReal.ofReal (Real.exp (t * T ρ)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_distOn_apply ρ)))
  have hindep := hd.indepFun.comp hφm hφm
  have hfm : Measurable fun ω => ENNReal.ofReal (Real.exp (t * hU ω ρ)) :=
    hφm.comp hd.isZBGFFExtOn.measurable
  have hsubm : Measurable fun ω => h ω - hU ω :=
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp hh.measurable).sub
        ((measurable_distOn_apply φ).comp hd.isZBGFFExtOn.measurable)
  have hgm : Measurable fun ω => ENNReal.ofReal (Real.exp (t * (h ω - hU ω) ρ)) := hφm.comp hsubm
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hfm hgm hindep
  have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (t * h ω ρ)) =
      ENNReal.ofReal (Real.exp (t * hU ω ρ)) *
        ENNReal.ofReal (Real.exp (t * (h ω - hU ω) ρ)) := fun ω => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [sub_apply]
    ring
  have hkey : ENNReal.ofReal (Real.exp (t ^ 2 * zeroGFFTestCov D ρ ρ / 2)) =
      ENNReal.ofReal (Real.exp (t ^ 2 * zeroGFFTestCov U ρ ρ / 2)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (h ω - hU ω) ρ)) ∂P := by
    rw [← eX, ← eZ, ← hprod]
    exact lintegral_congr fun ω => hsplit ω
  have hne0 : ENNReal.ofReal (Real.exp (t ^ 2 * zeroGFFTestCov U ρ ρ / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hnetop : ENNReal.ofReal (Real.exp (t ^ 2 * zeroGFFTestCov U ρ ρ / 2)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have e : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (h ω ρ - hU ω ρ))) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (h ω - hU ω) ρ)) ∂P := by
    simp only [sub_apply]
  rw [e, (ENNReal.eq_div_iff hne0 hnetop).2 hkey.symm,
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  congr 2
  ring

end MGF

/-! ### Radial bumps and the exponential moment at a point -/

open LQGMetric.GM (radProf contDiff_radProf radProf_eq_zero radProf_nonneg radProf_rot
  integral_radProf_pos radProf_le)

/-- The radial bump `y ↦ e(1 − |y − x|²/δ²)` (`e` = `expNegInvGlue`), supported in `B̄(x, δ)`. -/
def bumpFun (x : ℂ) (δ : ℝ) (y : ℂ) : ℝ := radProf 1 ((y - x) / δ)

/-- The mass `∫ e(1 − |y|²)` of the unit bump. -/
def bumpMass : ℝ := ∫ y, radProf 1 y

lemma bumpMass_pos : 0 < bumpMass := integral_radProf_pos one_pos

lemma contDiff_bumpFun (x : ℂ) (δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bumpFun x δ) :=
  (contDiff_radProf 1).comp ((contDiff_id.sub contDiff_const).div_const _)

lemma bumpFun_nonneg (x : ℂ) (δ : ℝ) (y : ℂ) : 0 ≤ bumpFun x δ y := radProf_nonneg _ _

lemma bumpFun_le (x : ℂ) (δ : ℝ) (y : ℂ) : bumpFun x δ y ≤ expNegInvGlue 1 := by
  have := radProf_le 1 ((y - x) / δ); rwa [one_pow] at this

lemma bumpFun_eq_zero {x : ℂ} {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (hy : δ ≤ dist y x) :
    bumpFun x δ y = 0 := by
  refine radProf_eq_zero zero_le_one ?_
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, le_div_iff₀ hδ, one_mul,
    ← dist_eq_norm]
  exact hy

lemma tsupport_bumpFun_subset {x : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    tsupport (bumpFun x δ) ⊆ closedBall x δ := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra h
  rw [mem_closedBall, not_le] at h
  exact hy (bumpFun_eq_zero hδ h.le)

lemma hasCompactSupport_bumpFun {x : ℂ} {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (bumpFun x δ) :=
  (isCompact_closedBall x δ).of_isClosed_subset (isClosed_tsupport _) (tsupport_bumpFun_subset hδ)

lemma integral_bumpFun {x : ℂ} {δ : ℝ} (hδ : 0 < δ) : ∫ y, bumpFun x δ y = δ ^ 2 * bumpMass := by
  have h1 : ∫ y, bumpFun x δ y = ∫ y, radProf 1 (δ⁻¹ • y) := by
    rw [← integral_sub_right_eq_self (fun y => radProf 1 (δ⁻¹ • y)) x]
    congr 1; funext y
    simp only [bumpFun, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  rw [h1, Measure.integral_comp_inv_smul_of_nonneg volume (radProf 1) hδ.le,
    Complex.finrank_real_complex, smul_eq_mul, bumpMass]

/-- **Mean value property** against the radial bump: `∫ g · bump_{x,δ} = g(x) δ² ∫ e(1 − |y|²)`. -/
lemma integral_mul_bumpFun_of_harmonic {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V) {x : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall x δ ⊆ V) :
    ∫ y, g y * bumpFun x δ y = g x * (δ ^ 2 * bumpMass) := by
  have hmv := LQGMetric.GM.integral_mul_radial_of_harmonic hV hg hB
    (ψ := fun z => radProf 1 (z / δ)) ((contDiff_radProf 1).continuous.comp
      (continuous_id.div_const _))
    (fun z hz => radProf_eq_zero zero_le_one (by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, le_div_iff₀ hδ,
        one_mul]; exact hz.le))
    (fun a z => by simp only [mul_div_assoc]; exact radProf_rot 1 a _)
  have h2 : ∫ z, radProf 1 (z / δ) = δ ^ 2 * bumpMass := by
    have := integral_bumpFun (x := 0) hδ
    simpa [bumpFun] using this
  rw [← h2, ← hmv, ← integral_add_left_eq_self (fun y => g y * bumpFun x δ y) x]
  congr 1; funext z
  simp [bumpFun]

/-- The bump as a test function on `D ⊇ B̄(x, δ)`. -/
def bumpTest {D : Opens ℂ} (x : ℂ) {δ : ℝ} (hδ : 0 < δ) (hB : closedBall x δ ⊆ D) :
    LQGMetric.TestOn D :=
  ⟨bumpFun x δ, contDiff_bumpFun x δ, hasCompactSupport_bumpFun hδ,
    (tsupport_bumpFun_subset hδ).trans hB⟩

@[simp] lemma coe_bumpTest {D : Opens ℂ} (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall x δ ⊆ D) : ⇑(bumpTest x hδ hB) = bumpFun x δ := rfl



/-- The Koebe scale `t = (2 d(x)/(c R))^(1/C₂)` of the variance bound, `d(x) = dist(x, ∂D)`. -/
def koebeScale (D : Set ℂ) (x : ℂ) (R : ℝ) : ℝ :=
  (2 * infDist x Dᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹

lemma koebeScale_nonneg (D : Set ℂ) (x : ℂ) {R : ℝ} (hR : 0 < R) : 0 ≤ koebeScale D x R := by
  have h1 := koebeCovConst_pos
  have h2 := infDist_nonneg (x := x) (s := Dᶜ)
  exact Real.rpow_nonneg (by positivity) _

/-- If the Koebe scale is at most `1/4` then `dist(x, ∂D) < R`. -/
lemma infDist_lt_of_koebeScale_le {D : Set ℂ} {x : ℂ} {R : ℝ} (hR : 0 < R)
    (ht : koebeScale D x R ≤ 1 / 4) : infDist x Dᶜ < R := by
  have hc := koebeCovConst_pos
  have hc1 : koebeCovConst < 1 := by norm_num [koebeCovConst]
  have ha : 2 * infDist x Dᶜ / (koebeCovConst * R) < 1 := by
    by_contra hge
    push Not at hge
    have := Real.one_le_rpow hge (inv_nonneg.2 koebeDistExp_pos.le)
    unfold koebeScale at ht
    linarith
  rw [div_lt_one (by positivity)] at ha
  nlinarith [infDist_nonneg (x := x) (s := Dᶜ)]

/-- **Exponential moment of the harmonic projection at a point** (specification Proposition 3.3,
Gaussian moment bound). In the setting of `zeroGFFTestCov_sub_le_of_dist`, there is a radius
`δ > 0` with `B̄(x, δ) ⊆ U` such that the normalized bump pairing
`X = (h − h_U)(bump_{x,δ}) / ∫ bump_{x,δ}` (`= h₁(x)` when `h − h_U` is harmonic on `U`) satisfies
`E e^{λ X} ≤ e^{2 λ² t}`, `t = koebeScale D x R`. -/
theorem exists_lintegral_exp_bump_le {U D : Opens ℂ} (hUD : U ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → LQGMetric.DistOn D}
    (hh : LQGMetric.IsZeroBoundaryGFF D h P) (hd : IsMarkovDecomposition U D h hU P) {x : ℂ}
    (hx : x ∈ D) {R : ℝ} (hR : 0 < R) (hRU : ∀ y ∈ D, dist y x < R → y ∈ U)
    (ht : koebeScale D x R ≤ 1 / 4) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hB : closedBall x δ ⊆ U), ∀ lam : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam *
          ((h ω - hU ω) (bumpTest x hδ (hB.trans hUD)) / (δ ^ 2 * bumpMass)))) ∂P ≤
        ENNReal.ofReal (Real.exp (2 * lam ^ 2 * koebeScale D x R)) := by
  set d := infDist x (D : Set ℂ)ᶜ with hdd
  set τ := koebeScale D x R with hτ
  have hd0 : 0 < d := by
    have hc : ((D : Set ℂ)ᶜ).Nonempty := nonempty_compl.2 hDne
    exact (IsClosed.notMem_iff_infDist_pos D.isOpen.isClosed_compl hc).1 (fun h => h hx)
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos (by have := koebeCovConst_pos; positivity) _
  have hdR : d < R := infDist_lt_of_koebeScale_le hR ht
  set δ := τ * d / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδd : δ < d := by nlinarith
  have hB : closedBall x δ ⊆ U := by
    intro y hy
    have hyx : dist y x < d := lt_of_le_of_lt (mem_closedBall.1 hy) hδd
    have hyD : y ∈ (D : Set ℂ) := by
      by_contra hyD
      have := infDist_le_dist_of_mem (x := x) (show y ∈ (D : Set ℂ)ᶜ from hyD)
      rw [dist_comm] at this; linarith
    exact hRU y hyD (by linarith)
  refine ⟨δ, hδ, hB, fun lam => ?_⟩
  set ρ := bumpTest x hδ (hB.trans hUD) with hρ
  have hmass : ∫ y, ρ y = δ ^ 2 * bumpMass := by rw [hρ, coe_bumpTest]; exact integral_bumpFun hδ
  have hm0 : 0 < δ ^ 2 * bumpMass := by have := bumpMass_pos; positivity
  have hvar := zeroGFFTestCov_sub_le_of_dist hUD hDc hDs hDne hx hR hRU ht ρ
    (bumpTest x hδ hB) rfl (fun y => bumpFun_nonneg x δ y) (fun y hy => by
      by_contra hge
      push Not at hge
      change τ * d ≤ dist y x at hge
      exact hy (bumpFun_eq_zero hδ (by nlinarith)))
  change _ ≤ 4 * τ * (∫ y, ρ y) ^ 2 at hvar
  have hmgf := lintegral_exp_sub_markov hh hd ρ ((tsupport_bumpFun_subset hδ).trans hB)
    (lam / (δ ^ 2 * bumpMass))
  have e : ∀ ω, lam * ((h ω - hU ω) ρ / (δ ^ 2 * bumpMass)) =
      lam / (δ ^ 2 * bumpMass) * (h ω ρ - hU ω ρ) := fun ω => by
    simp only [sub_apply]; ring
  simp_rw [e]
  rw [hmgf]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hv : zeroGFFTestCov D ρ ρ - zeroGFFTestCov U ρ ρ ≤ 4 * τ * (δ ^ 2 * bumpMass) ^ 2 := by
    rw [← hmass]; exact hvar
  calc (lam / (δ ^ 2 * bumpMass)) ^ 2 * (zeroGFFTestCov D ρ ρ - zeroGFFTestCov U ρ ρ) / 2
      ≤ (lam / (δ ^ 2 * bumpMass)) ^ 2 * (4 * τ * (δ ^ 2 * bumpMass) ^ 2) / 2 := by
        gcongr
    _ = 2 * lam ^ 2 * τ := by
        have := bumpMass_pos
        field_simp
        ring


end GFF
end InteractingSLE
