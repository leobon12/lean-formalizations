import GaussianLQG.Field.Realization.Represent
import GaussianLQG.Field.Realization.Mollify
import GaussianLQG.Field.Frame.Circle
import LQGMetric.Field.CircleAvgAffine

/-!
# Pairing compatibility of the coordinate realization (blueprint Prop. 1.9 (c))

For every regular measure `μ`, almost surely
`∑_{j<n} ω_j ∫ e_j dμ → (h₀(ω), μ)` (`ae_tendsto_measPairing`), where `(h₀, μ)` is the
mollified pairing `measPairing` of the normalized coordinate field `h₀ = field0 b` and
`e_j = frameFunN (b j)`.

Proof. Write `X_m = ∫ ⟨h₀, ψ_{m,x}⟩ μ(dx)`. On the good set, `X_m = X̃^μ_m - h̃_1(0) μ(ℂ)` and
`X̃^ρ_m = ∫ ⟨h̃, ψ_{m,x}⟩ ρ(dx)` is the limit of the coordinate series with coefficients
`∫ ẽ_k d(ρ * ψ_m)` (`tendsto_psum_pairCoef`). Subtracting `μ(ℂ)` times the circle case `ρ = σ`
removes the circle-average constants `avg_{∂𝔻} ẽ_k`, so `X_m = D_m + μ(ℂ)(X̃^σ_m - h̃_1(0))`, where
`D_m` is the sum of the coordinate series with coefficients `∫ e_k d(μ * ψ_m) - μ(ℂ) ∫ e_k d(σ * ψ_m)`.
`X̃^σ_m` is the mollified circle average of `h̃`, which converges to `h̃_1(0)`. By the frame
identity and the energy decay of mollification (`frame_moll_decay`), `D_m - L` (with
`L = ∑_k ω_k ∫ e_k dμ`) is Gaussian with variance `≤ K q^m`, so `D_m → L` almost surely
(Chebyshev and Borel–Cantelli).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace GaussianLQG
namespace Realization

open LQGMetric LQGMetric.GFFExist

variable (b : HilbertBasis ℕ ℝ WNSpace)

lemma field0_apply (ω : Coord) (φ : TestC) :
    field0 b ω φ = tildeField b ω φ - circleAvg (tildeField b ω) 1 0 * ∫ x, φ x := by
  simp only [field0, addConst, addFun, add_apply, ofCont_apply, ContinuousMap.const_apply]
  rw [integral_mul_const]
  ring

lemma frameFun0_eq_add (g : WNSpace) (y : ℂ) :
    frameFun0 g y = frameFunN g y + Real.circleAverage (frameFun0 g) 0 1 := by
  simp only [frameFunN]; ring

lemma summable_sq_sub_mul {x y : ℕ → ℝ} (hx : Summable fun k => x k ^ 2)
    (hy : Summable fun k => y k ^ 2) (c : ℝ) : Summable fun k => (x k - c * y k) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((hx.mul_left 2).add (hy.mul_left (2 * c ^ 2)))
  have := sq_nonneg (x k + c * y k)
  nlinarith

lemma frame_summable_sq {e : ℕ → ℂ → ℝ} (hframe : IsGFFFrame e) {ρ : Measure ℂ}
    (hρ : IsRegular ρ) : Summable fun k => (∫ z, e k z ∂ρ) ^ 2 :=
  (hframe.2.2 ρ ρ hρ hρ).summable.congr fun _ => (sq _).symm

variable (hb : ∀ j, IsNiceWN (b j))
include hb

lemma integral_moll_frameFunN {ρ : Measure ℂ} [IsFiniteMeasure ρ] {R : ℝ}
    (hR : ρ (closedBall (0 : ℂ) R)ᶜ = 0) (m k : ℕ) :
    ∫ z, frameFunN (b k) z ∂moll m ρ = ∫ x, (∫ y, bumpTest m x y * frameFunN (b k) y) ∂ρ :=
  integral_moll_eq (measurable_frameFunN (hb k))
    (integrable_of_continuous_of_compl_closedBall (continuous_frameFunN (hb k))
      (moll_compl_closedBall hR))

lemma pairCoef_eq {ρ : Measure ℂ} [IsFiniteMeasure ρ] {R : ℝ}
    (hR : ρ (closedBall (0 : ℂ) R)ᶜ = 0) (m k : ℕ) :
    pairCoef b m ρ k = ∫ z, frameFunN (b k) z ∂moll m ρ +
      Real.circleAverage (frameFun0 (b k)) 0 1 * ρ.real univ := by
  rw [integral_moll_frameFunN b hb hR m k, pairCoef]
  obtain ⟨B, hB⟩ := exists_bound_frameFunN (hb k)
  have hI : Integrable (fun x => ∫ y, bumpTest m x y * frameFunN (b k) y) ρ :=
    integrable_of_bounded (measurable_integral_bump_mul m (continuous_frameFunN (hb k)))
      fun x => abs_integral_bump_mul_le m x (continuous_frameFunN (hb k)) hB
  have e : ∀ x, ∫ y, bumpTest m x y * frameFun0 (b k) y =
      (∫ y, bumpTest m x y * frameFunN (b k) y) + Real.circleAverage (frameFun0 (b k)) 0 1 :=
    fun x => by
      simp_rw [frameFun0_eq_add (b k)]
      exact integral_bump_mul_add_const m x (continuous_frameFunN (hb k)) _
  simp_rw [e]
  rw [integral_add hI (integrable_const _), integral_const, smul_eq_mul, mul_comm]

lemma integral_frameFunN_circle (k : ℕ) : ∫ z, frameFunN (b k) z ∂circleMeasure 0 1 = 0 := by
  rw [integral_circleMeasure 0 1 (measurable_frameFunN (hb k)).aestronglyMeasurable]
  have h0 := continuous_frameFun0 (hb k)
  have e : frameFunN (b k) = frameFun0 (b k) - fun _ => Real.circleAverage (frameFun0 (b k)) 0 1 :=
    funext fun y => by simp only [frameFunN, Pi.sub_apply]
  rw [e, Real.circleAverage_sub h0.continuousOn.circleIntegrable'
    continuousOn_const.circleIntegrable', Real.circleAverage_const, sub_self]

/-- **Pairing compatibility** (blueprint Prop. 1.9 (c)). -/
theorem ae_tendsto_measPairing (hframe : IsGFFFrame fun j => frameFunN (b j)) {μ : Measure ℂ}
    (hμ : IsRegular μ) :
    ∀ᵐ ω ∂stdP, Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, frameFunN (b j) z ∂μ)
      atTop (𝓝 (measPairing (field0 b ω) μ)) := by
  set e : ℕ → ℂ → ℝ := fun j => frameFunN (b j) with he
  set σ : Measure ℂ := circleMeasure 0 1 with hσdef
  have hσ : IsRegular σ := isRegular_circleMeasure 0 one_pos
  obtain ⟨hμfin, ⟨R, hR⟩, -⟩ := id hμ
  set c : ℝ := μ.real univ with hcdef
  set a : ℕ → ℝ := fun k => ∫ z, e k z ∂μ with hadef
  set Q : Measure ℂ → ℕ → ℕ → ℝ := fun ρ m k => ∫ z, e k z ∂moll m ρ with hQdef
  set d : ℕ → ℕ → ℝ := fun m k => Q μ m k - c * Q σ m k with hddef
  set g : ℕ → ℕ → ℝ := fun m k => d m k - a k with hgdef
  -- summability
  have ha : Summable fun k => a k ^ 2 := frame_summable_sq hframe hμ
  have hQs : ∀ ρ : Measure ℂ, IsRegular ρ → ∀ m, Summable fun k => Q ρ m k ^ 2 :=
    fun ρ hρ m => frame_summable_sq hframe (isRegular_moll hρ m)
  have hds : ∀ m, Summable fun k => d m k ^ 2 := fun m =>
    summable_sq_sub_mul (hQs μ hμ m) (hQs σ hσ m) c
  have hgs : ∀ m, Summable fun k => g m k ^ 2 := fun m => summable_sq_sub (hds m) ha
  -- the decay of the variances
  obtain ⟨Kμ, qμ, hKμ, hqμ0, hqμ1, hdecμ⟩ := frame_moll_decay hframe hμ
  obtain ⟨Kσ, qσ, hKσ, hqσ0, hqσ1, hdecσ⟩ := frame_moll_decay hframe hσ
  set q : ℝ := max qμ qσ with hqdef
  have hq0 : 0 < q := lt_of_lt_of_le hqμ0 (le_max_left _ _)
  have hq1 : q < 1 := max_lt hqμ1 hqσ1
  set K : ℝ := 2 * Kμ + 2 * c ^ 2 * Kσ with hKdef
  have hgbound : ∀ m, ∑' k, g m k ^ 2 ≤ K * q ^ m := by
    intro m
    obtain ⟨hsμ, hbμ⟩ := hdecμ m
    obtain ⟨hsσ, hbσ⟩ := hdecσ m
    have hσ0 : ∀ k, ∫ z, e k z ∂σ = 0 := fun k => integral_frameFunN_circle b hb k
    have hpt : ∀ k, g m k ^ 2 ≤ 2 * (∫ z, e k z ∂moll m μ - ∫ z, e k z ∂μ) ^ 2 +
        2 * c ^ 2 * (∫ z, e k z ∂moll m σ - ∫ z, e k z ∂σ) ^ 2 := by
      intro k
      simp only [hgdef, hddef, hQdef, hσ0 k, sub_zero, hadef]
      have := sq_nonneg ((∫ z, e k z ∂moll m μ) - (∫ z, e k z ∂μ) +
        c * ∫ z, e k z ∂moll m σ)
      nlinarith
    calc ∑' k, g m k ^ 2
        ≤ ∑' k, (2 * (∫ z, e k z ∂moll m μ - ∫ z, e k z ∂μ) ^ 2 +
          2 * c ^ 2 * (∫ z, e k z ∂moll m σ - ∫ z, e k z ∂σ) ^ 2) :=
          (hgs m).tsum_le_tsum hpt ((hsμ.mul_left 2).add (hsσ.mul_left (2 * c ^ 2)))
      _ = 2 * ∑' k, (∫ z, e k z ∂moll m μ - ∫ z, e k z ∂μ) ^ 2 +
          2 * c ^ 2 * ∑' k, (∫ z, e k z ∂moll m σ - ∫ z, e k z ∂σ) ^ 2 := by
          rw [(hsμ.mul_left 2).tsum_add (hsσ.mul_left (2 * c ^ 2)), tsum_mul_left, tsum_mul_left]
      _ ≤ 2 * (Kμ * qμ ^ m) + 2 * c ^ 2 * (Kσ * qσ ^ m) :=
          add_le_add (mul_le_mul_of_nonneg_left hbμ zero_le_two)
            (mul_le_mul_of_nonneg_left hbσ (by positivity))
      _ ≤ 2 * (Kμ * q ^ m) + 2 * c ^ 2 * (Kσ * q ^ m) := by
          have h1 : qμ ^ m ≤ q ^ m := pow_le_pow_left₀ hqμ0.le (le_max_left _ _) m
          have h2 : qσ ^ m ≤ q ^ m := pow_le_pow_left₀ hqσ0.le (le_max_right _ _) m
          have h3 : 0 ≤ c ^ 2 * Kσ := mul_nonneg (sq_nonneg _) hKσ
          nlinarith
      _ = K * q ^ m := by rw [hKdef]; ring
  -- the almost sure events
  have hE3 : ∀ᵐ ω ∂stdP, ∀ m, Tendsto (fun n => psum (d m) n ω) atTop
      (𝓝 (seriesLim (d m) ω)) := ae_all_iff.mpr fun m => ae_tendsto_seriesLim (hds m)
  have hE5 : ∀ᵐ ω ∂stdP, ∀ m, Tendsto (fun n => psum (g m) n ω) atTop
      (𝓝 (seriesLim (g m) ω)) := ae_all_iff.mpr fun m => ae_tendsto_seriesLim (hgs m)
  have hE4 : ∀ᵐ ω ∂stdP, Tendsto (fun m => seriesLim (g m) ω) atTop (𝓝 0) :=
    CircleAvg.ae_tendsto_zero_of_sq_le (Y := fun m ω => seriesLim (g m) ω)
      (fun m => (memLp_seriesLim (hgs m)).integrable_sq) hq0 hq1
      (fun m => (integral_sq_seriesLim (hgs m)).le.trans (hgbound m))
  filter_upwards [ae_mem_goodW b, ae_tendsto_seriesLim ha, hE3, hE4, hE5] with ω hW h2 h3 h4 h5
  set T : DistC := tildeField b ω with hT
  obtain ⟨aω, haω⟩ := hW.2
  have hcirc : circleAvg T 1 0 = aω := CircleAvg.circleAvg_eq_of_tendsto haω
  have hRμ := fun m => tendsto_psum_pairCoef b hb hW.1 m hR
  have hRσ := fun m =>
    tendsto_psum_pairCoef b hb hW.1 m (ρ := σ) WNFrame.circleMeasure_compl_closedBall
  have hXσ : ∀ m, ∫ x, T (bumpTest m x) ∂σ = CircleAvg.mollAvg T m 0 1 := fun m =>
    integral_circleMeasure 0 1 (measurable_tildeField_bump b hW.1 m).aestronglyMeasurable
  -- the coefficients `d` in terms of the pairing coefficients
  have hdP : ∀ m k, d m k = pairCoef b m μ k - c * pairCoef b m σ k := by
    intro m k
    have hσ1 : σ.real univ = 1 := probReal_univ
    rw [pairCoef_eq b hb hR m k,
      pairCoef_eq b hb (ρ := σ) WNFrame.circleMeasure_compl_closedBall m k, hσ1]
    simp only [hddef, hQdef, hcdef, he]
    ring
  have hd_eq : ∀ m, seriesLim (d m) ω =
      (∫ x, T (bumpTest m x) ∂μ) - c * ∫ x, T (bumpTest m x) ∂σ := by
    intro m
    have h1 : Tendsto (fun j => psum (d m) (subN b j) ω) atTop
        (𝓝 ((∫ x, T (bumpTest m x) ∂μ) - c * ∫ x, T (bumpTest m x) ∂σ)) := by
      have e : ∀ j, psum (d m) (subN b j) ω =
          psum (pairCoef b m μ) (subN b j) ω - c * psum (pairCoef b m σ) (subN b j) ω := by
        intro j
        rw [← psum_smul, ← psum_sub]
        exact congrArg (fun f => psum f (subN b j) ω) (funext (hdP m))
      simp_rw [e]
      exact (hRμ m).2.sub ((hRσ m).2.const_mul c)
    exact tendsto_nhds_unique ((h3 m).comp (strictMono_subN b).tendsto_atTop) h1
  have hg_eq : ∀ m, seriesLim (g m) ω = seriesLim (d m) ω - seriesLim a ω := by
    intro m
    have h := (h3 m).sub h2
    have e : (fun n => psum (d m) n ω - psum a n ω) = fun n => psum (g m) n ω :=
      funext fun n => (psum_sub _ _ n ω).symm
    rw [e] at h
    exact tendsto_nhds_unique (h5 m) h
  have hX : ∀ m, ∫ x, field0 b ω (bumpTest m x) ∂μ =
      seriesLim a ω + seriesLim (g m) ω + c * (CircleAvg.mollAvg T m 0 1 - aω) := by
    intro m
    have e1 : ∫ x, field0 b ω (bumpTest m x) ∂μ = (∫ x, T (bumpTest m x) ∂μ) - aω * c := by
      simp_rw [field0_apply, CircleAvg.integral_bumpTest', mul_one]
      rw [integral_sub (hRμ m).1 (integrable_const _), integral_const, smul_eq_mul, ← hT, hcirc]
      ring
    rw [e1, hg_eq m, hd_eq m, hXσ m]
    ring
  have hconv : Tendsto (fun m => ∫ x, field0 b ω (bumpTest m x) ∂μ) atTop
      (𝓝 (seriesLim a ω)) := by
    simp_rw [hX]
    have h1 : Tendsto (fun m => c * (CircleAvg.mollAvg T m 0 1 - aω)) atTop (𝓝 (c * 0)) := by
      have := haω.sub_const aω
      rw [sub_self] at this
      exact this.const_mul c
    have h := (tendsto_const_nhds (x := seriesLim a ω)).add h4 |>.add h1
    rwa [add_zero, mul_zero, add_zero] at h
  have hmp : measPairing (field0 b ω) μ = seriesLim a ω := hconv.limUnder_eq
  rw [hmp]
  exact h2

end Realization

namespace Realization

/-! ## Compatibility names (cleanup W15)

Old names from the former `GaussianLQG/Field/Realization/CircleMeasure.lean`, about the uniform
measure `σ = circleMeasure 0 1`. Its content now comes from `GaussianLQG/Energy/Measures.lean` and
`GaussianLQG/Field/Frame/Circle.lean`; the names are kept so that code written against them still
compiles. -/

theorem circleMap_zero_one (θ : ℝ) : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by
  simp [circleMap]

theorem circleMeasure_apply {s : Set ℂ} (hs : MeasurableSet s) :
    circleMeasure 0 1 s =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * volume (Ioc 0 (2 * Real.pi) ∩ circleMap 0 1 ⁻¹' s) :=
  WNFrame.circleMeasure_apply 0 1 hs

theorem ballBound_circleMeasure : BallBound (circleMeasure 0 1) 2 1 := fun u r hr _ => by
  simpa using circleMeasure_ball_toReal_le one_pos 0 u hr.le

theorem circleMeasure_univ : circleMeasure 0 1 univ = 1 := measure_univ

alias circleMeasure_compl_closedBall := WNFrame.circleMeasure_compl_closedBall

theorem isRegular_circleMeasure : IsRegular (circleMeasure 0 1) :=
  GaussianLQG.isRegular_circleMeasure 0 one_pos

theorem integral_circleMeasure {f : ℂ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂circleMeasure 0 1 = Real.circleAverage f 0 1 :=
  GaussianLQG.integral_circleMeasure 0 1 hf.aestronglyMeasurable

end Realization
end GaussianLQG
