import HigherDimLQGMetric.LGF.BoxCov
import HigherDimLQGMetric.LGF.StochFubini
import HigherDimLQGMetric.Field.Measurable
import HigherDimLQGMetric.Frozen.IsWholeSpaceLGF

/-!
# The whole-space LGF exists as a random distribution (packet F2, target 1)

Source: `source/higher-dimensional-lqg-metric.pdf` l. 50–56 ([1] (1.1), §1.1); MA0 §5.2 block A1
("LGF realization from white noise as a random distribution; existence anchor"), MA0 Details (a)
D-WN, MA3 E8.

**Construction** (white-noise representation, made into a random distribution by an antiderivative):

1. `W`: a white noise on `L²(ℝ × ℝ^d)` (HigherDimLFPP's `exists_isWhiteNoise`, on `(ℕ → ℝ, stdP)`).
2. For bounded boundedly supported mean-zero `f`, `gramVec f ∈ L²(ℝ × ℝ^d)` with
   `⟪gramVec f, gramVec g⟫ = ∫∫ f(u) g(w) log|u − w|⁻¹` (`inner_gramVec`, from HigherDimLFPP's
   `scaleCov_eq_logCov`).
3. The antiderivative field `G(x) = W(gramVec (boxDens x))`, `boxDens x = 1_{[0,x]} − (∏ xᵢ) θ`, has
   `½`-Hölder `L²` increments, hence a continuous version `Y` (`exists_continuous_boxField`).
4. `h(ω) = (−1)^d (Y(·, ω)) ∘ ∂₁⋯∂_d`, i.e. `⟨h(ω), φ⟩ = (−1)^d ∫ Y(x, ω) ∂₁⋯∂_dφ(x) dx` — a
   distribution for every `ω` (`lgfOf`).
5. Stochastic Fubini (`ae_lgfOf_apply`): `⟨h, φ⟩ = W(gramVec (φ − (∫ φ) θ))` a.s. for every test
   function `φ`; for mean-zero `φ` this is `W(gramVec φ)`, so the mean-zero pairings form a centered
   Gaussian process with covariance `logCovRd` (`isWholeSpaceLGF_lgfOf`).

Main results: `exists_isWholeSpaceLGF` (target 1) and `exists_wn_realization` (the realization
together with its white noise and the a.s. pairing formula, for packets F3–F5); the law version
`exists_isWholeSpaceLGF_law` is in `LGF/NormLaw.lean`.

Port of LQGMetric's `Field/ExistGFF.lean`, `ExistDist.lean`, `ExistSFub2.lean` (whole-plane GFF:
heat-kernel white-noise vectors, rectangles in `ℂ`) to `ℝ^d` with HigherDimLFPP's band vectors and
boxes (ruling M10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The random distribution built from a continuous field -/

/-- `⟨lgfOf Y ω, φ⟩ = (−1)^d ∫ Y(x, ω) ∂₁⋯∂_dφ(x) dx`. -/
def lgfOf {Ω : Type*} (Y : Rd d → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) :
    DistRd d :=
  ((-1 : ℝ) ^ d) • (ofCont ⟨fun x => Y x ω, hYc ω⟩).comp (boxDeriv d)

theorem lgfOf_apply {Ω : Type*} (Y : Rd d → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω)
    (ω : Ω) (φ : TestRd d) :
    lgfOf Y hYc ω φ = (-1) ^ d * ∫ x, boxDeriv d φ x * Y x ω := by
  have h : lgfOf Y hYc ω φ = (-1 : ℝ) ^ d * ofCont ⟨fun x => Y x ω, hYc ω⟩ (boxDeriv d φ) := rfl
  rw [h, ofCont_apply]
  rfl

theorem measurable_lgfOf {Ω : Type*} [MeasurableSpace Ω] (Y : Rd d → Ω → ℝ)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) :
    Measurable (lgfOf Y hYc) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  simp only [lgfOf_apply]
  have hj : Measurable (Function.uncurry Y) :=
    measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm
  have hF : Measurable fun p : Rd d × Ω => boxDeriv d φ p.1 * Y p.1 p.2 :=
    ((boxDeriv d φ).continuous.measurable.comp measurable_fst).mul hj
  exact (hF.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable.const_mul _

/-! ## Stochastic Fubini -/

/-- `φ − (∫ φ) θ`, the mean-zero part of `φ` relative to `θ`. -/
def subTheta (φ : TestRd d) (u : Rd d) : ℝ := φ u - (∫ y, φ y) * theta d u

theorem exists_isBddSupp_subTheta (φ : TestRd d) : ∃ M D, IsBddSupp (subTheta φ) M D := by
  have hc : Continuous (subTheta φ) :=
    φ.continuous.sub (continuous_const.mul (theta d).continuous)
  have hs : HasCompactSupport (subTheta φ) :=
    φ.hasCompactSupport.sub ((theta d).hasCompactSupport.mul_left)
  exact exists_isBddSupp_of_continuous hc hs

theorem integral_subTheta (φ : TestRd d) : ∫ u, subTheta φ u = 0 := by
  unfold subTheta
  rw [integral_sub (integrable_testOn φ) ((integrable_testOn _).const_mul _), integral_const_mul,
    integral_theta, mul_one, sub_self]

theorem subTheta_of_integral_eq_zero {φ : TestRd d} (hφ : ∫ y, φ y = 0) :
    subTheta φ = ⇑φ := by
  funext u
  simp only [subTheta, hφ, zero_mul, sub_zero]

section Realization

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : HigherDimLFPP.WN d → Ω → ℝ}
  (hW : HigherDimLFPP.IsWhiteNoise P W) {Y : Rd d → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x))
  (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (gramVec (boxDens x.ofLp)))
include hW hYm hYW

/-- **Stochastic Fubini** (`d ≥ 1`): for every test function `φ`, almost surely
`⟨lgfOf Y ω, φ⟩ = W(gramVec (φ − (∫ φ) θ))(ω)`. -/
theorem ae_lgfOf_apply [NeZero d] (φ : TestRd d) :
    (fun ω => lgfOf Y hYc ω φ) =ᵐ[P] W (gramVec (subTheta φ)) := by
  have := hW.isProbabilityMeasure
  have hv : ∀ R : ℝ, ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ‖gramVec (boxDens x.ofLp)‖ ^ 2 ≤ C :=
    exists_norm_gramVec_boxDens_sq_le
  set ψ : Rd d → ℝ := fun x => boxDeriv d φ x with hψ
  have hψc : Continuous ψ := (boxDeriv d φ).continuous
  have hψs : HasCompactSupport ψ := (boxDeriv d φ).hasCompactSupport
  obtain ⟨Mφ, Dφ, hφS⟩ := exists_isBddSupp_subTheta φ
  have hφ0 := integral_subTheta φ
  set A : Ω → ℝ := fun ω => ∫ x, ψ x * Y x ω with hA
  set B : Ω → ℝ := W (gramVec (subTheta φ)) with hB
  set T : ℝ := logCovF (subTheta φ) (subTheta φ) with hT
  set s : ℝ := (-1) ^ d with hs
  have hs2 : s * s = 1 := by rw [hs, ← pow_two, ← pow_mul, mul_comm, pow_mul]; simp
  have hAL : MemLp A 2 P := memLp_integral_mul_Y hW hYc hYm hYW hv hψc hψs
  have hBL : MemLp B 2 P := hW.memLp _ 2 (by norm_num)
  -- `E[A W(gramVec f)] = s ⟪gramVec (subTheta φ), gramVec f⟫` for mean-zero bounded `f`
  have hAW : ∀ (f : Rd d → ℝ) (M D : ℝ), IsBddSupp f M D → ∫ z, f z = 0 →
      ∫ ω, A ω * W (gramVec f) ω ∂P = s * logCovF (subTheta φ) f := by
    intro f M D hf hf0
    rw [hA, integral_integral_mul_Y_mul hW hYc hYm hYW hv hψc hψs (hW.memLp _ 2 (by norm_num))]
    have e : ∀ x : Rd d, ψ x * ∫ ω, Y x ω * W (gramVec f) ω ∂P =
        boxDeriv d φ x * logCovF (boxDens x.ofLp) f := fun x => by
      obtain ⟨Mb, hMb⟩ := exists_isBddSupp_boxDens (d := d) (norm_nonneg x.ofLp)
      have hq : ∀ i, |x.ofLp i| ≤ ‖x.ofLp‖ := fun i => by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x.ofLp i
      rw [integral_Y_mul_W hW hYW x, inner_gramVec (hMb _ hq) (integral_boxDens _) hf hf0]
    simp_rw [e]
    rw [integral_boxDeriv_mul_logCovF φ hf]
    rfl
  have hAB : ∫ ω, A ω * B ω ∂P = s * T := hAW _ _ _ hφS hφ0
  have hAA : ∫ ω, A ω * A ω ∂P = T := by
    rw [hA, integral_integral_mul_Y_mul hW hYc hYm hYW hv hψc hψs hAL]
    have e : ∀ x : Rd d, ψ x * ∫ ω, Y x ω * A ω ∂P =
        s * (boxDeriv d φ x * logCovF (boxDens x.ofLp) (subTheta φ)) := fun x => by
      obtain ⟨Mb, hMb⟩ := exists_isBddSupp_boxDens (d := d) (norm_nonneg x.ofLp)
      have hq : ∀ i, |x.ofLp i| ≤ ‖x.ofLp‖ := fun i => by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x.ofLp i
      rw [integral_Y_mul hYW x]
      have e2 : ∫ ω, W (gramVec (boxDens x.ofLp)) ω * A ω ∂P =
          ∫ ω, A ω * W (gramVec (boxDens x.ofLp)) ω ∂P := by
        congr 1; funext ω; ring
      rw [e2, hAW _ _ _ (hMb _ hq) (integral_boxDens _), logCovF_comm]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_boxDeriv_mul_logCovF φ hφS, ← mul_assoc, hs2, one_mul]
    rfl
  have hBB : ∫ ω, B ω * B ω ∂P = T := by
    rw [hB, wn_integral_mul hW, inner_gramVec hφS hφ0 hφS hφ0]
  -- `E[(s A − B)²] = 0`
  have hiAA : Integrable (fun ω => A ω * A ω) P := hAL.integrable_mul hAL
  have hiAB : Integrable (fun ω => A ω * B ω) P := hAL.integrable_mul hBL
  have hiBB : Integrable (fun ω => B ω * B ω) P := hBL.integrable_mul hBL
  have hsq : ∫ ω, (s * A ω - B ω) ^ 2 ∂P = 0 := by
    have e : ∀ ω, (s * A ω - B ω) ^ 2 = (s * s) * (A ω * A ω) - 2 * s * (A ω * B ω) + B ω * B ω :=
      fun ω => by ring
    simp_rw [e]
    have i1 : Integrable (fun ω => (s * s) * (A ω * A ω) - 2 * s * (A ω * B ω)) P :=
      (hiAA.const_mul _).sub (hiAB.const_mul _)
    rw [integral_add i1 hiBB, integral_sub (hiAA.const_mul _) (hiAB.const_mul _),
      integral_const_mul, integral_const_mul, hAA, hAB, hBB, hs2]
    have : 2 * s * (s * T) = 2 * (s * s) * T := by ring
    rw [this, hs2]
    ring
  have hint : Integrable (fun ω => (s * A ω - B ω) ^ 2) P :=
    ((hAL.const_mul s).sub hBL).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (s * A ω - B ω)) hint).mp hsq
  filter_upwards [h0] with ω hω
  have h1 : (s * A ω - B ω) ^ 2 = 0 := hω
  have h2 : s * A ω = B ω := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    linarith
  rw [lgfOf_apply]
  exact h2

/-- **The white-noise realization is a whole-space LGF** (`d ≥ 1`). -/
theorem isWholeSpaceLGF_lgfOf [NeZero d] : IsWholeSpaceLGF (lgfOf Y hYc) P := by
  have := hW.isProbabilityMeasure
  have hae : ∀ φ : TestRd0 d, (fun ω => lgfOf Y hYc ω φ.1) =ᵐ[P] W (gramVec φ.1) := fun φ => by
    have h := ae_lgfOf_apply hW hYc hYm hYW φ.1
    rwa [subTheta_of_integral_eq_zero φ.2] at h
  have hmean : ∀ φ : TestRd0 d, ∫ ω, lgfOf Y hYc ω φ.1 ∂P = 0 := fun φ => by
    rw [integral_congr_ae (hae φ), hW.integral_eq_zero]
  refine ⟨measurable_lgfOf Y hYc hYm, ?_, hmean, ?_⟩
  · exact (hW.isGaussianProcess_comp fun φ : TestRd0 d => gramVec (φ.1 : Rd d → ℝ)).congr
      fun φ => (hae φ).symm
  · intro φ ψ
    obtain ⟨M₁, D₁, h₁⟩ := exists_isBddSupp_testOn φ.1
    obtain ⟨M₂, D₂, h₂⟩ := exists_isBddSupp_testOn ψ.1
    have hm1 := (hW.memLp (gramVec φ.1) 2 (by norm_num)).ae_eq (hae φ).symm
    have hm2 := (hW.memLp (gramVec ψ.1) 2 (by norm_num)).ae_eq (hae ψ).symm
    rw [covariance_eq_sub hm1 hm2, hmean φ, zero_mul, sub_zero,
      integral_congr_ae ((hae φ).mul (hae ψ))]
    simp only [Pi.mul_apply]
    rw [wn_integral_mul hW, inner_gramVec h₁ φ.2 h₂ ψ.2, logCovRd_eq_logCovF h₁ h₂]

end Realization

/-! ## Existence -/

/-- **The white-noise realization of the whole-space LGF** (`d ≥ 1`): on `(ℕ → ℝ, stdP)` there are a
white noise `W` and a random distribution `h` which is a whole-space LGF, with
`⟨h, φ⟩ = W(gramVec (φ − (∫ φ) θ))` almost surely for every test function `φ`. -/
theorem exists_wn_realization (hd : 1 ≤ d) :
    ∃ (W : HigherDimLFPP.WN d → (ℕ → ℝ) → ℝ) (h : (ℕ → ℝ) → DistRd d),
      HigherDimLFPP.IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧
      IsWholeSpaceLGF h LQGDimension.ExistAsm.stdP ∧
      ∀ φ : TestRd d, (fun ω => h ω φ) =ᵐ[LQGDimension.ExistAsm.stdP] W (gramVec (subTheta φ)) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_continuous_boxField hW
  exact ⟨W, lgfOf Y hYc, hW, isWholeSpaceLGF_lgfOf hW hYc hYm hYW,
    ae_lgfOf_apply hW hYc hYm hYW⟩

/-- **Existence of the whole-space LGF as a random distribution** (target 1; `d ≥ 1`). -/
theorem exists_isWholeSpaceLGF (hd : 1 ≤ d) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : Ω → DistRd d),
      IsProbabilityMeasure P ∧ IsWholeSpaceLGF h P := by
  obtain ⟨W, h, hW, hh, -⟩ := exists_wn_realization hd
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, h, hW.isProbabilityMeasure, hh⟩

end HigherDimLQGMetric
