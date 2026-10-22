import HigherDimLQGMetric.Sphere.Mol
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.LGF.NormLaw
import LQGMetric.Field.CircleAvgLimit

/-!
# Covariances of mollified sphere averages and the a.s. existence of `h_r(z)`

Packet F3 (Phase A, block A1), target 1 (core). MA0 Details (a) D-F3; the frozen characterization
`sphereAvg_spec` (MA1 item 1, MA4 note 4); F2's handoff §7 ("Notes for F3").

For an LGF `h` (any probability space) and nonnegative test functions `φ₁, φ₂` (resp. `ψ₁, ψ₂`)
of equal masses, `⟨h, φ₁ - φ₂⟩` is a mean-zero pairing and

`Cov(⟨h, φ₁ - φ₂⟩, ⟨h, ψ₁ - ψ₂⟩) = logCov(φ₁ dz, φ₂ dz, ψ₁ dz, ψ₂ dz)`

(`IsWholeSpaceLGF.covariance_sub_sub`): the frozen covariance `logCovRd` equals F2's `logCovF`
(Fubini) and, for nonnegative densities, HigherDimLFPP's four-term `logCov` of the measures
`posM φ = φ dz` (`logCovF_sub_sub_eq_logCov`). For the mollified sphere bumps
`posM (sphMol ε z r) = sphLaw r z ε`, so the transport bound of `Sphere/Law.lean` gives

`E[(h(sphMol ε z r) - h(sphMol ε' z' r'))²] ≤ C (‖z - z'‖ + |r - r'| + |ε - ε'|) / min(r, r')`

(`IsWholeSpaceLGF.integral_sq_sphMol_sub_le`, `d ≥ 2`, `ε, ε', r, r' > 0`). With `ε = 2^{-n-1}`,
`ε' = 2^{-n}` the increments of `n ↦ sphereAvgSeq h r z n` have `L²` norms `≲ 2^{-n/2}`, so
(Chebyshev + Borel–Cantelli, LQGMetric's `ae_tendsto_of_sq_incr_le`) the mollified sphere
averages converge almost surely (`IsWholeSpaceLGF.ae_exists_tendsto_sphereAvgSeq`).

`sphereAvg_spec_holds` and `normLGFLaw_spec_holds` have exactly the statements of the frozen anchors
`sphereAvg_spec` and `normLGFLaw_spec` (the anchors' providers `Assembly/SphereAvgSpec.lean`,
`Assembly/NormLGFLawSpec.lean` can declare their `_impl` as these terms).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### `logCovF` of nonnegative densities as HigherDimLFPP's `logCov` -/

theorem logCovF_eq_integral_posM {f g : Rd d → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    logCovF f g = ∫ p, -Real.log ‖p.1 - p.2‖ ∂((posM f).prod (posM g)) := by
  rw [integral_prod_posM hf hg, logCovF]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [max_eq_left (hf0 p.1), max_eq_left (hg0 p.2)]

/-- **`logCovF` of differences of nonnegative densities is HigherDimLFPP's `logCov`.** -/
theorem logCovF_sub_sub_eq_logCov [NeZero d] {f₁ f₂ g₁ g₂ : Rd d → ℝ}
    {M₁ D₁ M₂ D₂ M₃ D₃ M₄ D₄ : ℝ} (h₁ : IsBddSupp f₁ M₁ D₁) (h₂ : IsBddSupp f₂ M₂ D₂)
    (h₃ : IsBddSupp g₁ M₃ D₃) (h₄ : IsBddSupp g₂ M₄ D₄) (p₁ : ∀ x, 0 ≤ f₁ x)
    (p₂ : ∀ x, 0 ≤ f₂ x) (p₃ : ∀ x, 0 ≤ g₁ x) (p₄ : ∀ x, 0 ≤ g₂ x) :
    logCovF (f₁ - f₂) (g₁ - g₂) =
      HigherDimLFPP.logCov (posM f₁) (posM f₂) (posM g₁) (posM g₂) := by
  have hg : IsBddSupp (g₁ - g₂) (M₃ + M₄) (max D₃ D₄) :=
    (h₃.mono le_rfl (le_max_left _ _)).sub (h₄.mono le_rfl (le_max_right _ _))
  rw [logCovF_sub_left h₁ h₂ hg, logCovF_sub_right h₁ h₃ h₄, logCovF_sub_right h₂ h₃ h₄,
    HigherDimLFPP.logCov,
    logCovF_eq_integral_posM h₁.measurable h₃.measurable p₁ p₃,
    logCovF_eq_integral_posM h₁.measurable h₄.measurable p₁ p₄,
    logCovF_eq_integral_posM h₂.measurable h₃.measurable p₂ p₃,
    logCovF_eq_integral_posM h₂.measurable h₄.measurable p₂ p₄]
  ring

/-! ### Mean-zero differences of test functions -/

theorem integral_sub_testRd (φ ψ : TestRd d) : ∫ x, (φ - ψ) x = (∫ x, φ x) - ∫ x, ψ x := by
  simp_rw [sub_apply]
  exact integral_sub (integrable_testOn φ) (integrable_testOn ψ)

/-- `φ - ψ` as a mean-zero test function when `∫ φ = ∫ ψ`. -/
def testSub0 (φ ψ : TestRd d) (h : ∫ x, φ x = ∫ x, ψ x) : TestRd0 d :=
  ⟨φ - ψ, by rw [integral_sub_testRd, h, sub_self]⟩

@[simp]
theorem testSub0_val (φ ψ : TestRd d) (h : ∫ x, φ x = ∫ x, ψ x) :
    (testSub0 φ ψ h).1 = φ - ψ := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- `E[⟨h, φ⟩²] = logCovRd φ φ` for mean-zero `φ` (port of 2D `integral_sq_pair`). -/
theorem IsWholeSpaceLGF.integral_sq_apply (hh : IsWholeSpaceLGF h P) (φ : TestRd0 d) :
    Integrable (fun ω => h ω φ.1 ^ 2) P ∧ ∫ ω, h ω φ.1 ^ 2 ∂P = logCovRd φ.1 φ.1 := by
  have hG := hh.gaussian.hasGaussianLaw_eval φ
  refine ⟨hG.memLp_two.integrable_sq, ?_⟩
  rw [← hh.covariance_eq φ φ, covariance_self hG.aemeasurable,
    variance_eq_integral hG.aemeasurable, hh.centered φ]
  simp

theorem IsWholeSpaceLGF.hasGaussianLaw_sub (hh : IsWholeSpaceLGF h P) {φ ψ : TestRd d}
    (hm : ∫ x, φ x = ∫ x, ψ x) : HasGaussianLaw (fun ω => h ω φ - h ω ψ) P := by
  have hG := hh.gaussian.hasGaussianLaw_eval (testSub0 φ ψ hm)
  have e : (fun ω => h ω (testSub0 φ ψ hm).1) = fun ω => h ω φ - h ω ψ := by
    funext ω; rw [testSub0_val, map_sub]
  rw [e] at hG
  exact hG

theorem IsWholeSpaceLGF.integral_sub_eq_zero (hh : IsWholeSpaceLGF h P) {φ ψ : TestRd d}
    (hm : ∫ x, φ x = ∫ x, ψ x) : ∫ ω, (h ω φ - h ω ψ) ∂P = 0 := by
  have := hh.centered (testSub0 φ ψ hm)
  simp only [testSub0_val, map_sub] at this
  exact this

/-- **Covariances of differences of nonnegative test functions**:
`Cov(⟨h, φ₁ - φ₂⟩, ⟨h, ψ₁ - ψ₂⟩) = logCov(φ₁ dz, φ₂ dz, ψ₁ dz, ψ₂ dz)`. -/
theorem IsWholeSpaceLGF.covariance_sub_sub [NeZero d] (hh : IsWholeSpaceLGF h P)
    {φ₁ φ₂ ψ₁ ψ₂ : TestRd d} (hφ : ∫ x, φ₁ x = ∫ x, φ₂ x) (hψ : ∫ x, ψ₁ x = ∫ x, ψ₂ x)
    (p₁ : ∀ x, 0 ≤ φ₁ x) (p₂ : ∀ x, 0 ≤ φ₂ x) (p₃ : ∀ x, 0 ≤ ψ₁ x) (p₄ : ∀ x, 0 ≤ ψ₂ x) :
    cov[fun ω => h ω φ₁ - h ω φ₂, fun ω => h ω ψ₁ - h ω ψ₂; P] =
      HigherDimLFPP.logCov (posM φ₁) (posM φ₂) (posM ψ₁) (posM ψ₂) := by
  have hc := hh.covariance_eq (testSub0 φ₁ φ₂ hφ) (testSub0 ψ₁ ψ₂ hψ)
  simp only [testSub0_val, map_sub] at hc
  rw [hc]
  obtain ⟨M₁, D₁, b₁⟩ := exists_isBddSupp_testOn φ₁
  obtain ⟨M₂, D₂, b₂⟩ := exists_isBddSupp_testOn φ₂
  obtain ⟨M₃, D₃, b₃⟩ := exists_isBddSupp_testOn ψ₁
  obtain ⟨M₄, D₄, b₄⟩ := exists_isBddSupp_testOn ψ₂
  have e1 : (⇑(φ₁ - φ₂) : Rd d → ℝ) = (fun x => φ₁ x) - fun x => φ₂ x := by
    funext x; rw [sub_apply]; rfl
  have e2 : (⇑(ψ₁ - ψ₂) : Rd d → ℝ) = (fun x => ψ₁ x) - fun x => ψ₂ x := by
    funext x; rw [sub_apply]; rfl
  have hb1 : IsBddSupp (⇑(φ₁ - φ₂)) (M₁ + M₂) (max D₁ D₂) := by
    rw [e1]; exact (b₁.mono le_rfl (le_max_left _ _)).sub (b₂.mono le_rfl (le_max_right _ _))
  have hb2 : IsBddSupp (⇑(ψ₁ - ψ₂)) (M₃ + M₄) (max D₃ D₄) := by
    rw [e2]; exact (b₃.mono le_rfl (le_max_left _ _)).sub (b₄.mono le_rfl (le_max_right _ _))
  rw [logCovRd_eq_logCovF hb1 hb2, e1, e2,
    logCovF_sub_sub_eq_logCov b₁ b₂ b₃ b₄ p₁ p₂ p₃ p₄]

/-- The second moment of a difference of nonnegative test functions of equal masses. -/
theorem IsWholeSpaceLGF.integral_sq_sub [NeZero d] (hh : IsWholeSpaceLGF h P)
    {φ ψ : TestRd d} (hm : ∫ x, φ x = ∫ x, ψ x) (p₁ : ∀ x, 0 ≤ φ x) (p₂ : ∀ x, 0 ≤ ψ x) :
    Integrable (fun ω => (h ω φ - h ω ψ) ^ 2) P ∧
      ∫ ω, (h ω φ - h ω ψ) ^ 2 ∂P =
        HigherDimLFPP.logCov (posM φ) (posM ψ) (posM φ) (posM ψ) := by
  have hG := hh.hasGaussianLaw_sub hm
  refine ⟨hG.memLp_two.integrable_sq, ?_⟩
  rw [← hh.covariance_sub_sub hm hm p₁ p₂ p₁ p₂, covariance_self hG.aemeasurable,
    variance_eq_integral hG.aemeasurable, hh.integral_sub_eq_zero hm]
  simp

/-! ### Mollified sphere bumps -/

/-- **The basic `L²` estimate** (`d ≥ 2`): for `ε, ε', r, r' > 0`,
`E[(h(sphMol ε z r) - h(sphMol ε' z' r'))²] ≤ C (‖z - z'‖ + |r - r'| + |ε - ε'|) / min(r, r')`,
with `C = C(d)` (independent of the LGF). -/
theorem exists_integral_sq_sphMol_sub_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {ε ε' r r' : ℝ}, 0 < ε → 0 < ε' → 0 < r → 0 < r' →
        ∀ z z' : Rd d,
          Integrable (fun ω => (h ω (sphMol ε z r) - h ω (sphMol ε' z' r')) ^ 2) P ∧
          HigherDimLFPP.logCov (sphLaw r z ε) (sphLaw r' z' ε') (sphLaw r z ε) (sphLaw r' z' ε') =
            ∫ ω, (h ω (sphMol ε z r) - h ω (sphMol ε' z' r')) ^ 2 ∂P ∧
          ∫ ω, (h ω (sphMol ε z r) - h ω (sphMol ε' z' r')) ^ 2 ∂P ≤
            C * (‖z - z'‖ + |r - r'| + |ε - ε'|) / min r r' := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_logCov_sphLaw_le hd
  refine ⟨C, hC0, fun {Ω} _ {P} {h} hh {ε ε' r r'} hε hε' hr hr' z z' => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have : NeZero d := ⟨by omega⟩
  have hm : ∫ x, sphMol ε z r x = ∫ x, sphMol ε' z' r' x := by
    rw [integral_sphMol hd1 hε, integral_sphMol hd1 hε']
  obtain ⟨hi, he⟩ := hh.integral_sq_sub hm (sphMol_nonneg hε z r) (sphMol_nonneg hε' z' r')
  rw [posM_sphMol hd1 hε, posM_sphMol hd1 hε'] at he
  refine ⟨hi, he.symm, ?_⟩
  rw [he]
  have hb := hC r r' r r' hr hr' hr hr' z z' z z' ε ε' ε ε'
  set u := ‖z - z'‖ + |r - r'| + |ε - ε'| with hu
  have hu0 : 0 ≤ u := by positivity
  rw [Real.sqrt_mul_self hu0] at hb
  exact (le_abs_self _).trans hb

/-- `sphereAvgSeq h r z n = h (sphMol 2^{-n} z r)`. -/
theorem sphereAvgSeq_eq_apply_sphMol (g : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq g r z n = g (sphMol ((2 : ℝ) ^ n)⁻¹ z r) := by
  rw [sphMol_two_pow_inv, sphereAvgSeq_eq_apply_sphBump]

/-- **A.s. existence of the sphere-average limit for an LGF** (`d ≥ 2`, `r > 0`). -/
theorem IsWholeSpaceLGF.ae_exists_tendsto_sphereAvgSeq (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∀ᵐ ω ∂P, ∃ a, Tendsto (sphereAvgSeq (h ω) r z) atTop (𝓝 a) := by
  have := hh.gaussian.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphMol_sub_le hd
  have key : ∀ n : ℕ, Integrable (fun ω => (sphereAvgSeq (h ω) r z (n + 1) -
        sphereAvgSeq (h ω) r z n) ^ 2) P ∧
      ∫ ω, (sphereAvgSeq (h ω) r z (n + 1) - sphereAvgSeq (h ω) r z n) ^ 2 ∂P ≤
        C / (2 * r) * (1 / 2) ^ n := by
    intro n
    simp_rw [sphereAvgSeq_eq_apply_sphMol]
    obtain ⟨hi, -, hb⟩ := hC hh (ε := ((2 : ℝ) ^ (n + 1))⁻¹) (ε' := ((2 : ℝ) ^ n)⁻¹)
      (by positivity) (by positivity) hr hr z z
    refine ⟨hi, hb.trans (le_of_eq ?_)⟩
    have e : |((2 : ℝ) ^ (n + 1))⁻¹ - ((2 : ℝ) ^ n)⁻¹| = (1 / 2) ^ n * (1 / 2) := by
      rw [← inv_pow, ← inv_pow, pow_succ, one_div,
        show (2 : ℝ)⁻¹ ^ n * 2⁻¹ - 2⁻¹ ^ n = -(2⁻¹ ^ n * 2⁻¹) by ring, abs_neg,
        abs_of_pos (by positivity)]
    rw [sub_self, norm_zero, sub_self, abs_zero, zero_add, zero_add, min_self, e]
    ring
  exact LQGMetric.CircleAvg.ae_tendsto_of_sq_incr_le (X := fun n ω => sphereAvgSeq (h ω) r z n)
    (fun n => (key n).1) (by norm_num) (by norm_num) fun n => (key n).2

/-! ### The two sanity anchors (exact frozen statements) -/

/-- **The frozen statement of `sphereAvg_spec`, proved**: for an LGF plus a continuous function, the
limit defining `h_r(z)` exists almost surely (`d ≥ 2`, `r > 0`, every `z`). The LGF part converges
a.s. (`IsWholeSpaceLGF.ae_exists_tendsto_sphereAvgSeq`); the continuous part converges for every `ω`
(F1's `exists_tendsto_sphereAvgSeq_addFun_iff`). -/
theorem sphereAvg_spec_holds :
    ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u)) ∂(unitSphereProb d))
          atTop (𝓝 (sphereAvg (h ω) r z)) := by
  intro d hd Ω _ P _ h hh r hr z
  obtain ⟨-, f, -, hlgf⟩ := hh
  filter_upwards [hlgf.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω hω
  have e : h ω = addFun (h ω - ofCont (f ω)) (f ω) := by rw [addFun_def, sub_add_cancel]
  have hconv : ∃ b, Tendsto (sphereAvgSeq (h ω) r z) atTop (𝓝 b) := by
    rw [e]
    exact (exists_tendsto_sphereAvgSeq_addFun_iff _ _ _ _).2 hω
  exact tendsto_sphereAvgSeq_sphereAvg hconv

/-- **The frozen statement of `normLGFLaw_spec`, proved** (F2's reduction
`normLGFLaw_spec_of_sphereAvg_spec'` applied to `sphereAvg_spec_holds`). -/
theorem normLGFLaw_spec_holds :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ →
        μ = normLGFLaw d :=
  normLGFLaw_spec_of_sphereAvg_spec' sphereAvg_spec_holds

end HigherDimLQGMetric
