import HigherDimLQGMetric.Markov.Norm
import HigherDimLQGMetric.CM.Direction

/-!
# Interior Riesz representatives from the Cameron–Martin Gaussian variable

`lgf_cameronMartin_aug` constructs a genuine Gaussian random variable whose covariance with
every mean-zero LGF pairing is integration against a compact smooth shift. Projecting this
variable onto the interior Gaussian space gives the bounded functional needed for the open-set
Markov decomposition, without repeating the private Hahn–Banach construction in `CM.Direction`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped RealInnerProductSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- Every Cameron–Martin shift has an interior projected Gaussian vector with the correct
covariances against all recentered tests supported in `V`. -/
theorem markov_exists_projected_cmVec (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) (F : C(Rd d, ℝ)) {C : ℝ}
    (hF : IsCMBounded F C) :
    ∃ y : Lp ℝ 2 P, y ∈ markovInsideSpace hh V hρ ∧ ‖y‖ ≤ |C| ∧
      ∀ φ : TestOn V, ⟪y, markovInsideVec hh V hρ φ⟫ =
        ∫ x, F x * (markovInsideTest V hρ φ).1 x := by
  obtain ⟨Y, hYm, hYsq, hYcov, hYgp, _, _⟩ := lgf_cameronMartin_aug hh F hF
  have hY2 : MemLp Y 2 P := (hYgp.hasGaussianLaw_eval (Sum.inl ())).memLp_two
  let u : Lp ℝ 2 P := hY2.toLp Y
  let y : Lp ℝ 2 P := (markovInsideSpace hh V hρ).starProjection u
  have huSq : ‖u‖ ^ 2 = ∫ ω, Y ω ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hY2.coeFn_toLp] with ω hω
    change (u : Ω → ℝ) ω = Y ω at hω
    rw [hω]
    simp [pow_two]
  have hynorm : ‖y‖ ≤ |C| := by
    have hp := (markovInsideSpace hh V hρ).norm_starProjection_apply_le u
    have hp2 := pow_le_pow_left₀ (norm_nonneg y) hp 2
    rw [huSq] at hp2
    nlinarith [abs_nonneg C, norm_nonneg y, sq_abs C]
  refine ⟨y, (markovInsideSpace hh V hρ).starProjection_apply_mem u, hynorm, fun φ => ?_⟩
  have horth := (markovInsideSpace hh V hρ).starProjection_inner_eq_zero u
    (markovInsideVec hh V hρ φ) (markov_insideVec_mem hh V hρ φ)
  have hyu : ⟪y, markovInsideVec hh V hρ φ⟫ =
      ⟪u, markovInsideVec hh V hρ φ⟫ := by
    rw [inner_sub_left] at horth
    exact sub_eq_zero.mp horth |>.symm
  rw [hyu, L2.inner_def]
  have haeY : (u : Ω → ℝ) =ᵐ[P] Y := hY2.coeFn_toLp
  have haeφ : (markovInsideVec hh V hρ φ : Ω → ℝ) =ᵐ[P]
      (fun ω => h ω (markovInsideTest V hρ φ).1) :=
    (markov_memLp_pair hh (markovInsideTest V hρ φ)).coeFn_toLp
  rw [← hYcov (markovInsideTest V hρ φ)]
  apply integral_congr_ae
  filter_upwards [haeY, haeφ] with ω hYω hφω
  simp [hYω, hφω, mul_comm]

omit [IsProbabilityMeasure P] in
/-- A vector in the interior Gaussian space is determined by its inner products with the
generating interior pairings. -/
theorem markov_insideVec_ext (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) {y z : Lp ℝ 2 P}
    (hy : y ∈ markovInsideSpace hh V hρ) (hz : z ∈ markovInsideSpace hh V hρ)
    (he : ∀ φ : TestOn V,
      ⟪y, markovInsideVec hh V hρ φ⟫ = ⟪z, markovInsideVec hh V hρ φ⟫) :
    y = z := by
  let K : Submodule ℝ (Lp ℝ 2 P) :=
    Submodule.span ℝ (Set.range (markovInsideVec hh V hρ))
  have horth : y - z ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨φ, rfl⟩ := hx
        simpa only [inner_sub_left, sub_eq_zero] using he φ
    | zero => simp
    | add x t hx ht ihx iht => simp [inner_add_right, ihx, iht]
    | smul a x hx ih => simp [inner_smul_right, ih]
  have horth' : y - z ∈ (markovInsideSpace hh V hρ)ᗮ := by
    simpa only [markovInsideSpace, K, Submodule.orthogonal_closure] using horth
  have hmem : y - z ∈ markovInsideSpace hh V hρ := Submodule.sub_mem _ hy hz
  have hzero := Submodule.inner_left_of_mem_orthogonal hmem horth'
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

end HigherDimLQGMetric
