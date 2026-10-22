import HigherDimLQGMetric.Markov.Sigma
import HigherDimLQGMetric.LGF.Law
import LQGMetric.Field.MarkovGauss

/-!
# Orthogonal Gaussian split for an open set

This is the Hilbert-space part of D-M. It uses the already formalized Gaussian Hilbert space and
the orthogonality-to-independence theorem from `LQGMetric.Field.MarkovGauss`. The remaining
analytic task is to identify the projected exterior pairings with a continuous function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-- The mean-zero pairing process with the argument order used by the Gaussian-space API. -/
def markovPair (h : Ω → DistRd d) (φ : TestRd0 d) (ω : Ω) : ℝ := h ω φ.1

omit [IsProbabilityMeasure P] in
/-- Square integrability of each mean-zero pairing. -/
theorem markov_memLp_pair (hh : IsWholeSpaceLGF h P) (φ : TestRd0 d) :
    MemLp (markovPair h φ) 2 P :=
  (hh.gaussian.hasGaussianLaw_eval φ).memLp_two

/-- The mean-zero test obtained by centering a test supported in `V` at `ρ`. -/
def markovInsideTest (V : Opens (Rd d)) {ρ : TestRd d}
    (hρ : ∫ x, ρ x = 1) (φ : TestOn V) : TestRd0 d :=
  subMean hρ (testIncl V φ)

/-- The `L²` vector of an interior pairing. -/
def markovInsideVec (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d)) {ρ : TestRd d}
    (hρ : ∫ x, ρ x = 1) (φ : TestOn V) : Lp ℝ 2 P :=
  (markov_memLp_pair hh (markovInsideTest V hρ φ)).toLp
    (markovPair h (markovInsideTest V hρ φ))

/-- The closed span of the interior Gaussian pairings. -/
def markovInsideSpace (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d)) {ρ : TestRd d}
    (hρ : ∫ x, ρ x = 1) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (Set.range (markovInsideVec hh V hρ))).topologicalClosure

instance markovInsideSpace_hasOrthogonalProjection (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) :
    (markovInsideSpace hh V hρ).HasOrthogonalProjection := by
  unfold markovInsideSpace
  infer_instance

/-- The `L²` vector of an exterior pairing, centered at the same test `ρ`. -/
def markovOutsideVec (hh : IsWholeSpaceLGF h P) (O : Opens (Rd d)) {ρ : TestRd d}
    (hρ : ∫ x, ρ x = 1) (ψ : TestOn O) : Lp ℝ 2 P :=
  (markov_memLp_pair hh (markovInsideTest O hρ ψ)).toLp
    (markovPair h (markovInsideTest O hρ ψ))

/-- The exterior pairing after subtracting its projection onto interior pairings. -/
def markovResidualVec (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d)) {ρ : TestRd d}
    (hρ : ∫ x, ρ x = 1) (ψ : TestOn (extOpen V)) : Lp ℝ 2 P :=
  markovOutsideVec hh (extOpen V) hρ ψ -
    (markovInsideSpace hh V hρ).starProjection (markovOutsideVec hh (extOpen V) hρ ψ)

omit [IsProbabilityMeasure P] in
theorem markov_insideVec_mem (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) (φ : TestOn V) :
    markovInsideVec hh V hρ φ ∈ markovInsideSpace hh V hρ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, rfl⟩)

omit [IsProbabilityMeasure P] in
theorem markov_insideSpace_le_global (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) :
    markovInsideSpace hh V hρ ≤
      LQGMetric.MarkovGauss.gaussSpace (markovPair h) (markov_memLp_pair hh) := by
  unfold markovInsideSpace LQGMetric.MarkovGauss.gaussSpace
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro u ⟨φ, rfl⟩
  exact ⟨markovInsideTest V hρ φ, rfl⟩

omit [IsProbabilityMeasure P] in
theorem markov_residual_mem_global (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) (ψ : TestOn (extOpen V)) :
    markovResidualVec hh V hρ ψ ∈
      LQGMetric.MarkovGauss.gaussSpace (markovPair h) (markov_memLp_pair hh) := by
  unfold markovResidualVec
  apply Submodule.sub_mem
  · exact LQGMetric.MarkovGauss.toLp_mem_gaussSpace (markov_memLp_pair hh) _
  · exact markov_insideSpace_le_global hh V hρ
      ((markovInsideSpace hh V hρ).starProjection_apply_mem _)

omit [IsProbabilityMeasure P] in
theorem markov_residual_inner_inside (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) (ψ : TestOn (extOpen V)) (φ : TestOn V) :
    ⟪markovResidualVec hh V hρ ψ, markovInsideVec hh V hρ φ⟫ = 0 := by
  unfold markovResidualVec
  exact Submodule.inner_left_of_mem_orthogonal
    (markov_insideVec_mem hh V hρ φ)
    ((markovInsideSpace hh V hρ).sub_starProjection_mem_orthogonal _)

/-- Orthogonal projection makes all exterior residual pairings independent of all interior
pairings, on the original probability space. -/
theorem markov_residual_indep_inside (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) :
    IndepFun (fun ω (ψ : TestOn (extOpen V)) => (markovResidualVec hh V hρ ψ : Ω → ℝ) ω)
      (fun ω (φ : TestOn V) => markovPair h (markovInsideTest V hρ φ) ω) P := by
  exact LQGMetric.MarkovGauss.indepFun_of_inner_eq_zero hh.gaussian hh.centered
    (markov_memLp_pair hh) (fun ψ => markovResidualVec hh V hρ ψ)
    (markov_residual_mem_global hh V hρ) (markovInsideTest V hρ)
    (fun ψ φ => markov_residual_inner_inside hh V hρ ψ φ)

/-- The same independence statement against the actual sigma algebra of the recentered field
restricted to `V`. -/
theorem markov_residual_indep_fieldSigma (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) :
    Indep
      (MeasurableSpace.comap
        (fun ω (ψ : TestOn (extOpen V)) => (markovResidualVec hh V hρ ψ : Ω → ℝ) ω)
        MeasurableSpace.pi)
      (fieldSigmaRd (fun ω => recenter ρ (h ω)) V) P := by
  have hind := (IndepFun_iff_Indep _ _ P).mp (markov_residual_indep_inside hh V hρ)
  have he : (fun ω (φ : TestOn V) => markovPair h (markovInsideTest V hρ φ) ω) =
      (fun ω (φ : TestOn V) => restrictTo V (recenter ρ (h ω)) φ) := by
    funext ω φ
    rw [restrictTo_apply, recenter_apply]
    rfl
  rw [he] at hind
  rw [fieldSigmaRd, DistOn.measurableSpace, MeasurableSpace.comap_comp]
  exact hind

end HigherDimLQGMetric
