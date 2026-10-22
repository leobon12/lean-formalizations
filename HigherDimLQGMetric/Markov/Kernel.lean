import HigherDimLQGMetric.Markov.Cutoff

/-!
# Exterior point functionals on the interior Gaussian space

The logarithmic covariance kernel restricted to a bounded interior open set is represented by an
interior `L²` vector at each exterior point. The cutoff disappears from the covariance formula
because all interior mean-zero tests are supported in `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped RealInnerProductSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The formal covariance with a point evaluation outside `V` is a bounded functional on the
interior Gaussian space. The representative is independent of the cutoff used to construct it. -/
theorem markov_exists_pointVec (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x : Rd d) (hx : x ∈ extOpen V) :
    ∃ Z : Lp ℝ 2 P, Z ∈ markovInsideSpace hh V hρ ∧
      (∃ C : ℝ, 0 ≤ C ∧ ‖Z‖ ≤ C) ∧
      ∀ φ : TestOn V,
        ⟪Z, markovInsideVec hh V hρ φ⟫ =
          ∫ y, (-Real.log ‖x - y‖ - markovLogPot ρ y) *
            (markovInsideTest V hρ φ).1 y := by
  obtain ⟨χ, hχ, hχc, hχ1, hχ0⟩ := markov_exists_cutoff V hVb hx
  let f : Rd d → ℝ := markovCutKernel ρ χ x
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    markov_contDiff_cutKernel hd ρ x hχ hχ0
  have hfc : HasCompactSupport f := markov_hasCompactSupport_cutKernel ρ x hχc
  obtain ⟨C, hC, hCM⟩ := exists_isCMBounded hd hf hfc
  let F : C(Rd d, ℝ) := ⟨f, hf.continuous⟩
  obtain ⟨Z, hZ, hZn, hZcov⟩ := markov_exists_projected_cmVec hh V hρ F hCM
  refine ⟨Z, hZ, ⟨C, hC, by simpa only [abs_of_nonneg hC] using hZn⟩, fun φ => ?_⟩
  rw [hZcov]
  apply integral_congr_ae
  refine ae_of_all _ fun y => ?_
  by_cases hy : y ∈ V
  · have hχy : χ y = 1 := hχ1 y (subset_closure hy)
    simp [F, f, markovCutKernel, hχy]
  · have hy0 : (markovInsideTest V hρ φ).1 y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hy (markov_insideTest_tsupport V hρ hρV φ ht))
    simp [hy0]

/-- The unique interior Riesz vector of the normalized exterior point functional. -/
def markovPointVec (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x : Rd d) (hx : x ∈ extOpen V) : Lp ℝ 2 P :=
  Classical.choose (markov_exists_pointVec hd hh V hVb hρ hρV x hx)

theorem markovPointVec_mem (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x : Rd d) (hx : x ∈ extOpen V) :
    markovPointVec hd hh V hVb hρ hρV x hx ∈ markovInsideSpace hh V hρ :=
  (Classical.choose_spec (markov_exists_pointVec hd hh V hVb hρ hρV x hx)).1

theorem markovPointVec_inner (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x : Rd d) (hx : x ∈ extOpen V) (φ : TestOn V) :
    ⟪markovPointVec hd hh V hVb hρ hρV x hx,
      markovInsideVec hh V hρ φ⟫ =
        ∫ y, (-Real.log ‖x - y‖ - markovLogPot ρ y) *
          (markovInsideTest V hρ φ).1 y :=
  (Classical.choose_spec (markov_exists_pointVec hd hh V hVb hρ hρV x hx)).2.2 φ

end HigherDimLQGMetric
