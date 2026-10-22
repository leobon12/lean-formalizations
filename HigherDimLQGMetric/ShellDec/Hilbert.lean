import HigherDimLQGMetric.ShellDec.Uniform
import LQGMetric.Field.MarkovGauss

/-!
# Gaussianity of coordinates in closed annular blocks
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private def shellGaussSpace {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) :
    Submodule ℝ (Lp ℝ 2 P) :=
  LQGMetric.MarkovGauss.gaussSpace
    (fun (φ : TestRd0 d) ω => h ω φ.1)
    (fun φ => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two)

theorem annularBlock_mem_shellGaussSpace {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b r : ℝ} {X : Lp ℝ 2 P}
    (hX : X ∈ annularBlock hh a b r) : X ∈ shellGaussSpace hh := by
  have hsub : annularPairings hh a b r ⊆ (shellGaussSpace hh : Set (Lp ℝ 2 P)) := by
    rintro Y ⟨φ, -, rfl⟩
    exact LQGMetric.MarkovGauss.toLp_mem_gaussSpace
      (fun φ : TestRd0 d => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two) φ
  have hclosed : IsClosed (shellGaussSpace hh : Set (Lp ℝ 2 P)) := by
    unfold shellGaussSpace LQGMetric.MarkovGauss.gaussSpace
    exact Submodule.isClosed_topologicalClosure _
  exact closure_minimal hsub hclosed hX

theorem shellBlock_gaussian {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) {S : Type*} (W : S → Lp ℝ 2 P)
    {a b : ℝ} (ρ : S → ℝ)
    (hW : ∀ s, W s ∈ annularBlock hh a b (ρ s)) :
    IsGaussianProcess (fun s => (W s : Ω → ℝ)) P := by
  exact LQGMetric.MarkovGauss.isGaussianProcess_of_mem_gaussSpace
    hh.gaussian hh.centered
    (fun φ : TestRd0 d => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two)
    W (fun s => annularBlock_mem_shellGaussSpace hh (hW s))

theorem shellBlock_centered {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) {a b r : ℝ} {W : Lp ℝ 2 P}
    (hW : W ∈ annularBlock hh a b r) :
    ∫ ω, (W : Ω → ℝ) ω ∂P = 0 := by
  exact (LQGMetric.MarkovGauss.isCGauss_of_mem_gaussSpace
    hh.gaussian hh.centered
    (fun φ : TestRd0 d => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two)
    (annularBlock_mem_shellGaussSpace hh hW)).2

end HigherDimLQGMetric
