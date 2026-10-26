import SupercriticalConformalCovariance.Markov.DensityBound
import LQGMetric.Field.MarkovAdmCov

/-!
# Canonical zero extension: arbitrary-domain Gaussian law at the process level

The new admissibility result makes the library's `rieszFun` genuinely represent every smooth
whole-plane test restricted to `V`, even when its support meets the boundary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt LQGMetric.MarkovGauss
  LQGMetric.MarkovNorm
  QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

/-- The canonical Riesz vector for a boundary-touching smooth test has the expected pairings. -/
theorem inner_rieszFun_indicator_gradFeat (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (φ : TestC) {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    ⟪rieszFun V ((V : Set ℂ).indicator φ), gradFeat V f⟫ =
      ∫ x, φ x * f x := by
  have hadm := admissible_indicator_test hh hV φ
  obtain ⟨hm, ⟨C, hC⟩, -⟩ := (extZeroTest V φ).2
  rw [rieszFun, inner_sub_left]
  rw [pair_rieszVec (isDNSpace_zeroSpace (V : Set ℂ)) hadm.1 hpos f hf,
    pair_rieszVec (isDNSpace_zeroSpace (V : Set ℂ)) hadm.2 hpos f hf]
  change (∫ x, f x ∂testMeasPos (extZeroTest V φ).1) -
      (∫ x, f x ∂testMeasNeg (extZeroTest V φ).1) = _
  rw [integral_testMeas_sub hm hC hf]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    change (V : Set ℂ).indicator φ x * f x = φ x * f x
    by_cases hx : x ∈ (V : Set ℂ)
    · rw [indicator_of_mem hx, mul_comm]
    · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2.2 h)
      rw [indicator_of_notMem hx, hf0]
      ring)

/-- The library's zero extension equals the intrinsic anchored projection on all smooth tests. -/
theorem extVec_eq_anchoredPair (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) :
    extVec hh V ((V : Set ℂ).indicator φ) = anchoredPair hh β hβ φ := by
  apply eq_of_cmRange_inner hh
    (show extVec hh V ((V : Set ℂ).indicator φ) ∈ cmRange hh V from ⟨_, rfl⟩)
    (anchoredPair_mem_cmRange hh β hβ φ)
  intro f
  rw [extVec, LinearIsometry.inner_map_map, Submodule.coe_inner]
  change ⟪rieszFun V ((V : Set ℂ).indicator φ), gradFeat V f.1⟫ = _
  rw [inner_rieszFun_indicator_gradFeat hh hV hpos φ f.2,
    inner_anchoredPair_gradLin hh hV hpos β hβ φ f]

/-- Full covariance law of the canonical zero extension for arbitrary admissible `V`. -/
theorem covariance_zbExt_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (φ ψ : TestC) :
    cov[zbExt hh V φ, zbExt hh V ψ; P] =
      zeroGFFTestCov V ((V : Set ℂ).indicator φ) ((V : Set ℂ).indicator ψ) := by
  have hm : MemLp (zbExt hh V ψ) 2 P := (Lp.memLp _).ae_eq (zbExt_ae hh V ψ).symm
  have hcov : cov[zbExt hh V φ, zbExt hh V ψ; P] =
      cov[(extVec hh V ((V : Set ℂ).indicator φ) : Ω → ℝ), zbExt hh V ψ; P] := by
    unfold covariance
    refine integral_congr_ae ?_
    filter_upwards [zbExt_ae hh V φ] with ω h1
    rw [h1, integral_congr_ae (zbExt_ae hh V φ)]
  have h0 : P[(extVec hh V ((V : Set ℂ).indicator φ) : Ω → ℝ)] = 0 := by
    rw [← integral_congr_ae (zbExt_ae hh V φ), integral_zbExt]
  rw [hcov, covariance_eq_inner _ hm h0,
    MemLp.toLp_congr hm (Lp.memLp _) (zbExt_ae hh V ψ),
    Lp.toLp_coeFn, extVec, extVec, LinearIsometry.inner_map_map, Submodule.coe_inner]
  exact inner_rieszFun (admissible_indicator_test hh hV φ)
    (admissible_indicator_test hh hV ψ)

end SupercriticalConformalCovariance.Markov
