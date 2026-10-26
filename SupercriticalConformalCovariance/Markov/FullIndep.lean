import SupercriticalConformalCovariance.Markov.GeneralExtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt LQGMetric.MarkovGauss
  QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

/-- The library zero extension is the orthogonal projection on every mean-zero test. -/
theorem extVec_meanZero_eq_projectedPair (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (ψ : TestC0) :
    extVec hh V ((V : Set ℂ).indicator ψ.1) = projectedPair hh V ψ := by
  apply eq_of_cmRange_inner hh
    (show extVec hh V ((V : Set ℂ).indicator ψ.1) ∈ cmRange hh V from ⟨_, rfl⟩)
    (projectedPair_mem_cmRange hh V ψ)
  intro f
  rw [extVec, LinearIsometry.inner_map_map, Submodule.coe_inner]
  change ⟪rieszFun V ((V : Set ℂ).indicator ψ.1), gradFeat V f.1⟫ = _
  rw [inner_rieszFun_indicator_gradFeat hh hV hpos ψ.1 f.2,
    inner_projectedPair_gradLin hh V ψ f]

theorem extVec_meanZero_eq_projectedPair_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (ψ : TestC0) :
    extVec hh V ((V : Set ℂ).indicator ψ.1) = projectedPair hh V ψ := by
  by_cases hne : (V : Set ℂ).Nonempty
  · exact extVec_meanZero_eq_projectedPair hh hV
      (exists_pos_energy_zeroSpace_m7d V.isOpen hne) ψ
  · have hVe : (V : Set ℂ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    apply eq_of_cmRange_inner hh
      (show extVec hh V ((V : Set ℂ).indicator ψ.1) ∈ cmRange hh V from ⟨_, rfl⟩)
      (projectedPair_mem_cmRange hh V ψ)
    intro f
    have hf0 : f.1 = 0 := by
      funext z
      exact image_eq_zero_of_notMem_tsupport fun hz => by
        have hzV := f.2.2.2 hz
        simpa [hVe] using hzV
    have hg : gradLin V f = 0 := by
      apply Subtype.ext
      change gradFeat V f.1 = 0
      rw [hf0]
      exact gradFeat_zero (isDNSpace_zeroSpace (V : Set ℂ))
    rw [hg, map_zero, inner_zero_right, inner_zero_right]

/-- Full complement independence on all mean-zero whole-plane tests. -/
theorem indepFun_zbExt_complement_meanZero (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) :
    IndepFun
      (fun ω (φ : TestC0) => zbExt hh V φ.1 ω)
      (fun ω (ψ : TestC0) => h ω ψ.1 - zbExt hh V ψ.1 ω) P := by
  apply (indepFun_projected_remainder hh V).process_congr
  · intro φ
    have he := extVec_meanZero_eq_projectedPair_general hh hV φ
    filter_upwards [(zbExt_ae hh V φ.1).symm] with ω hw
    change (projectedPair hh V φ : Ω → ℝ) ω = zbExt hh V φ.1 ω
    rw [← he]
    exact hw
  · intro ψ
    have he := extVec_meanZero_eq_projectedPair_general hh hV ψ
    filter_upwards [Lp.coeFn_sub ((memLp_pair hh ψ).toLp _)
      (projectedPair hh V ψ), (memLp_pair hh ψ).coeFn_toLp,
      (zbExt_ae hh V ψ.1).symm] with ω hsub hp hz
    change (remainderPair hh V ψ : Ω → ℝ) ω =
      h ω ψ.1 - zbExt hh V ψ.1 ω
    rw [remainderPair, hsub, Pi.sub_apply, hp, ← he, hz]
    rfl

end SupercriticalConformalCovariance.Markov
