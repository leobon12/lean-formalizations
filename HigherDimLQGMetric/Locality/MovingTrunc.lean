import HigherDimLQGMetric.Locality.TruncError
import LQGMetric.Prob.PolishContinuousMap

/-! Truncation control along moving field samples in a Skorokhod coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The fixed-field truncation theorem remains usable when Skorokhod field
samples move with the scale but all have the same normalized LGF law. A
subsequence is essential: equality of marginals gives convergence in measure,
which is then upgraded to almost sure convergence. -/
theorem l7a_exists_moving_trunc_error_subseq {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hL2c : L2c_trunc) (εs : ℕ → ℝ)
    (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    (μ : Measure (DistRd d)) [IsProbabilityMeasure μ]
    (hhμ : IsNormalizedLGF (id : DistRd d → DistRd d) μ)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (Xlim : Ω → DistRd d)
    (Xn : ℕ → Ω → DistRd d) (hXn : ∀ n, Measurable (Xn n))
    (hlaw : ∀ n, Q.map (Xn n) = μ) (hlimlaw : Q.map Xlim = μ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂Q, Tendsto
        (fun k => l7a_truncErrorC hd κ hκ (εs (ns k)) (hεs (ns k))
          (Xn (ns k) ω)) atTop (𝓝 (0 : C(Rd d, ℝ))) := by
  letI : PolishSpace C(Rd d, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  letI : PseudoMetricSpace C(Rd d, ℝ) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric C(Rd d, ℝ)
  let Eraw : ℕ → DistRd d → C(Rd d, ℝ) := fun n g =>
    l7a_truncErrorC hd κ hκ (εs n) (hεs n) g
  have hEa (n : ℕ) : AEMeasurable (Eraw n) μ :=
    l7a_aemeasurable_truncErrorC hd κ hκ (εs n) (hεs n) μ id hhμ
  let E : ℕ → DistRd d → C(Rd d, ℝ) := fun n => (hEa n).mk (Eraw n)
  have hEm (n : ℕ) : Measurable (E n) := (hEa n).measurable_mk
  have hEae (n : ℕ) : Eraw n =ᵐ[μ] E n := (hEa n).ae_eq_mk
  have hrawlim : ∀ᵐ g ∂μ, Tendsto (fun n => Eraw n g) atTop
      (𝓝 (0 : C(Rd d, ℝ))) :=
    l7a_ae_truncErrorC_tendsto_zero hd κ hκ hL2c εs hεs hεt μ id hhμ
  have hEall : ∀ᵐ g ∂μ, ∀ n, Eraw n g = E n g :=
    ae_all_iff.mpr hEae
  have hElim : ∀ᵐ g ∂μ, Tendsto (fun n => E n g) atTop
      (𝓝 (0 : C(Rd d, ℝ))) := by
    filter_upwards [hrawlim, hEall] with g hg he
    have hf : (fun n => Eraw n g) = fun n => E n g := funext he
    rw [← hf]
    exact hg
  have hbase : TendstoInMeasure μ E atTop (fun _ => (0 : C(Rd d, ℝ))) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hEm n).aestronglyMeasurable) hElim
  have hbad (n : ℕ) (ε : ℝ≥0∞) :
      MeasurableSet {g : DistRd d | ε ≤ edist (E n g) (0 : C(Rd d, ℝ))} := by
    have hm : Measurable fun g : DistRd d => edist (E n g) (0 : C(Rd d, ℝ)) :=
      continuous_edist.measurable.comp ((hEm n).prodMk measurable_const)
    exact measurableSet_le measurable_const hm
  have hbase' : TendstoInMeasure (Q.map Xlim) E atTop
      (fun _ => (0 : C(Rd d, ℝ))) := by
    rw [hlimlaw]
    exact hbase
  obtain ⟨ns, hns, hlim⟩ :=
    l7a_exists_moving_fixed_law_ae_subseq Q Xlim Xn hXn
      (fun n => (hlaw n).trans hlimlaw.symm) E 0 hbad hbase'
  have hEqn (n : ℕ) : (fun ω => Eraw n (Xn n ω)) =ᵐ[Q]
      (fun ω => E n (Xn n ω)) := by
    have hμ : Eraw n =ᵐ[Q.map (Xn n)] E n := by
      rw [hlaw n]
      exact hEae n
    exact ae_of_ae_map (hXn n).aemeasurable hμ
  have hEqall : ∀ᵐ ω ∂Q, ∀ n, Eraw n (Xn n ω) = E n (Xn n ω) :=
    ae_all_iff.mpr hEqn
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, hEqall] with ω hω he
  have hefun : (fun k => Eraw (ns k) (Xn (ns k) ω)) =
      fun k => E (ns k) (Xn (ns k) ω) := funext fun k => he (ns k)
  rw [hefun]
  exact hω

end HigherDimLQGMetric
