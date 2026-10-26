import SupercriticalConformalCovariance.Markov.Replacement
import SupercriticalConformalCovariance.Markov.GeneralVersion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace Laplacian
open InnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt LQGMetric.MarkovHarm
  LQGMetric.Blueprint
  QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

/-- The actual measurable zero extension and its mean-zero complement are independent. -/
theorem indepFun_version_complement_meanZero (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {hz : Ω → DistC}
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) :
    IndepFun (fun ω (φ : TestC0) => hz ω φ.1)
      (fun ω (ψ : TestC0) => h ω ψ.1 - hz ω ψ.1) P := by
  apply (indepFun_zbExt_complement_meanZero hh hV).process_congr
  · intro φ
    exact (hzae φ.1).symm
  · intro ψ
    filter_upwards [hzae ψ.1] with ω he
    rw [he]

/-- Arbitrary-domain whole-plane Markov decomposition. The zero-boundary extension is a
+single measurable distribution, supported on the closure, with a simultaneous harmonic
+representative of the remainder. -/
theorem exists_joint_markov_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) :
    ∃ (hz : Ω → DistC) (H : Ω → ℂ → ℝ),
      Measurable hz ∧
      (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) ∧
      (∀ ω, restrictTo
        (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl)
        (hz ω) = 0) ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      Measurable (fun p : Ω × ℂ => H p.1 p.2) ∧
      (∀ᵐ ω ∂P, HarmonicOnNhd (H ω) (V : Set ℂ) ∧
        ∀ φ : TestOn V,
          restrictTo V (h ω - hz ω) φ = ∫ x, H ω x * φ x) ∧
      IndepFun (fun ω (φ : TestC0) => hz ω φ.1)
        (fun ω (ψ : TestC0) => h ω ψ.1 - hz ω ψ.1) P := by
  obtain ⟨hz, hzm, hzae, hsupp⟩ := exists_dist_version_zbExt_general hh hV
  obtain ⟨H, hHm, hH⟩ := exists_joint_harmonic_of_version hh hV hzm hzae
  exact ⟨hz, H, hzm, hzae, hsupp,
    isZeroBoundaryGFF_restrict_of_version hh hV hzm hzae,
    hHm, hH, indepFun_version_complement_meanZero hh hV hzae⟩

end SupercriticalConformalCovariance.Markov
