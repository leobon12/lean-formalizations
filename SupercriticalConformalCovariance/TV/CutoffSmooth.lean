import SupercriticalConformalCovariance.TV.UniformPointVariance
import QuantumZipper.Proofs.GFF.K3.HarmonicPart
import LQGMetric.Papers.MQ.Cutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper QuantumZipper.K3
open scoped Convolution

namespace SupercriticalConformalCovariance.TV

/-- A deterministic smooth cutoff for the observed ball. -/
def innerCutoff (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℂ) :=
  ⟨R + 1, 2 * R + 2, by linarith, by linarith⟩

/-- The outer cutoff only serves to make the continuous field integrable before convolution. -/
def outerCutoff (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℂ) :=
  ⟨2 * R + 3, 2 * R + 4, by linarith, by linarith⟩

def rawCenteredRepresentative (δ : ℝ) (hδ : 0 < δ) (T : DistC) (x : ℂ) : ℝ :=
  radialRepresentative δ hδ T x - radialRepresentative δ hδ T 0

theorem continuous_rawCenteredRepresentative (δ : ℝ) (hδ : 0 < δ) (T : DistC) :
    Continuous (rawCenteredRepresentative δ hδ T) :=
  (radialRepresentative δ hδ T).continuous.sub continuous_const

def smoothedRepresentative (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (T : DistC) (x : ℂ) : ℝ :=
  (∫ y, rbump (0 : ℂ) ε y)⁻¹ *
    ((fun y => (outerCutoff R hR y) * rawCenteredRepresentative δ hδ T y)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (rbump 0 ε)) x

theorem contDiff_smoothedRepresentative (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (T : DistC) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (smoothedRepresentative R hR δ ε hδ T) := by
  have hv : Continuous (fun y => (outerCutoff R hR y) *
      rawCenteredRepresentative δ hδ T y) :=
    ((outerCutoff R hR).contDiff (n := 0)).continuous.mul
      (continuous_rawCenteredRepresentative δ hδ T)
  exact contDiff_const.mul
    ((hasCompactSupport_rbump hε).contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hv.locallyIntegrable (contDiff_rbump 0 ε))

def smoothCutoffShift (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (T : DistC) (x : ℂ) : ℝ :=
  innerCutoff R hR x * smoothedRepresentative R hR δ ε hδ T x

theorem contDiff_smoothCutoffShift (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (T : DistC) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (smoothCutoffShift R hR δ ε hδ T) :=
  (innerCutoff R hR).contDiff.mul
    (contDiff_smoothedRepresentative R hR δ ε hδ hε T)

theorem hasCompactSupport_smoothCutoffShift (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (T : DistC) :
    HasCompactSupport (smoothCutoffShift R hR δ ε hδ T) :=
  (innerCutoff R hR).hasCompactSupport.mul_right

theorem smoothCutoffShift_mem_zeroSpace (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (T : DistC) (D : Set ℂ)
    (hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D) :
    smoothCutoffShift R hR δ ε hδ T ∈ zeroSpace D := by
  refine ⟨contDiff_smoothCutoffShift R hR δ ε hδ hε T,
    hasCompactSupport_smoothCutoffShift R hR δ ε hδ T, ?_⟩
  exact (tsupport_mul_subset_left).trans
    ((innerCutoff R hR).tsupport_eq.le.trans (by simpa [innerCutoff] using hball))

theorem innerCutoff_eq_one (R : ℝ) (hR : 0 < R) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) (R + 1)) :
    innerCutoff R hR x = 1 :=
  (innerCutoff R hR).one_of_mem_closedBall (by simpa [innerCutoff] using hx)

theorem measurable_rawCenteredRepresentative (δ : ℝ) (hδ : 0 < δ) :
    Measurable (fun p : DistC × ℂ => rawCenteredRepresentative δ hδ p.1 p.2) := by
  change Measurable (fun p : DistC × ℂ =>
    p.1 (LQGMetric.GM.radBump δ hδ.le p.2) / (∫ y, LQGMetric.GM.radProf δ y) -
      p.1 (LQGMetric.GM.radBump δ hδ.le 0) / (∫ y, LQGMetric.GM.radProf δ y))
  exact ((LQGMetric.GM.measurable_apply_radBump δ hδ.le).div_const _).sub
    (((measurable_distOn_apply (LQGMetric.GM.radBump δ hδ.le 0)).comp measurable_fst).div_const _)

theorem measurable_smoothedRepresentative_apply (R : ℝ) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (x : ℂ) :
    Measurable (fun T : DistC => smoothedRepresentative R hR δ ε hδ T x) := by
  have hm : Measurable (fun p : DistC × ℂ =>
      (outerCutoff R hR p.2) * rawCenteredRepresentative δ hδ p.1 p.2 *
        rbump 0 ε (x - p.2)) := by
    exact (((outerCutoff R hR).contDiff (n := 0)).continuous.measurable.comp
      measurable_snd).mul (measurable_rawCenteredRepresentative δ hδ) |>.mul
        (((contDiff_rbump 0 ε (n := 0)).continuous.comp
          (continuous_const.sub continuous_id)).measurable.comp measurable_snd)
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))
  convert (hi.const_mul (∫ y, rbump (0 : ℂ) ε y)⁻¹).measurable using 1
  ext T
  simp only [smoothedRepresentative, convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

def smoothCutoffShiftC (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (T : DistC) : C(ℂ, ℝ) :=
  ⟨smoothCutoffShift R hR δ ε hδ T,
    (contDiff_smoothCutoffShift R hR δ ε hδ hε T).continuous⟩

theorem measurable_smoothCutoffShiftC (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    Measurable (smoothCutoffShiftC R hR δ ε hδ hε) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro x
  exact ((measurable_smoothedRepresentative_apply R hR δ ε hδ x).const_mul
    (innerCutoff R hR x))

theorem measurable_smoothCutoffShift_fderiv (R : ℝ) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    Measurable (fun p : DistC × ℂ =>
      fderiv ℝ (smoothCutoffShift R hR δ ε hδ p.1) p.2) := by
  have hm := measurable_fderiv_with_param ℝ
    (f := fun f : C(ℂ, ℝ) => (f : ℂ → ℝ)) continuous_eval
  exact hm.comp ((measurable_smoothCutoffShiftC R hR δ ε hδ hε).comp measurable_fst
    |>.prodMk measurable_snd)

theorem measurable_smoothCutoffShift_energy (R : ℝ) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (D : Set ℂ) :
    Measurable (fun T : DistC =>
      dirichletEnergyOn D (smoothCutoffShift R hR δ ε hδ T)) := by
  have hm : Measurable (fun p : DistC × ℂ =>
      ‖fderiv ℝ (smoothCutoffShift R hR δ ε hδ p.1) p.2‖ ^ 2) :=
    ((measurable_smoothCutoffShift_fderiv R hR δ ε hδ hε).norm).pow_const 2
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℂ).restrict D)
  exact hi.measurable.const_mul (2 * Real.pi)⁻¹

theorem measurable_smoothCutoffShift_pair (R : ℝ) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (ψ : ℂ → ℝ)
    (hψ : Measurable ψ) :
    Measurable (fun T : DistC =>
      ∫ x, smoothCutoffShift R hR δ ε hδ T x * ψ x) := by
  have hm : Measurable (fun p : DistC × ℂ =>
      smoothCutoffShift R hR δ ε hδ p.1 p.2 * ψ p.2) := by
    have he : Measurable (fun p : DistC × ℂ =>
        smoothCutoffShift R hR δ ε hδ p.1 p.2) :=
      continuous_eval.measurable.comp
        (((measurable_smoothCutoffShiftC R hR δ ε hδ hε).comp measurable_fst).prodMk
          measurable_snd)
    exact he.mul (hψ.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def canonicalShift (R : ℝ) (hR : 0 < R) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (D : Set ℂ)
    (hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D) (T : DistC) :
    LQGMetric.MarkovZB.zsSub D :=
  ⟨smoothCutoffShift R hR δ ε hδ T,
    smoothCutoffShift_mem_zeroSpace R hR δ ε hδ hε T D hball⟩

theorem measurable_canonicalShift_pair (R : ℝ) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (D : TopologicalSpace.Opens ℂ)
    (hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D) (ψ : TestOn D) :
    Measurable (fun T : DistC =>
      ∫ x, (canonicalShift R hR δ ε hδ hε D hball T).1 x * ψ x) :=
  measurable_smoothCutoffShift_pair R hR δ ε hδ hε ψ ψ.contDiff.continuous.measurable

theorem measurable_canonicalShift_energy (R : ℝ) (hR : 0 < R)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (D : TopologicalSpace.Opens ℂ)
    (hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D) :
    Measurable (fun T : DistC =>
      dirichletEnergyOn D (canonicalShift R hR δ ε hδ hε D hball T).1) :=
  measurable_smoothCutoffShift_energy R hR δ ε hδ hε D

end SupercriticalConformalCovariance.TV
