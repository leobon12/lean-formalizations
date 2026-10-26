import SupercriticalConformalCovariance.Small.TangentConfVarying
import SupercriticalConformalCovariance.Small.ZoomWitness
import SupercriticalConformalCovariance.Root.Field

set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace
namespace SupercriticalConformalCovariance.Small
open LQGMetric (DistC restrictTo affineComp affinePt ofCont)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)

/-- A field and its original target realization, with the smooth normalizer,
mapped to the corrected realization on the global zoomed target domain. -/
def zoomRealizationData (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) →
      SupercriticalConformalCovariance.Transport.RealizationData (affinePreimage V (φ z) r) := fun p =>
  (confPullbackField Q
      (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
      (restrictTo (affinePreimage U z r) p.1),
    affineComp r (φ z) p.2.1.2.1,
    (p.2.1.2.2.1.comp
        (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V (φ z) hr)) +
      negConstOn (affinePreimage V (φ z) r) p.2.2,
      p.2.1.2.2.2.comp (affinePt r (φ z))))

theorem zoomRealizationData_field (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ)) :
    (zoomRealizationData Q hφ z hr p).1 =
      confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
        (restrictTo (affinePreimage U z r) p.1) := rfl

theorem measurable_zoomRealizationData (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable (zoomRealizationData Q hφ z hr) := by
  let Z := affinePreimage V (φ z) r
  have hfield : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
      confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
        (restrictTo (affinePreimage U z r) p.1) :=
    (SupercriticalConformalCovariance.Root.measurable_confPullbackField Q
      (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))).comp
      ((LQGMetric.measurable_restrictTo _).comp measurable_fst)
  have hg : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
      affineComp r (φ z) p.2.1.2.1 :=
    (LQGMetric.measurable_affineComp r (φ z)).comp
      ((measurable_fst.comp measurable_snd).comp (measurable_fst.comp measurable_snd))
  have hk : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
      p.2.1.2.2.1.comp
        (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V (φ z) hr)) +
        negConstOn Z p.2.2 := by
    have : LocallyCompactSpace (Z : Set ℂ) := Z.isOpen.locallyCompactSpace
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    have hk₀ : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
        p.2.1.2.2.1 := by fun_prop
    have hc : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
        p.2.2 := by fun_prop
    exact ((ContinuousMap.measurable_eval _).comp hk₀).add hc.neg
  have hF : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
      p.2.1.2.2.2.comp (affinePt r (φ z)) := by
    have hF₀ : Measurable fun p : DistC × (SupercriticalConformalCovariance.Transport.RealizationData V × ℝ) =>
        p.2.1.2.2.2 := by fun_prop
    exact (ContinuousMap.continuous_precomp _).measurable.comp hF₀
  exact hfield.prodMk (hg.prodMk (hk.prodMk hF))

/-- A samplewise original realization and a chosen whole-plane GFF witness
give exactly the realization data required by varying-field Lemma 3.3. -/
theorem zoomRealizationData_realization (Q : ℝ)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h g : Ω → DistC) (k : Ω → C(V, ℝ))
    (hR : IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
        (restrictTo U (h ω))) g k)
    (F₀ : Ω → C(ℂ, ℝ))
    (hwp : LQGMetric.IsWholePlaneGFF (fun ω => g ω - ofCont (F₀ ω)) P)
    (c : Ω → ℝ) (hc : Measurable c) :
    let H : Ω → DistC := fun ω => LQGMetric.addConst (affineComp r z (h ω)) (-c ω)
    let mark : Ω → SupercriticalConformalCovariance.Transport.RealizationData V × ℝ :=
      fun ω => ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
        (restrictTo U (h ω)), g ω, (k ω, F₀ ω)), c ω)
    let J := zoomRealizationData Q hφ z hr
    IsDomainRealization (affinePreimage V (φ z) r) P
      (fun ω => (J (H ω, mark ω)).1)
      (fun ω => (J (H ω, mark ω)).2.1)
      (fun ω => (J (H ω, mark ω)).2.2.1) ∧
    LQGMetric.IsWholePlaneGFF
      (fun ω => (J (H ω, mark ω)).2.1 -
        ofCont (J (H ω, mark ω)).2.2.2) P := by
  dsimp only
  constructor
  · exact isDomainRealization_zoom_subConst Q hφ z hr hR c hc
  · exact wholePlaneGFF_zoom_witness P g F₀ hwp (φ z) hr

end SupercriticalConformalCovariance.Small
