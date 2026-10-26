import SupercriticalConformalCovariance.Markov.GeneralMarkov
import LQGMetric.Papers.CONF.S3D112M1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt
  QuantumZipper QuantumZipper.K3

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {h : Ω → DistC} {h' : Ω' → DistC} {V : Opens ℂ}

/-- The canonical zero extension has the full, intrinsic `DistC` Gaussian law on every
+admissible domain, including unbounded domains with no normalization circle. -/
theorem isZBExtField_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {hz : Ω → DistC} (hzm : Measurable hz)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) :
    LQGMetric.CONF.IsZBExtField V hz P where
  measurable := hzm
  gaussian := by
    have hg := (isGaussianProcess_zbExt_sumElim hh V).comp_right
      (Sum.inl : TestC → TestC ⊕ TestC0)
    exact hg.congr fun φ => (hzae φ).symm
  centered := fun φ => by
    rw [integral_congr_ae (hzae φ), integral_zbExt]
  covariance_eq := fun φ ψ => by
    rw [LQGMetric.CircleAvg.covariance_congr_ae (hzae φ) (hzae ψ),
      covariance_zbExt_general hh hV]

private def extPath (X : Ω → DistC) (ω : Ω) : TestC → ℝ := fun φ => X ω φ
private def extPath' (X : Ω' → DistC) (ω : Ω') : TestC → ℝ := fun φ => X ω φ
private def extEval (g : DistC) : TestC → ℝ := fun φ => g φ
private theorem measurable_extEval : Measurable extEval :=
  measurable_pi_iff.2 fun φ => measurable_distOn_apply φ

/-- The intrinsic Gaussian covariance specifies the complete cylinder law of the
zero-boundary extension. -/
theorem isZBExtField_map_eq {X : Ω → DistC} {Y : Ω' → DistC}
    (hX : LQGMetric.CONF.IsZBExtField V X P)
    (hY : LQGMetric.CONF.IsZBExtField V Y P') :
    P.map X = P'.map Y := by
  have hpm : Measurable (extPath X) := measurable_pi_iff.2 fun φ =>
    (measurable_distOn_apply φ).comp hX.measurable
  have hpm' : Measurable (extPath' Y) := measurable_pi_iff.2 fun φ =>
    (measurable_distOn_apply φ).comp hY.measurable
  have hfin : ∀ I : Finset TestC, (P.map (extPath X)).map I.restrict =
      (P'.map (extPath' Y)).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hpm,
      Measure.map_map (Finset.measurable_restrict I) hpm']
    exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
      (U := fun (i : I) ω => X ω i.1) (V := fun (i : I) ω => Y ω i.1)
      (hX.gaussian.hasGaussianLaw I) (hY.gaussian.hasGaussianLaw I)
      (fun i => (measurable_distOn_apply i.1).comp hX.measurable)
      (fun i => (measurable_distOn_apply i.1).comp hY.measurable)
      (fun i => (hX.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => (hY.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => hX.centered i.1) (fun i => hY.centered i.1)
      (fun i j => by rw [hX.covariance_eq, hY.covariance_eq])
  have hpath : P.map (extPath X) = P'.map (extPath' Y) :=
    IsProjectiveLimit.unique (P := fun I => (P'.map (extPath' Y)).map I.restrict)
      hfin (fun _ => rfl)
  have he1 : extPath X = extEval ∘ X := rfl
  have he2 : extPath' Y = extEval ∘ Y := rfl
  rw [he1, he2, ← Measure.map_map measurable_extEval hX.measurable,
    ← Measure.map_map measurable_extEval hY.measurable] at hpath
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := congrArg (fun μ : Measure (TestC → ℝ) => μ t) hpath
  rwa [Measure.map_apply measurable_extEval ht,
    Measure.map_apply measurable_extEval ht] at this

/-- The full law of the zero extension depends only on `V`. -/
theorem map_zbExt_version_eq (hh : IsWholePlaneGFF h P)
    (hh' : IsWholePlaneGFF h' P') (hV : ZBAdmissible V)
    {hz : Ω → DistC} {hz' : Ω' → DistC}
    (hzm : Measurable hz)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ)
    (hz'm : Measurable hz')
    (hz'ae : ∀ φ : TestC, (fun ω => hz' ω φ) =ᵐ[P'] zbExt hh' V φ) :
    P.map hz = P'.map hz' := by
  let hzG := isZBExtField_general hh hV hzm hzae
  let hz'G := isZBExtField_general hh' hV hz'm hz'ae
  have hpm : Measurable (extPath hz) := measurable_pi_iff.2 fun φ =>
    (measurable_distOn_apply φ).comp hzm
  have hpm' : Measurable (extPath' hz') := measurable_pi_iff.2 fun φ =>
    (measurable_distOn_apply φ).comp hz'm
  have hfin : ∀ I : Finset TestC, (P.map (extPath hz)).map I.restrict =
      (P'.map (extPath' hz')).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hpm,
      Measure.map_map (Finset.measurable_restrict I) hpm']
    exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
      (U := fun (i : I) ω => hz ω i.1) (V := fun (i : I) ω => hz' ω i.1)
      (hzG.gaussian.hasGaussianLaw I) (hz'G.gaussian.hasGaussianLaw I)
      (fun i => (measurable_distOn_apply i.1).comp hzm)
      (fun i => (measurable_distOn_apply i.1).comp hz'm)
      (fun i => (hzG.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => (hz'G.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => hzG.centered i.1) (fun i => hz'G.centered i.1)
      (fun i j => by rw [hzG.covariance_eq, hz'G.covariance_eq])
  have hpath : P.map (extPath hz) = P'.map (extPath' hz') :=
    IsProjectiveLimit.unique (P := fun I => (P'.map (extPath' hz')).map I.restrict)
      hfin (fun _ => rfl)
  have he1 : extPath hz = extEval ∘ hz := rfl
  have he2 : extPath' hz' = extEval ∘ hz' := rfl
  rw [he1, he2, ← Measure.map_map measurable_extEval hzm,
    ← Measure.map_map measurable_extEval hz'm] at hpath
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := congrArg (fun μ : Measure (TestC → ℝ) => μ t) hpath
  rwa [Measure.map_apply measurable_extEval ht,
    Measure.map_apply measurable_extEval ht] at this

end SupercriticalConformalCovariance.Markov
