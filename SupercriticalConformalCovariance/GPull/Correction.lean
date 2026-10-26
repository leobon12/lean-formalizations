import SupercriticalConformalCovariance.GPull.Regularize

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

/-- The logarithmic derivative is continuous in the ambient formulation. -/
theorem continuousOn_logDeriv (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) :
    ContinuousOn (fun x => Q * Real.log ‖deriv φ x‖) (U : Set ℂ) := by
  have hd := (hφ.1.deriv U.isOpen).continuousOn
  exact continuousOn_const.mul (hd.norm.log fun x hx =>
    norm_ne_zero_iff.mpr
      (QuantumZipper.CA.deriv_ne_zero_of_injOn U.isOpen hφ.1 hφ.2.injOn hx))

/-- The deterministic logarithmic derivative term is continuous on the source domain. -/
def logDerivCont (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) : C(U, ℝ) :=
  ⟨fun x => Q * Real.log ‖deriv φ x‖, by
    change Continuous (Set.domRestrict (U : Set ℂ)
      (fun x => Q * Real.log ‖deriv φ x‖))
    apply continuousOn_iff_continuous_domRestrict.mp
    exact continuousOn_logDeriv Q hφ⟩

/-- The conformal map as a continuous map between the domain carriers. -/
def confDomainMap {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) : C(U, V) :=
  ⟨fun x => ⟨φ x, hφ.2.mapsTo x.property⟩,
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hφ.1.continuousOn) _⟩

/-- Assemble the two Markov harmonic parts and the realization correction into
one measurable continuous random function on the source domain. -/
theorem exists_measurable_correction
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (Q : ℝ) {P' : Measure (Ω × DistC)}
    (hfst : MeasurePreserving (Prod.fst : Ω × DistC → Ω) P' P)
    {HV : Ω → ℂ → ℝ}
    (hVm : Measurable (fun p : Ω × U => HV p.1 (φ p.2)))
    (hVc : ∀ᵐ ω ∂P, Continuous fun x : U => HV ω (φ x))
    {HU : DistC → ℂ → ℝ}
    (hUm : Measurable (fun p : DistC × ℂ => HU p.1 p.2))
    (hUc : ∀ᵐ p ∂P', Continuous fun x : U => HU p.2 x)
    {c : Ω → C(ℂ, ℝ)} (hcm : Measurable c)
    {f : Ω → C(V, ℝ)} (hfm : Measurable f) :
    ∃ k : (Ω × DistC) → C(U, ℝ), Measurable k ∧
      (∀ᵐ p ∂P', ∀ x : U,
        k p x = HV p.1 (φ x) - HU p.2 x +
          c p.1 (φ x) + f p.1 ⟨φ x, hφ.2.mapsTo x.property⟩ +
          Q * Real.log ‖deriv φ x‖) := by
  haveI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let T : (Ω × DistC) → U → ℝ := fun p x =>
    HV p.1 (φ x) - HU p.2 x +
      c p.1 (φ x) + f p.1 ⟨φ x, hφ.2.mapsTo x.property⟩ +
      Q * Real.log ‖deriv φ x‖
  have hTm : Measurable (fun q : (Ω × DistC) × U => T q.1 q.2) := by
    have hφm : Measurable (fun x : U => φ x) :=
      (continuousOn_iff_continuous_domRestrict.mp hφ.1.continuousOn).measurable
    have hφVm : Measurable (confDomainMap hφ) := (confDomainMap hφ).continuous.measurable
    have hV' : Measurable (fun q : (Ω × DistC) × U => HV q.1.1 (φ q.2)) :=
      hVm.comp (Measurable.prodMk
        (measurable_fst.comp measurable_fst) measurable_snd)
    have hU' : Measurable (fun q : (Ω × DistC) × U => HU q.1.2 q.2) :=
      hUm.comp (Measurable.prodMk
        (measurable_snd.comp measurable_fst)
        (measurable_subtype_coe.comp measurable_snd))
    have hc' : Measurable (fun q : (Ω × DistC) × U => c q.1.1 (φ q.2)) :=
      continuous_eval.measurable.comp
        (Measurable.prodMk
          (hcm.comp (measurable_fst.comp measurable_fst))
          (hφm.comp measurable_snd))
    have hf' : Measurable (fun q : (Ω × DistC) × U =>
        f q.1.1 ⟨φ q.2, hφ.2.mapsTo q.2.property⟩) :=
      continuous_eval.measurable.comp
        (Measurable.prodMk
          (hfm.comp (measurable_fst.comp measurable_fst))
          (hφVm.comp measurable_snd))
    have hl' : Measurable (fun q : (Ω × DistC) × U =>
        Q * Real.log ‖deriv φ q.2‖) :=
      ((logDerivCont Q hφ).continuous.measurable).comp measurable_snd
    exact (((hV'.sub hU').add hc').add hf').add hl'
  have hTc : ∀ᵐ p ∂P', Continuous (T p) := by
    have hV' : ∀ᵐ p ∂P', Continuous fun x : U => HV p.1 (φ x) := by
      have h' : ∀ᵐ ω ∂(P'.map (Prod.fst : Ω × DistC → Ω)),
          Continuous fun x : U => HV ω (φ x) := by
        rwa [hfst.map_eq]
      exact ae_of_ae_map measurable_fst.aemeasurable h'
    filter_upwards [hV', hUc] with p hV hU
    exact ((((hV.sub hU).add
      ((c p.1).continuous.comp
        (continuousOn_iff_continuous_domRestrict.mp hφ.1.continuousOn))).add
      ((f p.1).continuous.comp (confDomainMap hφ).continuous)).add
      (logDerivCont Q hφ).continuous)
  exact exists_measurable_continuous_version hTm hTc


end SupercriticalConformalCovariance.GPull
