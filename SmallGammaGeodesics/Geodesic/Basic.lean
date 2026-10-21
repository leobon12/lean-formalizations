import LQGMetric.Assembly.MainFinal
import LQGMetric.Papers.GM.S2.Geodesics
import LQGMetric.Papers.GM.S1.Eq115
import LQGMetric.Papers.GM.S1.FieldAux
import LQGMetric.Papers.MQ.SphereMain
import LQGMetric.Meas.Geod
import GaussianLQG.Uniform.Limit.Basic

/-!
# The geodesic `P_γ` (source (1.3))

Compositions of certified LQGMetric results (ruling G11; planning audit GA1, (c2)):
a.s. existence and uniqueness of the constant-speed geodesic between two fixed points for a strong
γ-LQG metric and a whole-plane GFF, a measurable choice of it, a.e.-measurability of every a.s.
choice, and independence of its law from the realization of the normalized field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric

/-- DFGPS Lemma 3.8 (bounded compactness), unconditionally. -/
theorem dfgpsLem3_8_holds : Blueprint.DFGPSLem3_8 :=
  CONF.dfgpsLem3_8_of_exp (DZZ.dzzLem53ExpAll_of_hbadB l53HbadBAll_proved)

/-- Miller–Qian Theorem 1.2 for weak metrics (a.s. uniqueness of geodesics), unconditionally. -/
theorem mqThm1_2Weak_holds : Blueprint.MQThm1_2Weak :=
  MQ.mqThm1_2Weak dfgpsLem3_8_holds

/-- A.s. existence and uniqueness of the constant-speed geodesic between two fixed points, for a
strong γ-LQG metric and any whole-plane GFF. -/
theorem ae_existsUnique_geod01 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (z w : ℂ) :
    ∀ᵐ ω ∂P, ∃! η, Blueprint.IsGeod01 (D (h ω)) z w η :=
  GM.gm_S1_2 mqThm1_2Weak_holds hγ hγ2 (GM.gm_eq1_15 hγ hD) P h hh z w

/-- A.s. existence of geodesics between all pairs simultaneously (bounded compactness). -/
theorem ae_exists_geod01_all {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ, ∃ η, Blueprint.IsGeod01 (D (h ω)) z w η :=
  GM.gm_S1_1 dfgpsLem3_8_holds hγ hγ2 (GM.gm_eq1_15 hγ hD) P h hh

/-- A measurable choice of the a.s. unique geodesic, on any probability space. -/
theorem exists_measurable_geod01 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (z w : ℂ) :
    ∃ η : Ω → C(unitInterval, ℂ), Measurable η ∧
      ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D (h ω)) z w (η ω) := by
  have hm : Measurable h := hh.measurable
  have : IsProbabilityMeasure (P.map h) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hu : ∀ᵐ g ∂(P.map h), ∃! η, (D g).IsGeod01 z w η :=
    ae_existsUnique_geod01 hγ hγ2 hD (P.map h) id (GM.isWholePlaneGFF_id_map hh) z w
  obtain ⟨Γ, hΓm, hΓ⟩ := exists_measurable_geodSel D hD.measurable z w (P.map h) hu
  exact ⟨Γ ∘ h, hΓm.comp hm, ae_of_ae_map hm.aemeasurable hΓ⟩

/-- Any a.s. choice of the geodesic is a.e. equal to the measurable selection, hence
a.e.-measurable: no measurability hypothesis is needed on the geodesic in frozen statements. -/
theorem aemeasurable_of_ae_geod01 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) {z w : ℂ}
    {η : Ω → C(unitInterval, ℂ)} (hη : ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D (h ω)) z w (η ω)) :
    AEMeasurable η P := by
  obtain ⟨η', hη'm, hη'⟩ := exists_measurable_geod01 hγ hγ2 hD P h hh z w
  have heq : η' =ᵐ[P] η := by
    filter_upwards [ae_existsUnique_geod01 hγ hγ2 hD P h hh z w, hη, hη'] with ω hu h1 h2
    exact hu.unique h2 h1
  exact hη'm.aemeasurable.congr heq

/-- **Transfer.** For a fixed `γ ∈ (0,2)`, the law of any a.s. choice of the geodesic from `0` to
`1` is the same for every realization of the normalized whole-plane GFF: it is
`normGFFLaw.map Γ` for a measurable selector `Γ`. -/
theorem map_geod_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') {η : Ω → C(unitInterval, ℂ)} {η' : Ω' → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D (h ω)) 0 1 (η ω))
    (hη' : ∀ᵐ ω ∂P', Blueprint.IsGeod01 (D (h' ω)) 0 1 (η' ω)) :
    P.map η = P'.map η' := by
  have : IsProbabilityMeasure normGFFLaw := GaussianLQG.UniformLimit.isProbabilityMeasure_normGFFLaw
  have hu : ∀ᵐ g ∂normGFFLaw, ∃! η, (D g).IsGeod01 0 1 η :=
    ae_existsUnique_geod01 hγ hγ2 hD normGFFLaw id GaussianLQG.UniformLimit.isWholePlaneGFF_id_normGFFLaw 0 1
  obtain ⟨Γ, hΓm, hΓ⟩ := exists_measurable_geodSel D hD.measurable 0 1 normGFFLaw hu
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistC}, IsNormalizedWPGFF h P → ∀ {η : Ω → C(unitInterval, ℂ)},
      (∀ᵐ ω ∂P, Blueprint.IsGeod01 (D (h ω)) 0 1 (η ω)) → P.map η = normGFFLaw.map Γ := by
    intro Ω _ P _ h hh η hη
    have hm : Measurable h := hh.1.measurable
    have hlaw : normGFFLaw = P.map h := GM.normGFFLaw_eq hh
    have hΓ' : ∀ᵐ g ∂(P.map h), (D g).IsGeod01 0 1 (Γ g) := by rw [← hlaw]; exact hΓ
    have hΓh : ∀ᵐ ω ∂P, (D (h ω)).IsGeod01 0 1 (Γ (h ω)) := ae_of_ae_map hm.aemeasurable hΓ'
    have heq : η =ᵐ[P] Γ ∘ h := by
      filter_upwards [ae_existsUnique_geod01 hγ hγ2 hD P h hh.1 0 1, hη, hΓh] with ω hu h1 h2
      exact hu.unique h1 h2
    rw [Measure.map_congr heq, ← Measure.map_map hΓm hm, ← hlaw]
  rw [key hh hη, key hh' hη']

/-- The two geodesic predicates of LQGMetric agree definitionally. -/
theorem contMetric_isGeod01_iff (D : ContMetric) (z w : ℂ) (η : C(unitInterval, ℂ)) :
    D.IsGeod01 z w η ↔ Blueprint.IsGeod01 D z w η := Iff.rfl

end SmallGammaGeodesics
