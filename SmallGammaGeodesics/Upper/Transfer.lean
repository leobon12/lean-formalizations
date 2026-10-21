import SmallGammaGeodesics.Upper.TransferPairing
import SmallGammaGeodesics.Upper.Defs
import SmallGammaGeodesics.Variance.FourKernel

/-!
# §5 transfer: joint laws, the normalization modulo constants, pairings (packet P-U1)

Blueprint `s5-upper.tex`, Subsection `ssec:transfer` (BP2 detail D6): Lemmas `lem:joint-law`,
`lem:normalize` and `lem:pairing-variance`. The probe argument runs on the coupling spaces of
Lemma 4.2′, where the fields are whole-plane GFFs only modulo additive constants; these lemmas
move laws, events and moments between those spaces and the coordinate space.

* `map_geod_field_eq`, `measure_pair_eq_of_geod` (`lem:joint-law`): for two normalized whole-plane
  GFFs and a.s. geodesics `η`, `η'` from `0` to `1`, the pairs `(η, h)` and `(η', h')` are
  a.e.-measurable with the same law on `C([0,1], ℂ) × 𝒟'(ℂ)` (the proof of `map_geod_eq`, with the
  selector `Γ` applied jointly: `(η, h) = (Γ ∘ h, h)` a.s.).
  `lintegral_pair_eq_of_geod` is the same statement for lower integrals of Borel functionals.
* `measurable_nrmF`, `isNormalizedWPGFF_nrmF`, `ae_dist_nrmF`, `ae_isGeod01_nrmF`,
  `ae_measPairing_addConst`, `ae_Zf_nrmF`, `ae_probePair_nrmF` (`lem:normalize`):
  `nrm g = g − g₁(0)` is Borel and normalizes every whole-plane GFF; `D_{nrm h} = e^{−ξ h₁(0)} D_h`
  a.s.; geodesics are unchanged; `(h + c, μ) = (h, μ) + c` a.s. for all `c` (from `MeasPair`, the
  general form of `lem:pairing-limits` (a)); hence `Z_b` and `G_θ` are a.s. unchanged by the
  normalization.
* `lintegral_sq_measPairing_sub` (`lem:pairing-variance`): for every whole-plane GFF and regular
  probability measures `μ, ν`, `∫⁻ ((h, μ) − (h, ν))² = ‖μ − ν‖_G²`, through the coordinate
  realization (`exists_coordRealization`, `integral_sq_pairing_sub`) and equality of laws.
* Borel events of the pair (BP2 D6): `continuous_band_yPath`, `measurable_band_yPath`,
  `measurable_euclidErrF`, `measurableSet_good_pair`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## The joint law of the geodesic and the field (`lem:joint-law`) -/

/-- **Joint law of the geodesic and the field.** For a strong γ-LQG metric, two normalized
whole-plane GFFs `h`, `h'` and a.s. geodesics `η`, `η'` from `0` to `1`: `(η, h)` is
a.e.-measurable and `(η, h)`, `(η', h')` have the same law. -/
theorem map_geod_field_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') {η : Ω → C(unitInterval, ℂ)} {η' : Ω' → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 0 1 (η ω))
    (hη' : ∀ᵐ ω ∂P', IsGeod01 (D (h' ω)) 0 1 (η' ω)) :
    AEMeasurable (fun ω => (η ω, h ω)) P ∧
      P.map (fun ω => (η ω, h ω)) = P'.map (fun ω => (η' ω, h' ω)) := by
  have : IsProbabilityMeasure normGFFLaw := GaussianLQG.UniformLimit.isProbabilityMeasure_normGFFLaw
  have hu : ∀ᵐ g ∂normGFFLaw, ∃! η, (D g).IsGeod01 0 1 η :=
    ae_existsUnique_geod01 hγ hγ2 hD normGFFLaw id
      GaussianLQG.UniformLimit.isWholePlaneGFF_id_normGFFLaw 0 1
  obtain ⟨Γ, hΓm, hΓ⟩ := exists_measurable_geodSel D hD.measurable 0 1 normGFFLaw hu
  have hpair : Measurable fun g : DistC => (Γ g, g) := hΓm.prodMk measurable_id
  have key : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistC}, IsNormalizedWPGFF h P → ∀ {η : Ω → C(unitInterval, ℂ)},
      (∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 0 1 (η ω)) →
      (fun ω => (η ω, h ω)) =ᵐ[P] (fun g : DistC => (Γ g, g)) ∘ h ∧
        P.map (fun ω => (η ω, h ω)) = normGFFLaw.map (fun g : DistC => (Γ g, g)) := by
    intro Ω _ P _ h hh η hη
    have hm : Measurable h := hh.1.measurable
    have hlaw : normGFFLaw = P.map h := GM.normGFFLaw_eq hh
    have hΓ' : ∀ᵐ g ∂(P.map h), (D g).IsGeod01 0 1 (Γ g) := by rw [← hlaw]; exact hΓ
    have hΓh : ∀ᵐ ω ∂P, (D (h ω)).IsGeod01 0 1 (Γ (h ω)) := ae_of_ae_map hm.aemeasurable hΓ'
    have heq : (fun ω => (η ω, h ω)) =ᵐ[P] (fun g : DistC => (Γ g, g)) ∘ h := by
      filter_upwards [ae_existsUnique_geod01 hγ hγ2 hD P h hh.1 0 1, hη, hΓh] with ω hu h1 h2
      simp only [Function.comp_apply]
      rw [hu.unique h1 h2]
    refine ⟨heq, ?_⟩
    rw [Measure.map_congr heq, ← Measure.map_map hpair hm, ← hlaw]
  obtain ⟨heq, hmap⟩ := key hh hη
  obtain ⟨-, hmap'⟩ := key hh' hη'
  exact ⟨(hpair.comp hh.1.measurable).aemeasurable.congr heq.symm, hmap.trans hmap'.symm⟩

/-- **Events of the pair `(η, h)`** have the same probability on every realization (outer measures:
`η` need not be measurable). -/
theorem measure_pair_eq_of_geod {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') {η : Ω → C(unitInterval, ℂ)} {η' : Ω' → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 0 1 (η ω))
    (hη' : ∀ᵐ ω ∂P', IsGeod01 (D (h' ω)) 0 1 (η' ω))
    {A : Set (C(unitInterval, ℂ) × DistC)} (hA : MeasurableSet A) :
    P {ω | (η ω, h ω) ∈ A} = P' {ω | (η' ω, h' ω) ∈ A} := by
  obtain ⟨hm, hmap⟩ := map_geod_field_eq hγ hγ2 hD hh hh' hη hη'
  obtain ⟨hm', -⟩ := map_geod_field_eq hγ hγ2 hD hh' hh hη' hη
  have h1 := Measure.map_apply_of_aemeasurable hm hA
  have h2 := Measure.map_apply_of_aemeasurable hm' hA
  rw [hmap, h2] at h1
  exact h1.symm

/-- **Lower integrals of Borel functionals of `(η, h)`** agree on every realization (the last clause
of `lem:joint-law`). -/
theorem lintegral_pair_eq_of_geod {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC} (hh : IsNormalizedWPGFF h P)
    (hh' : IsNormalizedWPGFF h' P') {η : Ω → C(unitInterval, ℂ)} {η' : Ω' → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 0 1 (η ω))
    (hη' : ∀ᵐ ω ∂P', IsGeod01 (D (h' ω)) 0 1 (η' ω))
    {F : C(unitInterval, ℂ) × DistC → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (η ω, h ω) ∂P = ∫⁻ ω, F (η' ω, h' ω) ∂P' := by
  obtain ⟨hm, hmap⟩ := map_geod_field_eq hγ hγ2 hD hh hh' hη hη'
  obtain ⟨hm', -⟩ := map_geod_field_eq hγ hγ2 hD hh' hh hη' hη
  rw [← lintegral_map' hF.aemeasurable hm, hmap, lintegral_map' hF.aemeasurable hm']

/-! ## Borel events of the pair `(η, h)` (BP2 D6) -/

/-- `η ↦ B_{j,a}(y_η)` is continuous on `C([0,1], ℂ)` (a finite combination of the integrals
`∫₀¹ y_η(t) sin(kπt) dt`). -/
theorem continuous_band_yPath (j : ℕ) (a : ℝ) :
    Continuous fun η : C(unitInterval, ℂ) => band (yPath η) j a := by
  unfold band sineCoef
  refine continuous_finsetSum _ fun k _ => ?_
  refine (continuous_const.mul (continuous_const.mul ?_)).mul continuous_const
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
  show Continuous fun p : C(unitInterval, ℂ) × ℝ => yPath p.1 p.2 * Real.sin (k * Real.pi * p.2)
  have hp : Continuous fun t : ℝ => projIcc (0 : ℝ) 1 zero_le_one t := continuous_projIcc
  have h1 : Continuous fun p : C(unitInterval, ℂ) × ℝ => p.1 (projIcc 0 1 zero_le_one p.2) :=
    continuous_eval.comp (continuous_fst.prodMk (hp.comp continuous_snd))
  exact (Complex.continuous_im.comp h1).mul
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd))

theorem measurable_band_yPath (j : ℕ) (a : ℝ) :
    Measurable fun η : C(unitInterval, ℂ) => band (yPath η) j a :=
  (continuous_band_yPath j a).measurable

/-- `d ↦ E_{b,R}(d)` is Borel on the continuous metrics. -/
theorem measurable_euclidErrF (b R : ℝ) : Measurable (euclidErrF b R) := by
  have e : euclidErrF b R = fun d : ContMetric =>
      ⨆ p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R,
        ENNReal.ofReal |Real.exp (-b) * d.1 p - ‖p.1 - p.2‖| := by
    funext d
    rw [biSup_prod]
    rfl
  rw [e]
  refine measurable_biSup_of_continuousOn _ (fun d => ?_) (fun p => ?_)
  · exact (ENNReal.continuous_ofReal.comp ((continuous_const.mul d.1.continuous).sub
      (continuous_fst.sub continuous_snd).norm).abs).continuousOn
  · have hc : Continuous fun d : ContMetric => d.1 p :=
      (continuous_eval_const p).comp continuous_subtype_val
    exact ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp ((hc.measurable.const_mul _).sub_const _))

/-- **Good events of the field and Borel path events** form a Borel event of the pair: for a
measurable metric map `D` and a Borel set `S` of paths,
`{(η, g) : E_{b,R}(D_g) ≤ x, η ∈ S}` is Borel. With `S = {η : r < σ B_{j,a}(y_η)}`
(`measurable_band_yPath`) this is the event of the single-probe transfer. -/
theorem measurableSet_good_pair {D : DistC → ContMetric} (hD : Measurable D) (b R x : ℝ)
    {S : Set C(unitInterval, ℂ)} (hS : MeasurableSet S) :
    MeasurableSet {p : C(unitInterval, ℂ) × DistC |
      euclidErrF b R (D p.2) ≤ ENNReal.ofReal x ∧ p.1 ∈ S} :=
  (measurableSet_le (((measurable_euclidErrF b R).comp hD).comp measurable_snd)
    measurable_const).inter (measurable_fst hS)

/-! ## The normalization `nrm g = g − g₁(0)` (`lem:normalize`) -/

/-- `nrm` is Borel on `𝒟'(ℂ)`. -/
theorem measurable_nrmF : Measurable nrmF := by
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [nrmF, GFFInv.addConst_apply]
  exact (GFFInv.measurable_pair φ).add ((measurable_circleAvg_left 1 0).neg.const_mul _)

/-- `nrm h` is a normalized whole-plane GFF for every whole-plane GFF `h`. -/
theorem isNormalizedWPGFF_nrmF {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    IsNormalizedWPGFF (fun ω => nrmF (h ω)) P := by
  have hc : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  refine ⟨hh.addConst hc, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
  rw [nrmF, hω, add_neg_cancel]

/-- `D_{nrm h} = e^{−ξ h₁(0)} D_h` almost surely (Weyl scaling by a constant). -/
theorem ae_dist_nrmF {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ z w, (D (nrmF (h ω))).1 (z, w) =
      Real.exp (-(xiGamma γ * circleAvg (h ω) 1 0)) * (D (h ω)).1 (z, w) := by
  filter_upwards [hD.ae_dist_addConst (GM.isGFFPlusCont_of_isWholePlaneGFF hh)] with ω hω z w
  rw [nrmF, hω, mul_neg]

/-- `D_h` and `D_{nrm h}` have a.s. the same constant-speed geodesics from `0` to `1`. -/
theorem ae_isGeod01_nrmF {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {η : Ω → C(unitInterval, ℂ)}
    (hη : ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) 0 1 (η ω)) :
    ∀ᵐ ω ∂P, IsGeod01 (D (nrmF (h ω))) 0 1 (η ω) := by
  filter_upwards [ae_dist_nrmF hD hh, hη] with ω hω hg
  exact (isGeod01_iff_of_eq_smul (Real.exp_pos _) hω 0 1 (η ω)).2 hg

/-- **`(h + c, μ) = (h, μ) + c`** almost surely, for all `c` at once, for every whole-plane GFF and
every regular probability measure `μ` (`lem:normalize` (c)). -/
theorem ae_measPairing_addConst {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {μ : Measure ℂ}
    [IsProbabilityMeasure μ] (hμ : IsRegular μ) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, measPairing (addConst (h ω) c) μ = measPairing (h ω) μ + c := by
  filter_upwards [MeasPair.ae_measPairing_addConst_of_isWholePlaneGFF hh hμ] with ω hω c
  rw [hω c, probReal_univ, mul_one]

/-- **`Z_b` is invariant under the normalization**, almost surely. -/
theorem ae_Zf_nrmF {γ b : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Zf γ b D (nrmF (h ω)) = Zf γ b D (h ω) := by
  filter_upwards [ae_dist_nrmF hD hh,
    ae_measPairing_addConst hh (isRegular_segMeasure (zero_ne_one (α := ℂ)))] with ω hd hp
  have hpos : 0 < (D (h ω)).1 (0, 1) := GaussianLQG.contMetric_pos _ zero_ne_one
  unfold Zf
  rw [hd, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp, nrmF, hp]
  ring

/-- **`G_θ` is invariant under the normalization**, almost surely, whenever `ψ_*λ` is a regular
probability measure. -/
theorem ae_probePair_nrmF {j : ℕ} {a θ : ℝ}
    (hμ1 : IsProbabilityMeasure ((segMeasure 0 1).map (probeInv j a θ)))
    (hμ : IsRegular ((segMeasure 0 1).map (probeInv j a θ)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, probePair j a θ (nrmF (h ω)) = probePair j a θ (h ω) := by
  filter_upwards [ae_measPairing_addConst hh hμ,
    ae_measPairing_addConst hh (isRegular_segMeasure (zero_ne_one (α := ℂ)))] with ω h1 h2
  unfold probePair nrmF
  rw [h1, h2]
  ring

/-! ## Pairings of a whole-plane GFF with two measures (`lem:pairing-variance`) -/

/-- **`∫⁻ ((h, μ) − (h, ν))² = ‖μ − ν‖_G²`** for every whole-plane GFF `h` and regular probability
measures `μ, ν`. -/
theorem lintegral_sq_measPairing_sub {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {μ ν : Measure ℂ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : IsRegular μ) (hν : IsRegular ν) :
    ∫⁻ ω, ENNReal.ofReal ((measPairing (h ω) μ - measPairing (h ω) ν) ^ 2) ∂P =
      ENNReal.ofReal (energyDistSq μ ν) := by
  obtain ⟨e, he, h₀, -, hm₀, hn₀, -, -, -, -, hpair⟩ := exists_coordRealization
  set F : DistC → ℝ≥0∞ := fun g => ENNReal.ofReal ((measPairing g μ - measPairing g ν) ^ 2)
    with hF_def
  have hF : Measurable F :=
    (((measurable_measPairing μ).sub (measurable_measPairing ν)).pow_const 2).ennreal_ofReal
  have h1 : ∫⁻ ω, F (h ω) ∂P = ∫⁻ ω, F (nrmF (h ω)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_measPairing_addConst hh hμ, ae_measPairing_addConst hh hν] with ω h1 h2
    simp only [hF_def, nrmF, h1, h2, add_sub_add_right_eq_sub]
  have h2 : ∫⁻ ω, F (nrmF (h ω)) ∂P = ∫⁻ ω, F (h₀ ω) ∂stdP := by
    have hm : Measurable fun ω => nrmF (h ω) := measurable_nrmF.comp hh.measurable
    rw [← lintegral_map hF hm, ← lintegral_map hF hm₀,
      map_eq_map_of_isNormalizedWPGFF (isNormalizedWPGFF_nrmF hh) hn₀]
  have h3 : ∫⁻ ω, F (h₀ ω) ∂stdP =
      ∫⁻ ω, ENNReal.ofReal ((pairing e μ ω - pairing e ν ω) ^ 2) ∂stdP := by
    refine lintegral_congr_ae ?_
    filter_upwards [pairing_ae_eq_measPairing (hpair μ hμ),
      pairing_ae_eq_measPairing (hpair ν hν)] with ω h1 h2
    simp only [hF_def, h1, h2]
  have hint : Integrable (fun ω => (pairing e μ ω - pairing e ν ω) ^ 2) stdP :=
    ((memLp_pairing he hμ (p := 2) ENNReal.ofNat_ne_top).sub
      (memLp_pairing he hν (p := 2) ENNReal.ofNat_ne_top)).integrable_sq
  rw [h1, h2, h3, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun ω => sq_nonneg _), integral_sq_pairing_sub he hμ hν, energyDistSq]

end SmallGammaGeodesics
