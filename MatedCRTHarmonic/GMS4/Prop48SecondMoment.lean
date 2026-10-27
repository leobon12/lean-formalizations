import MatedCRTHarmonic.GMS4.Prop48CircleConditioning

/-!
# The unconditional second-moment Fubini split

This is the corrected (4.30)–(4.31): the global good-event indicator is absent.
The only regularity inputs are integrability of the spatial product kernel and
of the squared spatial integral. These are ordinary Fubini hypotheses, not a
hypothesis of the desired near/far bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- Fubini expands the second moment of a spatial integral into its signed
pair covariance. The product integral identity itself requires no pointwise
integrability assumption because the Bochner integral has the standard zero
convention; the stated joint integrability justifies changing the order. -/
theorem prop48_secondMoment_fubini
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ))) :
    ∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P =
      ∫ p : V × V, (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ) := by
  calc
    (∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P) =
        ∫ ω, (∫ p : V × V, a ω p.1 * a ω p.2 ∂(μ.prod μ)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [integral_prod_mul]
      ring
    _ = ∫ p : V × V, (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ) :=
      integral_integral_swap htriple

/-- Joint integrability of the pair kernel already implies integrability of
The squared spatial integral, so the latter need not be a separate source
assumption when applying the Fubini split. -/
theorem prop48_square_integrable_of_triple
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ))) :
    Integrable (fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ)) P := by
  have hi : Integrable (fun ω => ∫ p : V × V,
      a ω p.1 * a ω p.2 ∂(μ.prod μ)) P := htriple.integral_prod_left
  apply hi.congr
  filter_upwards [] with ω
  rw [integral_prod_mul]
  ring

/-- The complete corrected second-moment split, including Fubini and the
near/far partition. The contributions are absolute covariances, which is
sufficient for the source's upper bounds and avoids a sign assumption. -/
theorem prop48_secondMoment_near_far_split
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (S : Set (V × V)) (hS : MeasurableSet S)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ)))
    (hsquare : Integrable (fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ)) P) :
    (∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂μ) ^ (2 : ℕ)) ∂P) ≤
      (∫⁻ p in S, ENNReal.ofReal
        |∫ ω, a ω p.1 * a ω p.2 ∂P| ∂(μ.prod μ)) +
      (∫⁻ p in Sᶜ, ENNReal.ofReal
        |∫ ω, a ω p.1 * a ω p.2 ∂P| ∂(μ.prod μ)) := by
  let C : V × V → ℝ := fun p => ∫ ω, a ω p.1 * a ω p.2 ∂P
  have hnonneg : 0 ≤ᵐ[P] fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hIntNonneg : 0 ≤ ∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  have hFubini := prop48_secondMoment_fubini a htriple
  have hC : Integrable C (μ.prod μ) := by
    exact htriple.swap.integral_prod_left
  calc
    (∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂μ) ^ (2 : ℕ)) ∂P) =
        ENNReal.ofReal (∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hsquare hnonneg).symm
    _ = ENNReal.ofReal (∫ p, C p ∂(μ.prod μ)) := by rw [hFubini]
    _ = ‖∫ p, C p ∂(μ.prod μ)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hFubini ▸ hIntNonneg)]
    _ ≤ ∫⁻ p, ‖C p‖ₑ ∂(μ.prod μ) := enorm_integral_le_lintegral_enorm _
    _ = (∫⁻ p in S, ENNReal.ofReal |C p| ∂(μ.prod μ)) +
        (∫⁻ p in Sᶜ, ENNReal.ofReal |C p| ∂(μ.prod μ)) := by
      simp_rw [Real.enorm_eq_ofReal_abs]
      exact (lintegral_add_compl (μ := μ.prod μ)
        (fun p => ENNReal.ofReal |C p|) hS).symm

/-- Source-faithful one-sided version of the split: the near calculation only
needs an upper bound on covariance. The far calculation can use the stronger
absolute A.3 estimate. -/
theorem prop48_secondMoment_near_far_positive_split
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    {P : Measure Ω} {μ : Measure V} [SFinite P] [SFinite μ]
    (a : Ω → V → ℝ)
    (S : Set (V × V)) (hS : MeasurableSet S)
    (htriple : Integrable (fun t : Ω × (V × V) =>
      a t.1 t.2.1 * a t.1 t.2.2) (P.prod (μ.prod μ)))
    (hsquare : Integrable (fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ)) P) :
    (∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂μ) ^ (2 : ℕ)) ∂P) ≤
      (∫⁻ p in S, ENNReal.ofReal
        (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ)) +
      (∫⁻ p in Sᶜ, ENNReal.ofReal
        (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μ.prod μ)) := by
  let C : V × V → ℝ := fun p => ∫ ω, a ω p.1 * a ω p.2 ∂P
  have hnonneg : 0 ≤ᵐ[P] fun ω => (∫ z, a ω z ∂μ) ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hFubini := prop48_secondMoment_fubini a htriple
  have hC : Integrable C (μ.prod μ) := htriple.swap.integral_prod_left
  have hCpos : Integrable (fun p => max (C p) 0) (μ.prod μ) := hC.pos_part
  have hmono : ∫ p, C p ∂(μ.prod μ) ≤
      ∫ p, max (C p) 0 ∂(μ.prod μ) :=
    integral_mono hC hCpos fun p => le_max_left _ _
  calc
    (∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂μ) ^ (2 : ℕ)) ∂P) =
        ENNReal.ofReal (∫ ω, (∫ z, a ω z ∂μ) ^ (2 : ℕ) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hsquare hnonneg).symm
    _ = ENNReal.ofReal (∫ p, C p ∂(μ.prod μ)) := by rw [hFubini]
    _ ≤ ENNReal.ofReal (∫ p, max (C p) 0 ∂(μ.prod μ)) :=
      ENNReal.ofReal_le_ofReal hmono
    _ = ∫⁻ p, ENNReal.ofReal (max (C p) 0) ∂(μ.prod μ) :=
      ofReal_integral_eq_lintegral_ofReal hCpos
        (Filter.Eventually.of_forall fun p => le_max_right _ _)
    _ = ∫⁻ p, ENNReal.ofReal (C p) ∂(μ.prod μ) := by
      congr 1
      funext p
      simp [ENNReal.ofReal_max]
    _ = (∫⁻ p in S, ENNReal.ofReal (C p) ∂(μ.prod μ)) +
        (∫⁻ p in Sᶜ, ENNReal.ofReal (C p) ∂(μ.prod μ)) :=
      (lintegral_add_compl (μ := μ.prod μ) (fun p => ENNReal.ofReal (C p)) hS).symm

/-- The constant-in-`ω` indicator used in the original fluctuation definition
agrees pointwise with the indicator defining the centered point observable. -/
theorem prop48_fluctuation_eq_centeredIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (L : Prop48LocalizedObservable P) (ω : Ω) :
    L.fluctuation ω = ∫ z in L.domain,
      L.test z * prop48PointwiseCentered L z ω ∂volume := by
  change (∫ z in L.domain, L.test z *
    ((L.localEvent z).indicator (fun _ => L.uStar ω z) ω - L.conditionalMean ω z)
    ∂volume) = _
  apply setIntegral_congr_fun L.measurableSet_domain
  intro z _
  by_cases hωz : ω ∈ L.localEvent z
  · simp [prop48PointwiseCentered, Set.indicator_of_mem hωz]
  · simp [prop48PointwiseCentered, Set.indicator_of_notMem hωz]

/-- The source localized observable satisfies the (4.30)–(4.31) moment split
once its joint product kernel and squared spatial integral are integrable.
The two contributions are defined by the actual pair covariance, with the
test weights kept inside the covariance. -/
theorem prop48_localized_fluctuation_near_far_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (L : Prop48LocalizedObservable P) (r : ℝ)
    (htriple : Integrable (fun t : Ω × (ℂ × ℂ) =>
      (L.test t.2.1 * prop48PointwiseCentered L t.2.1 t.1) *
        (L.test t.2.2 * prop48PointwiseCentered L t.2.2 t.1))
      (P.prod ((volume.restrict L.domain).prod (volume.restrict L.domain))))
    (hsquare : Integrable (fun ω => L.fluctuation ω ^ (2 : ℕ)) P) :
    L27MomentIntegralRegularityInput P L.fluctuation
      (∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r},
        ENNReal.ofReal |∫ ω,
          (L.test p.1 * prop48PointwiseCentered L p.1 ω) *
            (L.test p.2 * prop48PointwiseCentered L p.2 ω) ∂P|
        ∂((volume.restrict L.domain).prod (volume.restrict L.domain)))
      (∫⁻ p in {p : ℂ × ℂ | r < dist p.1 p.2},
        ENNReal.ofReal |∫ ω,
          (L.test p.1 * prop48PointwiseCentered L p.1 ω) *
            (L.test p.2 * prop48PointwiseCentered L p.2 ω) ∂P|
        ∂((volume.restrict L.domain).prod (volume.restrict L.domain))) := by
  let μD : Measure ℂ := volume.restrict L.domain
  let a : Ω → ℂ → ℝ := fun ω z => L.test z * prop48PointwiseCentered L z ω
  have hS : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
    measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
  have hfluc (ω : Ω) : L.fluctuation ω = ∫ z, a ω z ∂μD :=
    prop48_fluctuation_eq_centeredIntegral L ω
  have hsplit := prop48_secondMoment_near_far_split
    (P := P) (μ := μD) a {p : ℂ × ℂ | dist p.1 p.2 ≤ r} hS htriple hsquare
  change (∫⁻ ω, ENNReal.ofReal (L.fluctuation ω ^ (2 : ℕ)) ∂P) ≤
    (∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r},
      ENNReal.ofReal |∫ ω, a ω p.1 * a ω p.2 ∂P| ∂(μD.prod μD)) +
    (∫⁻ p in {p : ℂ × ℂ | r < dist p.1 p.2},
      ENNReal.ofReal |∫ ω, a ω p.1 * a ω p.2 ∂P| ∂(μD.prod μD))
  simpa only [a, μD, Set.compl_ofPred, not_le, ← hfluc] using hsplit

/-- The source localized fluctuation with the exact one-sided covariance
split used by (4.32). -/
theorem prop48_localized_fluctuation_positive_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (L : Prop48LocalizedObservable P) (r : ℝ)
    (htriple : Integrable (fun t : Ω × (ℂ × ℂ) =>
      (L.test t.2.1 * prop48PointwiseCentered L t.2.1 t.1) *
        (L.test t.2.2 * prop48PointwiseCentered L t.2.2 t.1))
      (P.prod ((volume.restrict L.domain).prod (volume.restrict L.domain))))
    (hsquare : Integrable (fun ω => L.fluctuation ω ^ (2 : ℕ)) P) :
    L27MomentIntegralRegularityInput P L.fluctuation
      (∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r},
        ENNReal.ofReal (∫ ω,
          (L.test p.1 * prop48PointwiseCentered L p.1 ω) *
            (L.test p.2 * prop48PointwiseCentered L p.2 ω) ∂P)
        ∂((volume.restrict L.domain).prod (volume.restrict L.domain)))
      (∫⁻ p in {p : ℂ × ℂ | r < dist p.1 p.2},
        ENNReal.ofReal (∫ ω,
          (L.test p.1 * prop48PointwiseCentered L p.1 ω) *
            (L.test p.2 * prop48PointwiseCentered L p.2 ω) ∂P)
        ∂((volume.restrict L.domain).prod (volume.restrict L.domain))) := by
  let μD : Measure ℂ := volume.restrict L.domain
  let a : Ω → ℂ → ℝ := fun ω z => L.test z * prop48PointwiseCentered L z ω
  have hS : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
    measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
  have hfluc (ω : Ω) : L.fluctuation ω = ∫ z, a ω z ∂μD :=
    prop48_fluctuation_eq_centeredIntegral L ω
  have hsplit := prop48_secondMoment_near_far_positive_split
    (P := P) (μ := μD) a {p : ℂ × ℂ | dist p.1 p.2 ≤ r} hS htriple hsquare
  change (∫⁻ ω, ENNReal.ofReal (L.fluctuation ω ^ (2 : ℕ)) ∂P) ≤
    (∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r},
      ENNReal.ofReal (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μD.prod μD)) +
    (∫⁻ p in {p : ℂ × ℂ | r < dist p.1 p.2},
      ENNReal.ofReal (∫ ω, a ω p.1 * a ω p.2 ∂P) ∂(μD.prod μD))
  simpa only [a, μD, Set.compl_ofPred, not_le, ← hfluc] using hsplit

end MatedCRTHarmonic.GMS4

