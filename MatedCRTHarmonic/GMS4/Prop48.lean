import MatedCRTHarmonic.GMSLemma27.CellModel
import MatedCRTHarmonic.GMSLemma27.SLEInterfaces
import MatedCRTHarmonic.GMS4b.JointMeasurable
import MatedCRTHarmonic.GMS4b.BundleAdapter
import MatedCRTHarmonic.GMS4b.UStarMoments
import MatedCRTHarmonic.GMS4b.Interfaces
import MatedCRTHarmonic.GMS4b.Packing
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import MatedCRTHarmonic.CellScaling.ConeDefs
import MatedCRTHarmonic.GMCFacts.ConeCompare
import MatedCRTHarmonic.LQGCoord.Transform
import MatedCRTHarmonic.GMS4c.Lemma49Observable
import MatedCRTHarmonic.GMS4c.BundleExcursions
import MatedCRTHarmonic.CellScaling.ZeroConeScalingCells
import MatedCRTHarmonic.LQGCone.AreaBridge
import MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import MatedCRTHarmonic.MesoModel.FrozenIdentities

/-!
# The second-moment conclusion in [18] Proposition 4.8

Source: Gwynne--Miller--Sheffield, *Harmonic functions on mated-CRT maps*,
 (equation (4.38) and the Chebyshev step in
Step 3 of Proposition 4.8). The source obtains an uncentered second-moment estimate for the
localized-density integral and applies Chebyshev with a positive threshold. The theorem below
records exactly that generic implication, including its failure probability.

The closest library result is Mathlib's `mul_meas_ge_le_lintegral₀` (Markov's inequality). We
specialize it to the square of a real random variable. This is only the concentration core; it
does not assume any of the field, cell, or localized-density estimates that produce the
second-moment premise in Proposition 4.8.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4

/-- **Second moment / Chebyshev implication used after [18, (4.38)].**

If the uncentered second moment of `X` is at most
`bound^2 * (C * ε^α)`, then the probability that `X` exceeds the positive threshold `bound`
is at most `C * ε^α`. The use of a one-sided event matches Proposition 4.8's required upper-tail
estimate; no centering hypothesis is needed once the second-moment bound has been established. -/
theorem measure_gt_le_of_lintegral_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ}
    (hX : AEMeasurable X P) {bound C ε α : ℝ} (hbound : 0 < bound)
    (hsecond : (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) ≤
      ENNReal.ofReal (bound ^ 2 * (C * ε ^ α))) :
    P {ω | bound < X ω} ≤ ENNReal.ofReal (C * ε ^ α) := by
  let t : ℝ≥0∞ := ENNReal.ofReal (bound ^ 2)
  let f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (X ω ^ 2)
  have ht0 : t ≠ 0 := by
    change ENNReal.ofReal (bound ^ 2) ≠ 0
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have htt : t ≠ ⊤ := by simp [t]
  have hXsq : AEMeasurable (fun ω => X ω ^ 2) P := by
    have heq : (fun ω => X ω ^ 2) = X * X := by
      funext ω
      simp [pow_two]
    rw [heq]
    exact hX.mul hX
  have hf : AEMeasurable f P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hXsq
  have hsubset : {ω | bound < X ω} ⊆ {ω | t ≤ f ω} := by
    intro ω hω
    change bound < X ω at hω
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hmul : t * P {ω | bound < X ω} ≤
      t * ENNReal.ofReal (C * ε ^ α) := by
    calc
      t * P {ω | bound < X ω} ≤ t * P {ω | t ≤ f ω} :=
        mul_le_mul' le_rfl (measure_mono hsubset)
      _ ≤ ∫⁻ ω, f ω ∂P := mul_meas_ge_le_lintegral₀ hf t
      _ ≤ ENNReal.ofReal (bound ^ 2 * (C * ε ^ α)) := hsecond
      _ = t * ENNReal.ofReal (C * ε ^ α) := by
        rw [ENNReal.ofReal_mul (sq_nonneg bound)]
  exact (ENNReal.mul_le_mul_iff_left ht0 htt).mp (by simpa [mul_comm] using hmul)

/-! ## The source-level completion boundary

The following three predicates keep the still-missing producers separate. In particular, none of
them assumes (4.38) or the conclusion of Proposition 4.8.
-/

/-- **L27 regularity/locality interface.** The corrected second-moment expansion (4.30) is the
unconditional second moment of the centered localized observable: it contains no indicator of
The global event `E^ε`. Measurability and Fubini justify the expansion, and the near/far partition
(4.31) splits it into two nonnegative contributions. Source: [18, Proposition 4.8], using the unconditional second-moment correction. Producer classification: **L27** (localized cell observables and their measurability). -/
def L27MomentIntegralRegularityInput {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (nearContribution farContribution : ℝ≥0∞) : Prop :=
  (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) ≤ nearContribution + farContribution

/-- **localized conditional-moment interface.** Equations (4.24)--(4.27), the local event
`F^ε(z)`, and the degree/area comparison imply the near-pair estimate (4.32)--(4.34). The outer-degree
estimate here uses the conditional area-ratio moment (4.24) and the degree cap in `F^ε(z)`; it does
not use a small-ball mass tail. Separately, [16, Lemma A.3]'s *upper*-mass estimate repairs the
lower diameter bound in (4.18) and hence belongs to the global regularity producer, whereas
Lemma 2.8 is a *lower*-mass estimate. This predicate records only the near contribution to the
corrected unconditional second-moment split, normalized by the eventual Chebyshev threshold.
Source: [18, Proposition 4.8], with the unconditional form of (4.36). Producer classification:
**mixed local and the analytic construction** (localized `u_*`, `DA^ε`, degree, conditional moments, and cell moments). -/
def L27LocalizedConditionalMomentInput
    (nearContribution : ℝ≥0∞) (bound nearFailure : ℝ) : Prop :=
  nearContribution ≤ ENNReal.ofReal (bound ^ 2 * nearFailure)

/-- **the analytic construction exterior-decorrelation interface.** The concrete GFF specialization of Appendix A.3,
together with locality of the localized observable, yields (4.35)--(4.37) for far pairs. The global
event `E^ε` is deliberately absent: the corrected argument takes this conditional
expectation without `1_{E^ε}`. Source: [18, Proposition 4.8]. Producer classification: **Gaussian and local estimates**
(Appendix A.3/A.5 Radon--Nikodym localization plus L27 exterior measurability). -/
def GMSAExteriorDecorrelationInput
    (farContribution : ℝ≥0∞) (bound farFailure : ℝ) : Prop :=
  farContribution ≤ ENNReal.ofReal (bound ^ 2 * farFailure)

/-- The corrected near/far inputs imply the Proposition 4.8 upper-tail estimate. This is the
source's Step 3 after the two contributions have been produced; unlike the
printed (4.36), the exterior input above contains no global-event indicator. -/
theorem prop48_event_estimate_of_near_far_inputs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ}
    (hX : AEMeasurable X P) {bound nearFailure farFailure : ℝ} (hbound : 0 < bound)
    (hnearFailure : 0 ≤ nearFailure) (hfarFailure : 0 ≤ farFailure)
    {nearContribution farContribution : ℝ≥0∞}
    (hregularity : L27MomentIntegralRegularityInput P X nearContribution farContribution)
    (hnear : L27LocalizedConditionalMomentInput nearContribution bound nearFailure)
    (hfar : GMSAExteriorDecorrelationInput farContribution bound farFailure) :
    P {ω | bound < X ω} ≤ ENNReal.ofReal (nearFailure + farFailure) := by
  have hsecond : (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) ≤
      ENNReal.ofReal (bound ^ 2 * ((nearFailure + farFailure) * (1 : ℝ) ^ (1 : ℝ))) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) ≤ nearContribution + farContribution :=
        hregularity
      _ ≤ ENNReal.ofReal (bound ^ 2 * nearFailure) +
          ENNReal.ofReal (bound ^ 2 * farFailure) := add_le_add hnear hfar
      _ = ENNReal.ofReal (bound ^ 2 * ((nearFailure + farFailure) * (1 : ℝ) ^ (1 : ℝ))) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg bound) hnearFailure)
          (mul_nonneg (sq_nonneg bound) hfarFailure)]
        norm_num
        ring_nf
  simpa using measure_gt_le_of_lintegral_sq_le P hX hbound hsecond

/-! ## Source-facing localized observable -/

/-- Minimal L27 data for the localized observable in [18, (4.27)--(4.29)]. The random variable
used below is the integral of
`1_{F^ε(z)} u_*^ε(z) - E[1_{F^ε(z)}u_*^ε(z) | local circle averages]`.

The last three fields are the exact regularity outputs needed to pass from this definition to the
good-event inequality: local truncation agrees with `u_*` on `E^ε`, the conditional mean integrates
to at most `A ∫ f`, and integration commutes with the subtraction. Source: [18, Proposition 4.8];
producer classification: **L27** (local observable/measurability) together with the conditional
moment output (4.27). -/
structure Prop48LocalizedObservable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The integration domain `D`. -/
  domain : Set ℂ
  measurableSet_domain : MeasurableSet domain
  /-- The nonnegative test function `f`. -/
  test : ℂ → ℝ
  /-- The localized density `u_*^ε`. -/
  uStar : Ω → ℂ → ℝ
  /-- The pointwise local event `F^ε(z)`. -/
  localEvent : ℂ → Set Ω
  /-- The conditional expectation in (4.27)--(4.28). -/
  conditionalMean : Ω → ℂ → ℝ
  /-- The global good event `E^ε`. -/
  goodEvent : Set Ω
  /-- The deterministic conditional-mean constant `A`. -/
  meanConstant : ℝ
  aeMeasurable_fluctuation : AEMeasurable (fun ω =>
    ∫ z in domain, test z *
      ((localEvent z).indicator (fun _ => uStar ω z) ω - conditionalMean ω z)) P
  localEvent_of_good : ∀ ω ∈ goodEvent, ∀ z ∈ domain, ω ∈ localEvent z
  conditionalIntegral_le : ∀ ω ∈ goodEvent,
    (∫ z in domain, test z * conditionalMean ω z) ≤
      meanConstant * ∫ z in domain, test z
  integral_subtraction : ∀ ω ∈ goodEvent,
    (∫ z in domain, test z *
      ((localEvent z).indicator (fun _ => uStar ω z) ω - conditionalMean ω z)) =
      (∫ z in domain, test z *
        (localEvent z).indicator (fun _ => uStar ω z) ω) -
      ∫ z in domain, test z * conditionalMean ω z

/-- The centered, locally truncated integral from [18, (4.28)--(4.29)]. -/
def Prop48LocalizedObservable.fluctuation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (L : Prop48LocalizedObservable P) (ω : Ω) : ℝ :=
  ∫ z in L.domain, L.test z *
    ((L.localEvent z).indicator (fun _ => L.uStar ω z) ω - L.conditionalMean ω z)

/-- The uncentered localized-density integral appearing in the Proposition 4.8 event. -/
def Prop48LocalizedObservable.localizedIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (L : Prop48LocalizedObservable P) (ω : Ω) : ℝ :=
  ∫ z in L.domain, L.test z * L.uStar ω z

/-- On `E^ε`, exceeding the conditional-mean main term by `bound` forces the centered localized
integral to exceed `bound` (the deterministic implication (4.29)). -/
theorem Prop48LocalizedObservable.good_failure_subset_fluctuation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (L : Prop48LocalizedObservable P) {bound : ℝ} :
    L.goodEvent ∩ {ω | L.meanConstant * (∫ z in L.domain, L.test z) + bound <
      L.localizedIntegral ω} ⊆ {ω | bound < L.fluctuation ω} := by
  rintro ω ⟨hgood, hlarge⟩
  change L.meanConstant * (∫ z in L.domain, L.test z) + bound <
    (∫ z in L.domain, L.test z * L.uStar ω z) at hlarge
  change bound < ∫ z in L.domain, L.test z *
    ((L.localEvent z).indicator (fun _ => L.uStar ω z) ω - L.conditionalMean ω z)
  rw [L.integral_subtraction ω hgood]
  have htruncate : (∫ z in L.domain, L.test z *
      (L.localEvent z).indicator (fun _ => L.uStar ω z) ω) =
      ∫ z in L.domain, L.test z * L.uStar ω z := by
    apply setIntegral_congr_fun L.measurableSet_domain
    intro z hz
    change L.test z * (L.localEvent z).indicator (fun _ => L.uStar ω z) ω =
      L.test z * L.uStar ω z
    rw [Set.indicator_of_mem (L.localEvent_of_good ω hgood z hz)]
  rw [htruncate]
  linarith [L.conditionalIntegral_le ω hgood]

/-- **Proposition 4.8 good-event conclusion at the completion boundary.** Once the separately named
near-pair (4.34) and corrected far-pair (4.37) producers are supplied for the actual localized
fluctuation, its upper-tail failure inside `E^ε` is at most the sum of their failure budgets.
Source: [18, Proposition 4.8]. -/
theorem prop48_good_event_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Prop48LocalizedObservable P)
    {bound nearFailure farFailure : ℝ} (hbound : 0 < bound)
    (hnearFailure : 0 ≤ nearFailure) (hfarFailure : 0 ≤ farFailure)
    {nearContribution farContribution : ℝ≥0∞}
    (hregularity : L27MomentIntegralRegularityInput P L.fluctuation
      nearContribution farContribution)
    (hnear : L27LocalizedConditionalMomentInput nearContribution bound nearFailure)
    (hfar : GMSAExteriorDecorrelationInput farContribution bound farFailure) :
    P (L.goodEvent ∩ {ω | L.meanConstant * (∫ z in L.domain, L.test z) + bound <
      L.localizedIntegral ω}) ≤ ENNReal.ofReal (nearFailure + farFailure) := by
  refine (measure_mono (L.good_failure_subset_fluctuation (bound := bound))).trans ?_
  exact prop48_event_estimate_of_near_far_inputs P L.aeMeasurable_fluctuation hbound
    hnearFailure hfarFailure hregularity hnear hfar

/-- **L27 Proposition 4.5 regularity-failure input.** The complement of the global event `E^ε`
has the indicated polynomial failure budget. Source: [18] Proposition 4.5 and Step 3. Producer classification: **local** (cell diameter, degree, and
circle-average regularity). -/
def L27RegularityFailureInput {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (goodEvent : Set Ω) (regularityFailure : ℝ) : Prop :=
  P goodEventᶜ ≤ ENNReal.ofReal regularityFailure

/-- The unrestricted Proposition 4.8 event estimate obtained by adding the Proposition 4.5
regularity failure to the corrected good-event estimate. -/
theorem prop48_event_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Prop48LocalizedObservable P)
    {bound regularityFailure nearFailure farFailure : ℝ} (hbound : 0 < bound)
    (hregularityFailure : 0 ≤ regularityFailure)
    (hnearFailure : 0 ≤ nearFailure) (hfarFailure : 0 ≤ farFailure)
    {nearContribution farContribution : ℝ≥0∞}
    (hgood : L27RegularityFailureInput P L.goodEvent regularityFailure)
    (hmoment : L27MomentIntegralRegularityInput P L.fluctuation
      nearContribution farContribution)
    (hnear : L27LocalizedConditionalMomentInput nearContribution bound nearFailure)
    (hfar : GMSAExteriorDecorrelationInput farContribution bound farFailure) :
    P {ω | L.meanConstant * (∫ z in L.domain, L.test z) + bound <
      L.localizedIntegral ω} ≤
      ENNReal.ofReal (regularityFailure + nearFailure + farFailure) := by
  let bad : Set Ω := {ω | L.meanConstant * (∫ z in L.domain, L.test z) + bound <
    L.localizedIntegral ω}
  have hsubset : bad ⊆ L.goodEventᶜ ∪ (L.goodEvent ∩ bad) := by
    intro ω hω
    by_cases hg : ω ∈ L.goodEvent
    · exact Or.inr ⟨hg, hω⟩
    · exact Or.inl hg
  have hinside : P (L.goodEvent ∩ bad) ≤ ENNReal.ofReal (nearFailure + farFailure) :=
    prop48_good_event_estimate P L hbound hnearFailure hfarFailure hmoment hnear hfar
  calc
    P bad ≤ P (L.goodEventᶜ ∪ (L.goodEvent ∩ bad)) := measure_mono hsubset
    _ ≤ P L.goodEventᶜ + P (L.goodEvent ∩ bad) := measure_union_le _ _
    _ ≤ ENNReal.ofReal regularityFailure + ENNReal.ofReal (nearFailure + farFailure) :=
      add_le_add hgood hinside
    _ = ENNReal.ofReal (regularityFailure + nearFailure + farFailure) := by
      rw [← ENNReal.ofReal_add hregularityFailure (add_nonneg hnearFailure hfarFailure)]
      congr 1
      ring

/-! ## L27 cell-model specialization -/

/-- The exact localized-observable output still required from L27 for a concrete
`GMSLemma27.CellModel γ`. This is a data interface indexed by the model, so its probability measure
is definitionally `M.P`; it adds no probabilistic conclusion to `Prop48LocalizedObservable`.
Producer classification: **local**, using the cell/field/curve data of `CellModel` and the
localized definitions in [18] . -/
abbrev L27CellModelLocalizedObservable {γ : ℝ}
    (M : MatedCRTHarmonic.GMSLemma27.CellModel γ) :=
  Prop48LocalizedObservable M.P

/-- **Missing L27 producer data for the actual source observable.** The current `CellModel` has the
field, area measure, and curve, but does not yet define the local structure graph, `τ_z`, the area
ratio `DA^ε`, the in/out degrees, or the IG circle average. This interface names those lower-level
outputs explicitly and enforces both source formulas:

* `u_*^ε(z) = DA^ε(z) (deg_in^ε(z) + deg_out^ε(z))`, [18, (4.19), ];
* `F^ε(z)` is exactly the conjunction of the three local conditions at [18] .

The source's SLE input `SegmentsContainBalls` ([GHM15, Proposition 3.4 and Remark 3.9],
`GMSLemma27/SLEInterfaces.lean`) is included explicitly. The final two fields identify these
source objects with the localized integral data. No probability or Proposition 4.8 conclusion is
included. Producer classification: **local**. -/
structure L27CellModelProp48Data {γ : ℝ}
    (M : MatedCRTHarmonic.GMSLemma27.CellModel γ) (ε q ζ : ℝ) where
  /-- The SLE-only segment-ball input used to control outer degree; see
  `GMSLemma27.SLEInterfaces.SegmentsContainBalls` and [18] . -/
  segmentsContainBalls : MatedCRTHarmonic.GMSLemma27.SegmentsContainBalls M
  /-- `DA^ε(z)`, the area ratio from [18, §4.2]. -/
  areaRatio : M.Ω → ℂ → ℝ
  /-- `deg_in^ε(z)` in the local structure graph. -/
  degreeIn : M.Ω → ℂ → ℕ
  /-- `deg_out^ε(z)` in the local structure graph. -/
  degreeOut : M.Ω → ℂ → ℕ
  /-- `diam(η([τ_z-ε,τ_z+ε]))`. -/
  localSegmentDiameter : M.Ω → ℂ → ℝ
  /-- The circle average `h_{ε^{q-4ζ}}(z)`. -/
  fieldCircleAverage : M.Ω → ℂ → ℝ
  /-- The IG-field circle average `h^{IG}_{ε^{q-4ζ}}(z)`. -/
  igCircleAverage : M.Ω → ℂ → ℝ
  /-- The source localized density `u_*^ε`. -/
  uStar : M.Ω → ℂ → ℝ
  /-- The local event `F^ε(z)`. -/
  localEvent : ℂ → Set M.Ω
  uStar_formula : ∀ ω z, uStar ω z =
    areaRatio ω z * ((degreeIn ω z + degreeOut ω z : ℕ) : ℝ)
  localEvent_formula : ∀ ω z, ω ∈ localEvent z ↔
    localSegmentDiameter ω z ≤ ε ^ q ∧
    ((degreeIn ω z + degreeOut ω z : ℕ) : ℝ) ≤ ε ^ (-ζ) ∧
    max |fieldCircleAverage ω z| |igCircleAverage ω z| ≤ 2 * q * Real.log ε⁻¹
  localizedObservable : L27CellModelLocalizedObservable M
  localized_uStar : ∀ ω z, localizedObservable.uStar ω z = uStar ω z
  localized_event : ∀ z, localizedObservable.localEvent z = localEvent z

/-- **[18] Proposition 4.8, cell-model good-event boundary.** For an L27 localized observable on
The concrete cell-model probability space, the named moment-expansion, near-pair (4.34), and
corrected Gaussian and local far-pair (4.37) outputs imply the claimed high-probability integral estimate on
`E^ε`. The hypotheses remain strictly below Proposition 4.8: they are the two contribution bounds
and the Fubini split, and no hypothesis states this event conclusion. -/
theorem prop48_cellModel_good_event_estimate
    {γ : ℝ} (M : MatedCRTHarmonic.GMSLemma27.CellModel γ)
    (L : L27CellModelLocalizedObservable M)
    {bound nearFailure farFailure : ℝ} (hbound : 0 < bound)
    (hnearFailure : 0 ≤ nearFailure) (hfarFailure : 0 ≤ farFailure)
    {nearContribution farContribution : ℝ≥0∞}
    (hregularity : L27MomentIntegralRegularityInput M.P L.fluctuation
      nearContribution farContribution)
    (hnear : L27LocalizedConditionalMomentInput nearContribution bound nearFailure)
    (hfar : GMSAExteriorDecorrelationInput farContribution bound farFailure) :
    M.P (L.goodEvent ∩ {ω | L.meanConstant * (∫ z in L.domain, L.test z) + bound <
      L.localizedIntegral ω}) ≤ ENNReal.ofReal (nearFailure + farFailure) :=
  prop48_good_event_estimate M.P L hbound hnearFailure hfarFailure hregularity hnear hfar

/-- The cell-model estimate specialized to the actual `(4.19)` observable and `(4.22)` local event
named by `L27CellModelProp48Data`. The remaining assumptions are precisely the regularity/Fubini,
near-pair, and corrected far-pair contribution producers. -/
theorem prop48_cellModel_source_observable_good_event_estimate
    {γ ε q ζ : ℝ} (M : MatedCRTHarmonic.GMSLemma27.CellModel γ)
    (D : L27CellModelProp48Data M ε q ζ)
    {bound nearFailure farFailure : ℝ} (hbound : 0 < bound)
    (hnearFailure : 0 ≤ nearFailure) (hfarFailure : 0 ≤ farFailure)
    {nearContribution farContribution : ℝ≥0∞}
    (hregularity : L27MomentIntegralRegularityInput M.P D.localizedObservable.fluctuation
      nearContribution farContribution)
    (hnear : L27LocalizedConditionalMomentInput nearContribution bound nearFailure)
    (hfar : GMSAExteriorDecorrelationInput farContribution bound farFailure) :
    M.P (D.localizedObservable.goodEvent ∩ {ω |
      D.localizedObservable.meanConstant *
          (∫ z in D.localizedObservable.domain, D.localizedObservable.test z) + bound <
        D.localizedObservable.localizedIntegral ω}) ≤
      ENNReal.ofReal (nearFailure + farFailure) :=
  prop48_cellModel_good_event_estimate M D.localizedObservable hbound hnearFailure hfarFailure
    hregularity hnear hfar

/-- **Full cell-model Proposition 4.8 boundary.** This adds the separately named Proposition 4.5
failure budget to `prop48_cellModel_source_observable_good_event_estimate`; the far-pair producer
remains the corrected one without a global-event indicator. -/
theorem prop48_cellModel_source_observable_event_estimate
    {γ ε q ζ : ℝ} (M : MatedCRTHarmonic.GMSLemma27.CellModel γ)
    (D : L27CellModelProp48Data M ε q ζ)
    {bound regularityFailure nearFailure farFailure : ℝ} (hbound : 0 < bound)
    (hregularityFailure : 0 ≤ regularityFailure)
    (hnearFailure : 0 ≤ nearFailure) (hfarFailure : 0 ≤ farFailure)
    {nearContribution farContribution : ℝ≥0∞}
    (hgood : L27RegularityFailureInput M.P D.localizedObservable.goodEvent regularityFailure)
    (hmoment : L27MomentIntegralRegularityInput M.P D.localizedObservable.fluctuation
      nearContribution farContribution)
    (hnear : L27LocalizedConditionalMomentInput nearContribution bound nearFailure)
    (hfar : GMSAExteriorDecorrelationInput farContribution bound farFailure) :
    M.P {ω | D.localizedObservable.meanConstant *
        (∫ z in D.localizedObservable.domain, D.localizedObservable.test z) + bound <
      D.localizedObservable.localizedIntegral ω} ≤
      ENNReal.ofReal (regularityFailure + nearFailure + farFailure) :=
  prop48_event_estimate M.P D.localizedObservable hbound hregularityFailure hnearFailure
    hfarFailure hgood hmoment hnear hfar

/-! ### The concrete zero-cone realization used in Proposition 4.8 -/

open MatedCRTHarmonic.MatedCRT

/-- The bundle's 0-cone field and area-parametrized curve, packaged as an L27 cell model.
The area-parametrization proof uses the v3 `areaParam₀` field only after the SLE-free
existence of the dyadic vague limit has been supplied by `FrozenIdentities`. -/
def prop48ZeroConeCellModel
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    MatedCRTHarmonic.GMSLemma27.CellModel γ where
  Ω := Ω
  measurableSpace := inferInstance
  P := P
  isProbabilityMeasure := D.isProbabilityMeasure
  field := fun ω => coneField (X₀ ω)
    (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
  area := fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ
    (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))
  curve := fun ω => η₀ ω
  ae_continuous_curve := Filter.Eventually.of_forall fun ω => (η₀ ω).continuous
  ae_curve_zero := by
    filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace
    rcases harea.1 with ⟨φ, hφ0, hηeq⟩
    rw [hηeq, hφ0, hspace.2.2.1]
  ae_area_curve := by
    filter_upwards [D.areaParam₀,
      MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ]
      with ω harea hex
    have hex' : ∃ μ : Measure ℂ, MatedCRTHarmonic.CellScaling.IsVagueLimitC
        (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ
          (coneField (X₀ ω)
            (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) μ := hex
    rw [MatedCRTHarmonic.CellScaling.lqgArea, dif_pos hex']
    exact harea.2 _ hex'.choose_spec

/-- The literal extended-real localized density (4.19) on the bundle's 0-cone curve. -/
def prop48ZeroConeUStar
    {Ω : Type} [MeasurableSpace Ω] (η₀ : Ω → C(ℝ, ℂ))
    (ε : ℝ) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  GMS4b.uStar ε (η₀ ω) z

theorem prop48ZeroConeUStar_eq_areaRatio_mul_degrees
    {Ω : Type} [MeasurableSpace Ω] (η₀ : Ω → C(ℝ, ℂ))
    (ε : ℝ) (ω : Ω) (z : ℂ) :
    prop48ZeroConeUStar η₀ ε ω z =
      GMS4b.areaRatio ε (η₀ ω) z *
        (((GMS4b.degreeIn ε (η₀ ω) z + GMS4b.degreeOut ε (η₀ ω) z : ℕ∞) : ℝ≥0∞)) :=
  rfl

/-- The source's local degree sum, retaining the natural-infinity carrier. -/
def prop48ZeroConeDegreeSum
    {Ω : Type} (η₀ : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) (z : ℂ) : ℕ∞ :=
  GMS4b.degreeIn ε (η₀ ω) z + GMS4b.degreeOut ε (η₀ ω) z

/-- The radius-`r` average of the 0-cone field used in the local event. -/
def prop48ZeroConeCircleAverage
    {Ω : Type} (γ : ℝ) (X₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (r : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  LQGMetric.circleAvg
    (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) r z

/-- The 0-cone field is almost surely measurable, using the Brownian cone-process
realization of the frozen bundle. -/
theorem aemeasurable_prop48ZeroConeField
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) P := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  let A : ℝ → Ω → ℝ := fun t ω =>
    MatedCRTHarmonic.LQGCone.motConeRadial γ 0
      (fun s => B₀ s ω) (fun s => B₀' s ω) t
  have hA : MatedCRTHarmonic.MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ) A P :=
    MatedCRTHarmonic.LQGCone.isConeProcess_motConeRadial
      D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hm := MatedCRTHarmonic.MoTPort.ConeMeas2.aemeasurable_coneField D.gff₀ hA
  refine hm.congr (ae_of_all _ fun ω => ?_)
  exact (MatedCRTHarmonic.LQGCone.coneField_eq_motConeField γ 0 (X₀ ω)
    (fun t => B₀ t ω) (fun t => B₀' t ω)).symm

theorem aemeasurable_prop48ZeroConeCircleAverage
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (r : ℝ) (z : ℂ) :
    AEMeasurable (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' r · z) P := by
  exact (LQGMetric.measurable_circleAvg_left r z).comp_aemeasurable
    (aemeasurable_prop48ZeroConeField D)

/-- The remaining Lemma 4.3 input used below: a Borel reconstruction of
The restricted canonical GMC measure from the restricted field. the reconstruction has
already proved the independent IG-excursion reconstruction. -/
structure Prop48LocalGMCFromFieldInput
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (h : Ω → MatedCRT.Field)
    (V : TopologicalSpace.Opens ℂ) where
  reconstruct : LQGMetric.DistOn V → Measure ℂ
  measurable_reconstruct : Measurable reconstruct
  ae_reconstruct : (fun ω => reconstruct (LQGMetric.restrictTo V (h ω))) =ᵐ[P]
    fun ω => (MatedCRTHarmonic.CellScaling.lqgArea γ (h ω)).restrict V

/-- the S7 reconstruction and a local GMC map give the actual zero-cone
local configuration as a measurable function of the field restriction and
independent IG data. This is the local-law transfer's reconstruction step. -/
theorem prop48_zeroCone_localConfiguration_from_localFields
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (δ : ℝ) (hδ : 0 < δ)
    (A : Prop48LocalGMCFromFieldInput P γ
      (fun ω => coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) V) :
    ∃ F : (LQGMetric.DistOn V ×
        (LQGMetric.DistOn
          (⟨Metric.thickening δ (V : Set ℂ), Metric.isOpen_thickening⟩ :
            TopologicalSpace.Opens ℂ) × ℝ)) → GMS4c.LocalConfiguration V,
      Measurable F ∧ ∀ᵐ ω ∂P,
        F (LQGMetric.restrictTo V
            (coneField (X₀ ω)
              (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))),
          (LQGMetric.restrictTo
            (⟨Metric.thickening δ (V : Set ℂ), Metric.isOpen_thickening⟩ :
              TopologicalSpace.Opens ℂ) (hIG₀ ω), U ω)) =
          GMS4c.localConfiguration V
            (MatedCRTHarmonic.CellScaling.lqgArea γ
              (coneField (X₀ ω)
                (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))))
            (coneField (X₀ ω)
              (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) (ηL ω) := by
  let h₀ : Ω → MatedCRT.Field := fun ω => coneField (X₀ ω)
    (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
  let μ : Ω → Measure ℂ := fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ (h₀ ω)
  obtain ⟨G, hG, hGeq⟩ :=
    GMS4c.ae_bundle_localConfiguration_from_localAreaIG D V hVb δ hδ μ h₀
  let F : (LQGMetric.DistOn V ×
      (LQGMetric.DistOn
        (⟨Metric.thickening δ (V : Set ℂ), Metric.isOpen_thickening⟩ :
          TopologicalSpace.Opens ℂ) × ℝ)) → GMS4c.LocalConfiguration V :=
    fun x => G ((A.reconstruct x.1, x.1), x.2)
  have hF : Measurable F :=
    hG.comp (((A.measurable_reconstruct.comp measurable_fst).prodMk measurable_fst).prodMk
      measurable_snd)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hGeq, A.ae_reconstruct] with ω hω hA
  change G ((A.reconstruct (LQGMetric.restrictTo V (h₀ ω)),
      LQGMetric.restrictTo V (h₀ ω)), _) = GMS4c.localConfiguration V (μ ω) (h₀ ω) (ηL ω)
  rw [hA]
  exact hω

private def prop48ZeroConeDiameterEvent
    {Ω : Type} (η₀ : Ω → C(ℝ, ℂ)) (ε q : ℝ) (z : ℂ) : Set Ω :=
  {ω | GMS4b.windowDiam ε (η₀ ω) z ≤ ε ^ q}

private def prop48ZeroConeDegreeEvent
    {Ω : Type} (η₀ : Ω → C(ℝ, ℂ)) (ε ζ : ℝ) (z : ℂ) : Set Ω :=
  {ω | ((prop48ZeroConeDegreeSum η₀ ε ω z : ℕ∞) : ℝ≥0∞) ≤
    ENNReal.ofReal (ε ^ (-ζ))}

private def prop48ZeroConeAverageEvent
    {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  {ω | max (abs (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z))
    (abs (LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z)) ≤
      2 * q * Real.log ε⁻¹}

/-- The local event (4.22) for the 0-cone realization. Degrees are kept in `ℕ∞`,
their actual `GMS4b` type, until finiteness has been proved from the event. -/
def prop48ZeroConeLocalEvent
    {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ)
    (η₀ : Ω → C(ℝ, ℂ)) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  prop48ZeroConeDiameterEvent η₀ ε q z ∩
    prop48ZeroConeDegreeEvent η₀ ε ζ z ∩
      prop48ZeroConeAverageEvent γ X₀ hIG₀ B₀ B₀' ε q ζ z

/-- The pointwise source event is the pullback of the Borel local event. -/
theorem prop48ZeroConeLocalEvent_eq_lemma49Event_preimage
    {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (η₀ : Ω → C(ℝ, ℂ))
    (ε q ζ : ℝ) (z : ℂ) :
    prop48ZeroConeLocalEvent γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z =
      (fun ω => ((η₀ ω,
        (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z,
          LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z)) :
            GMS4c.Lemma49Input)) ⁻¹' GMS4c.lemma49Event ε q ζ z := by
  ext ω
  simp only [prop48ZeroConeLocalEvent, Set.mem_inter_iff, Set.mem_preimage]
  change
    (GMS4b.windowDiam ε (η₀ ω) z ≤ ε ^ q ∧
      ((prop48ZeroConeDegreeSum η₀ ε ω z : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-ζ))) ∧
      max |prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z|
        |LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z| ≤
          2 * q * Real.log ε⁻¹ ↔ _
  simp only [GMS4c.lemma49Event, Set.mem_setOf_eq]
  tauto

/-- The 0-cone local event is measurable modulo null sets for each centre. -/
theorem nullMeasurableSet_prop48ZeroConeLocalEvent
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε q ζ : ℝ) (hε : 0 ≤ ε) (z : ℂ) :
    NullMeasurableSet (prop48ZeroConeLocalEvent γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z) P := by
  rw [prop48ZeroConeLocalEvent_eq_lemma49Event_preimage]
  have hIG : Measurable fun ω =>
      LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z :=
    (LQGMetric.measurable_circleAvg_left _ z).comp D.igField.1.1.measurable
  have hinput : AEMeasurable (fun ω => ((η₀ ω,
      (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z,
        LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z)) :
          GMS4c.Lemma49Input)) P :=
    D.measurable_curves.2.2.1.aemeasurable.prodMk
      ((aemeasurable_prop48ZeroConeCircleAverage D _ z).prodMk hIG.aemeasurable)
  exact hinput.nullMeasurableSet_preimage (GMS4c.measurableSet_lemma49Event hε z)

/-- The pointwise density is jointly measurable in the sample and centre when the
bundle's 0-cone curve is used. -/
theorem measurable_prop48ZeroConeUStar
    {Ω : Type} [MeasurableSpace Ω] {η₀ : Ω → C(ℝ, ℂ)}
    (hη : Measurable η₀) {ε : ℝ} (hε : 0 ≤ ε) :
    Measurable fun p : Ω × ℂ => prop48ZeroConeUStar η₀ ε p.1 p.2 := by
  exact GMS4b.measurable_uStar_comp hη hε

/-- the masked density evaluated on the actual 0-cone curve and averages. -/
def prop48ZeroConeMaskedUStar
    {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (η₀ : Ω → C(ℝ, ℂ))
    (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  GMS4c.lemma49MaskedUStar ε q ζ z
    (η₀ ω,
      (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z,
        LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z))

/-- The matching masked area ratio in (4.24). -/
def prop48ZeroConeMaskedAreaRatio
    {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (η₀ : Ω → C(ℝ, ℂ))
    (ε q ζ : ℝ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  GMS4c.lemma49MaskedAreaRatio ε q ζ z
    (η₀ ω,
      (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z,
        LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z))

/-- The event's degree cap gives (4.32)'s pointwise density comparison. -/
theorem prop48ZeroConeMaskedUStar_le_areaRatio
    {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (η₀ : Ω → C(ℝ, ℂ))
    (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z ω ≤
      ENNReal.ofReal (ε ^ (-ζ)) *
        prop48ZeroConeMaskedAreaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z ω := by
  exact GMS4c.lemma49_maskedUStar_le ε q ζ z _

theorem prop48ZeroConeMaskedUStar_eq_indicator
    {Ω : Type} [MeasurableSpace Ω] (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field)
    (B₀ B₀' : ℝ≥0 → Ω → ℝ) (η₀ : Ω → C(ℝ, ℂ))
    (ε q ζ : ℝ) (z : ℂ) :
    prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z =
      (prop48ZeroConeLocalEvent γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z).indicator
        (fun ω => prop48ZeroConeUStar η₀ ε ω z) := by
  funext ω
  rw [prop48ZeroConeLocalEvent_eq_lemma49Event_preimage]
  rfl

theorem aemeasurable_prop48ZeroConeMaskedUStar
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε q ζ : ℝ) (hε : 0 ≤ ε) (z : ℂ) :
    AEMeasurable (prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z) P := by
  have hIG : Measurable fun ω =>
      LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z :=
    (LQGMetric.measurable_circleAvg_left _ z).comp D.igField.1.1.measurable
  have hinput : AEMeasurable (fun ω => ((η₀ ω,
      (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z,
        LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z)) :
          GMS4c.Lemma49Input)) P :=
    D.measurable_curves.2.2.1.aemeasurable.prodMk
      ((aemeasurable_prop48ZeroConeCircleAverage D _ z).prodMk hIG.aemeasurable)
  exact (GMS4c.measurable_lemma49MaskedUStar hε z).comp_aemeasurable hinput

theorem aemeasurable_prop48ZeroConeMaskedAreaRatio
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε q ζ : ℝ) (hε : 0 ≤ ε) (z : ℂ) :
    AEMeasurable (prop48ZeroConeMaskedAreaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z) P := by
  have hIG : Measurable fun ω =>
      LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z :=
    (LQGMetric.measurable_circleAvg_left _ z).comp D.igField.1.1.measurable
  have hinput : AEMeasurable (fun ω => ((η₀ ω,
      (prop48ZeroConeCircleAverage γ X₀ B₀ B₀' (ε ^ (q - 4 * ζ)) ω z,
        LQGMetric.circleAvg (hIG₀ ω) (ε ^ (q - 4 * ζ)) z)) :
          GMS4c.Lemma49Input)) P :=
    D.measurable_curves.2.2.1.aemeasurable.prodMk
      ((aemeasurable_prop48ZeroConeCircleAverage D _ z).prodMk hIG.aemeasurable)
  exact (GMS4c.measurable_lemma49MaskedAreaRatio hε z).comp_aemeasurable hinput

/-- The Cauchy–Schwarz part of [18] (4.33): the event's degree cap and
uniform second moments of the masked area ratio bound the pair product. -/
theorem prop48_zeroCone_masked_pair_lintegral_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε q ζ : ℝ) (hε : 0 ≤ ε) (z w : ℂ) (K : ℝ≥0∞)
    (hz : ∫⁻ ω, prop48ZeroConeMaskedAreaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z ω ^
        (2 : ℝ) ∂P ≤ K)
    (hw : ∫⁻ ω, prop48ZeroConeMaskedAreaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ w ω ^
        (2 : ℝ) ∂P ≤ K) :
    (∫⁻ ω, prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z ω *
      prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ w ω ∂P) ≤
      ENNReal.ofReal (ε ^ (-ζ)) ^ 2 * (K ^ (1 / (2 : ℝ)) * K ^ (1 / (2 : ℝ))) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (ε ^ (-ζ))
  let A : ℂ → Ω → ℝ≥0∞ := fun x =>
    prop48ZeroConeMaskedAreaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ x
  let V : ℂ → Ω → ℝ≥0∞ := fun x =>
    prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ x
  have hAz : AEMeasurable (A z) P := aemeasurable_prop48ZeroConeMaskedAreaRatio D ε q ζ hε z
  have hAw : AEMeasurable (A w) P := aemeasurable_prop48ZeroConeMaskedAreaRatio D ε q ζ hε w
  have hpoint : ∀ ω, V z ω * V w ω ≤ c ^ 2 * (A z ω * A w ω) := by
    intro ω
    calc
      V z ω * V w ω ≤ (c * A z ω) * (c * A w ω) :=
        mul_le_mul' (prop48ZeroConeMaskedUStar_le_areaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z ω)
          (prop48ZeroConeMaskedUStar_le_areaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ w ω)
      _ = c ^ 2 * (A z ω * A w ω) := by ring
  have hholder : (∫⁻ ω, A z ω * A w ω ∂P) ≤
      (∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq P
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hAz hAw
  calc
    (∫⁻ ω, V z ω * V w ω ∂P) ≤
        ∫⁻ ω, c ^ 2 * (A z ω * A w ω) ∂P := lintegral_mono hpoint
    _ = c ^ 2 * ∫⁻ ω, A z ω * A w ω ∂P := by
      exact lintegral_const_mul'' (c ^ 2) (hAz.mul hAw)
    _ ≤ c ^ 2 *
        ((∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) :=
      mul_le_mul' le_rfl hholder
    _ ≤ c ^ 2 * (K ^ (1 / (2 : ℝ)) * K ^ (1 / (2 : ℝ))) := by
      gcongr

/-- The unit-scale `u_*` moment follows directly from the frozen cell moments. The
range `p < 4/γ²` is the inner-degree range of [20, Proposition 4.6]. -/
theorem prop48_zeroCone_unit_uStar_moment
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {p : ℝ} (hp : 1 ≤ p) (hpK : p < 4 / γ ^ 2) :
    ∫⁻ ω, GMS4b.locUStar 1 (η₀ ω) 0 ^ p ∂P < ⊤ := by
  have h0 : ∀ᵐ ω ∂P, η₀ ω 0 = 0 := by
    filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace
    rcases harea.1 with ⟨φ, hφ0, hηeq⟩
    rw [hηeq, hφ0, hspace.2.2.1]
  have hmom := GMS4b.unitCellMoments_of_cellMoments h0 D.cellMoments
  have hη := D.measurable_curves.2.2.1
  set K : ℝ := 4 / γ ^ 2
  have hp0 : 0 < p := by linarith
  set s : ℝ := (1 + K / p) / 2
  have hKp : 1 < K / p := by rw [lt_div_iff₀ hp0]; linarith
  have hs1 : 1 < s := by dsimp [s]; linarith
  have hps : p * s < K := by
    dsimp [s]
    rw [mul_div_assoc', mul_add, mul_one, mul_div_cancel₀ _ hp0.ne']
    linarith
  set r : ℝ := s.conjExponent
  have hsr : s.HolderConjugate r := Real.HolderConjugate.conjExponent hs1
  have hr1 : 1 < r := hsr.symm.lt
  have hps1 : 1 ≤ p * s := by nlinarith
  have hpr1 : 1 ≤ p * r := by nlinarith
  have hcoe : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := measurable_of_countable _
  set S : Ω → ℝ≥0∞ := fun ω =>
    ((GMS4b.locDegIn 1 (η₀ ω) 0 + GMS4b.locDegOut 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞)
  set A : Ω → ℝ≥0∞ := fun ω => GMS4b.locDA 1 (η₀ ω) 0
  have hSm : Measurable S :=
    hcoe.comp ((measurable_of_countable (fun x : ℕ∞ × ℕ∞ => x.1 + x.2)).comp
      (((GMS4b.measurable_locDegIn 1 0).comp hη).prodMk
        ((GMS4b.measurable_locDegOut zero_le_one 0).comp hη)))
  have hAm : Measurable A := (GMS4b.measurable_locDA 1 0).comp hη
  have hSfin : ∫⁻ ω, S ω ^ (p * s) ∂P < ⊤ := by
    have hle : ∀ ω, S ω ^ (p * s) ≤ (2 : ℝ≥0∞) ^ (p * s - 1) *
        (((GMS4b.locDegIn 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) +
         ((GMS4b.locDegOut 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s)) := by
      intro ω
      simp only [S, ENat.toENNReal_add]
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hps1
    have hm1 : Measurable fun ω =>
        ((GMS4b.locDegIn 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) :=
      (ENNReal.continuous_rpow_const.measurable).comp
        (hcoe.comp ((GMS4b.measurable_locDegIn 1 0).comp hη))
    have hm2 : Measurable fun ω =>
        ((GMS4b.locDegOut 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) :=
      (ENNReal.continuous_rpow_const.measurable).comp
        (hcoe.comp ((GMS4b.measurable_locDegOut zero_le_one 0).comp hη))
    refine (lintegral_mono hle).trans_lt ?_
    have hm12 : Measurable fun ω =>
        ((GMS4b.locDegIn 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) +
          ((GMS4b.locDegOut 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ (p * s) := hm1.add hm2
    rw [lintegral_const_mul _ hm12, lintegral_add_left hm1]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.add_lt_top.mpr ⟨hmom.2.1 _ hps1 hps, hmom.2.2 _ hps1⟩)
  have hAfin : ∫⁻ ω, A ω ^ (p * r) ∂P < ⊤ := hmom.1 _ hpr1
  have hsplit : ∀ ω, GMS4b.locUStar 1 (η₀ ω) 0 ^ p =
      S ω ^ p * A ω ^ p := by
    intro ω
    simp only [S, A, GMS4b.locUStar]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, mul_comm]
  simp_rw [hsplit]
  have hf : Measurable fun ω => S ω ^ p :=
    (ENNReal.continuous_rpow_const.measurable).comp hSm
  have hg : Measurable fun ω => A ω ^ p :=
    (ENNReal.continuous_rpow_const.measurable).comp hAm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hsr hf.aemeasurable hg.aemeasurable
  refine hH.trans_lt ?_
  simpa only [← ENNReal.rpow_mul] using
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hSfin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hAfin.ne)

/-- The one P23Z scaling input needed here: the zero-cone root cell's actual
area-ratio/inner-degree/outer-degree triple has its unit-scale law at every
positive quantum-time mesh. This is a law statement about the frozen `η₀`,
not a moment bound. -/
def Prop48ZeroConeLocalTripleScaleInput
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    P.map (fun ω => GMS4b.localTriple ε (η₀ ω)) =
      P.map (fun ω => GMS4b.localTriple 1 (η₀ ω))

/-- P23Z proves the required local-triple law for the actual zero-cone curve. -/
theorem prop48_zeroCone_localTriple_scaleInput
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) :
    Prop48ZeroConeLocalTripleScaleInput D := by
  intro ε hε
  exact CellScaling.ZeroConeScaling.cellLaw_holds D hγ hε

/-- P23Z's local-triple law transports the already proved unit-scale moment
uniformly to all positive meshes. -/
theorem prop48_zeroCone_uniform_uStar_moment_of_scaleInput
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hscale : Prop48ZeroConeLocalTripleScaleInput D)
    {p : ℝ} (hp : 1 ≤ p) (hpK : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, GMS4b.locUStar ε (η₀ ω) 0 ^ p ∂P ≤ C := by
  let C : ℝ≥0∞ := ∫⁻ ω, GMS4b.locUStar 1 (η₀ ω) 0 ^ p ∂P
  refine ⟨C, prop48_zeroCone_unit_uStar_moment D hp hpK, ?_⟩
  intro ε hε
  let F : ℝ≥0∞ × ℕ∞ × ℕ∞ → ℝ≥0∞ := fun x =>
    (x.1 * (((x.2.1 + x.2.2 : ℕ∞) : ℝ≥0∞))) ^ p
  have hcoe : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := measurable_of_countable _
  have hF : Measurable F := by
    exact (ENNReal.continuous_rpow_const.measurable).comp
      (measurable_fst.mul
        (hcoe.comp ((measurable_of_countable (fun x : ℕ∞ × ℕ∞ => x.1 + x.2)).comp
          measurable_snd)))
  have hmε : Measurable fun ω => GMS4b.localTriple ε (η₀ ω) :=
    (GMS4b.measurable_localTriple hε.le).comp D.measurable_curves.2.2.1
  have hm1 : Measurable fun ω => GMS4b.localTriple 1 (η₀ ω) :=
    (GMS4b.measurable_localTriple zero_le_one).comp D.measurable_curves.2.2.1
  have heq : (∫⁻ ω, F (GMS4b.localTriple ε (η₀ ω)) ∂P) =
      ∫⁻ ω, F (GMS4b.localTriple 1 (η₀ ω)) ∂P := by
    have h1 := lintegral_map (μ := P) hF hmε
    have h2 := lintegral_map (μ := P) hF hm1
    rw [← h1, ← h2, hscale ε hε]
  simpa only [C, F, GMS4b.localTriple, GMS4b.locUStar] using heq.le

/-- The uniform zero-cone root moment with all scale inputs discharged. -/
theorem prop48_zeroCone_uniform_uStar_moment
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2)
    {p : ℝ} (hp : 1 ≤ p) (hpK : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, GMS4b.locUStar ε (η₀ ω) 0 ^ p ∂P ≤ C := by
  exact prop48_zeroCone_uniform_uStar_moment_of_scaleInput D
    (prop48_zeroCone_localTriple_scaleInput D hγ) hp hpK

end MatedCRTHarmonic.GMS4

