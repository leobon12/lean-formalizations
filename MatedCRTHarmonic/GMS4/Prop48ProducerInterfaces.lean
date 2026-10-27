import MatedCRTHarmonic.GMS4.Prop48Statement
import MatedCRTHarmonic.GMSAppA.LemmaA1A2
import MatedCRTHarmonic.GMS4.Prop48JointConditioning

/-!
# Concrete producer interfaces below [18] Proposition 4.8

These interfaces expose the source steps that are not supplied by the abstract contribution
bounds in `Prop48WholePlaneFixedTestInputs`. They do not assume Proposition 4.8 or its probability
conclusion. Source references below cite [18].

The SLE and local graph observables enter through the stated interfaces. The
whole-plane GFF conditioning and long-range estimate are the analytic construction outputs (Appendix A.2/A.3),
combined respectively with the GMS4b cell moments and L27 locality. The near and far pair expectations are unconditional on the global event `E^ε`, as required by the corrected second-moment expansion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.GM LQGMetric.Blueprint
open Classical
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

/-- The two local circle averages used in (4.22), (4.27), and (4.28). -/
def prop48CircleAverageObservation {Ω : Type*} [MeasurableSpace Ω]
    (h hIG : Ω → LQGMetric.DistC) (r : ℝ) (z : ℂ) (ω : Ω) : ℝ × ℝ :=
  (LQGMetric.circleAvg (h ω) r z, LQGMetric.circleAvg (hIG ω) r z)

/-- The local field observation in (4.22): both distributions restricted to
`B_{4 ε^q}(z)` and the two circle averages on `∂B_{ε^(q-4ζ)}(z)`. -/
def prop48LocalFieldObservation {Ω : Type*} [MeasurableSpace Ω]
    (h hIG : Ω → LQGMetric.DistC) (localRadius averageRadius : ℝ) (z : ℂ) (ω : Ω) :
    (LQGMetric.DistOn (LQGMetric.Blueprint.ballO z localRadius) ×
      LQGMetric.DistOn (LQGMetric.Blueprint.ballO z localRadius)) × (ℝ × ℝ) :=
  ((LQGMetric.restrictTo (LQGMetric.Blueprint.ballO z localRadius) (h ω),
      LQGMetric.restrictTo (LQGMetric.Blueprint.ballO z localRadius) (hIG ω)),
    prop48CircleAverageObservation h hIG averageRadius z ω)

/-- The centered pointwise local observable `U_*^ε(z)` of (4.28). The conditional mean is given
The same name as `Prop48LocalizedObservable.conditionalMean`, but this function keeps the
pointwise-in-`z` source object visible for the near/far decomposition. -/
def prop48PointwiseCentered {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (L : Prop48LocalizedObservable P) (z : ℂ) (ω : Ω) : ℝ :=
  (L.localEvent z).indicator (fun ω' => L.uStar ω' z) ω - L.conditionalMean ω z

/-- **local-observable and regularity producer.**

The factorization is the exact local-determination claim (4.22): the truncated density
`1_{F^ε(z)}u_*^ε(z)` is a measurable function of both restrictions
`(h,h^IG)|_{B_{4ε^q}(z)}` and the two circle averages at radius `ε^(q-4ζ)`.
`conditionalMean_eq` makes the conditional mean in (4.28) an actual
conditional expectation given those averages, rather than an unrelated random variable. The
uniform upper bound is (4.27). The global-good-event implication is already represented by
`Prop48LocalizedObservable.localEvent_of_good`; its Fubini/subtraction regularity fields and the
abstract second-moment split are already represented by `Prop48LocalizedObservable` and
`L27MomentIntegralRegularityInput`, so they are not duplicated here.

Source: [18] (4.22)–(4.29). The local interface supplies the curve,
locality, and the observable; the Gaussian estimate supplies the conditional GFF moment input. -/
structure Prop48LocalObservableProducer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hIG : Ω → LQGMetric.DistC) (L : Prop48LocalizedObservable P)
    (ε q ζ γ : ℝ) where
  epsilon_range : 0 < ε ∧ ε < 1
  epsilonStar : ℝ
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_lt_one : epsilonStar < 1
  epsilon_le_star : ε ≤ epsilonStar
  gamma_range : 0 < γ ∧ γ < 2
  q_range : 0 < q ∧ q < min (2 / (2 + γ) ^ 2) γ
  zeta_range : 0 < ζ ∧ ζ < q / 100
  ig_is_normalized_wholePlaneGFF : LQGMetric.IsNormalizedWPGFF hIG P
  field_is_normalized_wholePlaneGFF : LQGMetric.IsNormalizedWPGFF h P
  field_ig_independent : IndepFun h hIG P
  localRadius : ℝ
  localRadius_eq : localRadius = 4 * ε ^ q
  averageRadius : ℝ
  averageRadius_eq : averageRadius = ε ^ (q - 4 * ζ)
  localFactor : ∀ z : ℂ,
    (LQGMetric.DistOn (LQGMetric.Blueprint.ballO z localRadius) ×
      LQGMetric.DistOn (LQGMetric.Blueprint.ballO z localRadius)) × (ℝ × ℝ) → ℝ
  localFactor_measurable : ∀ z, Measurable (localFactor z)
  localFactor_eq_truncated_density : ∀ z ∈ L.domain,
    (fun ω => localFactor z (prop48LocalFieldObservation h hIG localRadius averageRadius z ω))
      =ᵐ[P] fun ω => (L.localEvent z).indicator (fun ω' => L.uStar ω' z) ω
  conditionalMean_eq : ∀ z ∈ L.domain,
    (fun ω => L.conditionalMean ω z) =ᵐ[P]
      P[(fun ω => (L.localEvent z).indicator (fun ω' => L.uStar ω' z) ω) |
        MeasurableSpace.comap
          (prop48CircleAverageObservation h hIG averageRadius z) inferInstance]
  conditionalMean_nonnegative : ∀ z ∈ L.domain, ∀ᵐ ω ∂P,
    0 ≤ L.conditionalMean ω z
  conditionalMean_le : ∀ z ∈ L.domain, ∀ᵐ ω ∂P,
    L.conditionalMean ω z ≤ L.meanConstant

/-- The random variable in Lemma 4.9's conditional moment estimates. -/
def prop48MaskedDensity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (L : Prop48LocalizedObservable P) (z : ℂ) (ω : Ω) : ℝ :=
  (L.localEvent z).indicator (fun ω' => L.uStar ω' z) ω

/-- The source exterior σ-algebra generated by both fields outside the open disk. -/
def prop48ExteriorSigma {Ω : Type} [MeasurableSpace Ω]
    (h hIG : Ω → DistC) (r : ℝ) (z : ℂ) : MeasurableSpace Ω :=
  fieldSigmaClosed h (Metric.ball z r)ᶜ ⊔ fieldSigmaClosed hIG (Metric.ball z r)ᶜ

/-- The exterior sigma algebra in the two-field Appendix A.3 estimate is the source
exterior sigma algebra at the unit disk. Translation and scaling are still required
for the disks used in Proposition 4.8. -/
theorem prop48_extSigmaN_eq_exteriorSigma
    {Ω : Type} [MeasurableSpace Ω] (h hIG : Ω → DistC) :
    GMSAppA.extSigmaN (prop48FieldFamily h hIG) =
      prop48ExteriorSigma h hIG 1 0 := by
  change (⨆ i : Fin 2,
      fieldSigmaClosed (prop48FieldFamily h hIG i) (Metric.ball (0 : ℂ) 1)ᶜ) =
    fieldSigmaClosed h (Metric.ball (0 : ℂ) 1)ᶜ ⊔
      fieldSigmaClosed hIG (Metric.ball (0 : ℂ) 1)ᶜ
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · simpa [prop48FieldFamily] using
        (le_sup_left : fieldSigmaClosed h (Metric.ball (0 : ℂ) 1)ᶜ ≤
          fieldSigmaClosed h (Metric.ball (0 : ℂ) 1)ᶜ ⊔
          fieldSigmaClosed hIG (Metric.ball (0 : ℂ) 1)ᶜ)
    · simpa [prop48FieldFamily] using
        (le_sup_right : fieldSigmaClosed hIG (Metric.ball (0 : ℂ) 1)ᶜ ≤
          fieldSigmaClosed h (Metric.ball (0 : ℂ) 1)ᶜ ⊔
          fieldSigmaClosed hIG (Metric.ball (0 : ℂ) 1)ᶜ)
  · refine sup_le ?_ ?_
    · exact le_iSup_of_le 0 (by simp [prop48FieldFamily])
    · exact le_iSup_of_le 1 (by simp [prop48FieldFamily])

/-- The affine inverse image of `B_r(z)` is the unit disk. -/
private theorem prop48_preOpens_ball_eq
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((DFGPS.preOpens r z (ballO z r) : TopologicalSpace.Opens ℂ) : Set ℂ) =
      Metric.ball (0 : ℂ) 1 := by
  ext y
  rw [SetLike.mem_coe, DFGPS.mem_preOpens hr.ne']
  change dist (r • y + z) z < r ↔ dist y 0 < 1
  rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, dist_zero_right]
  exact (mul_lt_iff_lt_one_right hr)

/-- Appendix A.3's exterior sigma algebra after affine transport is the joint exterior
sigma algebra outside `B_r(z)` in the original coordinates. -/
theorem prop48_extSigmaN_affine_eq_exteriorSigma
    {Ω : Type} [MeasurableSpace Ω] (h hIG : Ω → DistC)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    GMSAppA.extSigmaN (prop48AffineFieldFamily h hIG r z) =
      prop48ExteriorSigma h hIG r z := by
  have hpre := prop48_preOpens_ball_eq hr z
  have hh : fieldSigmaClosed (fun ω => affineComp r z (h ω))
      (Metric.ball (0 : ℂ) 1)ᶜ =
      fieldSigmaClosed h (Metric.ball z r)ᶜ := by
    rw [← hpre]
    exact le_antisymm
      (DFGPS.fieldSigmaClosed_affineComp_le hr (ballO z r) h)
      (DFGPS.fieldSigmaClosed_le_affineComp hr (ballO z r) h)
  have hhIG : fieldSigmaClosed (fun ω => affineComp r z (hIG ω))
      (Metric.ball (0 : ℂ) 1)ᶜ =
      fieldSigmaClosed hIG (Metric.ball z r)ᶜ := by
    rw [← hpre]
    exact le_antisymm
      (DFGPS.fieldSigmaClosed_affineComp_le hr (ballO z r) hIG)
      (DFGPS.fieldSigmaClosed_le_affineComp hr (ballO z r) hIG)
  have hfam : prop48AffineFieldFamily h hIG r z =
      prop48FieldFamily (fun ω => affineComp r z (h ω))
        (fun ω => affineComp r z (hIG ω)) := by
    funext i ω
    fin_cases i <;> simp [prop48AffineFieldFamily, prop48FieldFamily]
  calc
    GMSAppA.extSigmaN (prop48AffineFieldFamily h hIG r z) =
        prop48ExteriorSigma (fun ω => affineComp r z (h ω))
          (fun ω => affineComp r z (hIG ω)) 1 0 := by
            rw [hfam]
            exact prop48_extSigmaN_eq_exteriorSigma
              (fun ω => affineComp r z (h ω)) (fun ω => affineComp r z (hIG ω))
    _ = prop48ExteriorSigma h hIG r z := by
      simp only [prop48ExteriorSigma]
      rw [hh, hhIG]

/-- The two unit-circle observations after affine transport agree almost surely with the
source circle averages at radius `r` and centre `z`. Circle averages are chosen versions, so
this is an almost-sure identity rather than a pointwise equality of sigma algebras. -/
theorem prop48_affine_circleAverages_ae
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h hIG : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun ω : Ω => (fun i : Fin 2 =>
      circleAvg (prop48AffineFieldFamily h hIG r z i ω) 1 0)) =ᵐ[P]
      fun ω => (fun i : Fin 2 =>
        if i = 0 then circleAvg (h ω) r z else circleAvg (hIG ω) r z) := by
  filter_upwards [CircleAvg.ae_circleAvg_affineComp hh.1 hr z,
    CircleAvg.ae_circleAvg_affineComp hhIG.1 hr z] with ω hω hωIG
  funext i
  fin_cases i
  · exact hω
  · exact hωIG

/-- The affine preimage of `B_{rδ}(z)` is `B_δ(0)`. -/
private theorem prop48_ball_scale_iff
    {r : ℝ} (hr : 0 < r) (δ : ℝ) (z y : ℂ) :
    y ∈ ballO 0 δ ↔ r • y + z ∈ ballO z (r * δ) := by
  change dist y 0 < δ ↔ dist (r • y + z) z < r * δ
  rw [dist_zero_right, dist_eq_norm, add_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro h
    nlinarith [mul_pos hr (sub_pos.mpr h)]
  · intro h
    by_contra hn
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr (le_of_not_gt hn))]

/-- A restriction in the original coordinates is a measurable function of the restriction
of the affine field to the rescaled disk. -/
def prop48PullbackRestriction {r : ℝ} (hr : 0 < r) (δ : ℝ) (z : ℂ) :
    DistOn (ballO 0 δ) → DistOn (ballO z (r * δ)) :=
  fun T => (r ^ 2) • T.comp
    (GM.testScalePush hr.ne' (prop48_ball_scale_iff hr δ z))

theorem measurable_prop48PullbackRestriction {r : ℝ} (hr : 0 < r)
    (δ : ℝ) (z : ℂ) : Measurable (prop48PullbackRestriction hr δ z) := by
  refine measurable_distOn_iff.2 fun ψ => ?_
  change Measurable fun T : DistOn (ballO 0 δ) =>
    r ^ 2 * T (GM.testScalePush hr.ne' (prop48_ball_scale_iff hr δ z) ψ)
  exact (measurable_distOn_apply _).const_mul _

theorem prop48_restrict_affine_eq_pullback {r : ℝ} (hr : 0 < r)
    (δ : ℝ) (z : ℂ) (g : DistC) :
    restrictTo (ballO z (r * δ)) g =
      prop48PullbackRestriction hr δ z
        (restrictTo (ballO 0 δ) (affineComp r z g)) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  exact GM.restrictTo_apply_eq_scale hr (prop48_ball_scale_iff hr δ z) g ψ

/-- Re-express a source local functional as a functional of the two affine fields observed
in `B_δ(0)` and their unit-circle averages. -/
def prop48AffineLocalFactor {r : ℝ} (hr : 0 < r) (δ : ℝ) (z : ℂ)
    (f : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) ×
      (ℝ × ℝ)) → ℝ) :
    ((Fin 2 → DistOn (ballO 0 δ)) × (Fin 2 → ℝ)) → ℝ :=
  fun O => f ((prop48PullbackRestriction hr δ z (O.1 0),
      prop48PullbackRestriction hr δ z (O.1 1)), (O.2 0, O.2 1))

theorem measurable_prop48AffineLocalFactor {r : ℝ} (hr : 0 < r)
    (δ : ℝ) (z : ℂ)
    {f : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) ×
      (ℝ × ℝ)) → ℝ} (hf : Measurable f) :
    Measurable (prop48AffineLocalFactor hr δ z f) := by
  have hfield (i : Fin 2) : Measurable fun O :
      (Fin 2 → DistOn (ballO 0 δ)) × (Fin 2 → ℝ) =>
        prop48PullbackRestriction hr δ z (O.1 i) :=
    (measurable_prop48PullbackRestriction hr δ z).comp
      ((measurable_pi_apply i).comp measurable_fst)
  have havg (i : Fin 2) : Measurable fun O :
      (Fin 2 → DistOn (ballO 0 δ)) × (Fin 2 → ℝ) => O.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  exact hf.comp ((hfield 0).prodMk (hfield 1) |>.prodMk
    ((havg 0).prodMk (havg 1)))

/-- The source local observation equals the transported Appendix A.3 observation almost
surely. The restriction part is pointwise; only circle-average versions require `=ᵐ`. -/
theorem prop48_affine_localFactor_ae
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h hIG : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    {r : ℝ} (hr : 0 < r) (δ : ℝ) (z : ℂ)
    (f : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) ×
      (ℝ × ℝ)) → ℝ) :
    (fun ω => f (prop48LocalFieldObservation h hIG (r * δ) r z ω)) =ᵐ[P]
      fun ω => prop48AffineLocalFactor hr δ z f
        (GMSAppA.obsN δ (prop48AffineFieldFamily h hIG r z) ω) := by
  filter_upwards [prop48_affine_circleAverages_ae hh hhIG hr z] with ω hω
  have h₀ := congrFun hω (0 : Fin 2)
  have h₁ := congrFun hω (1 : Fin 2)
  simp only [prop48AffineFieldFamily, prop48FieldFamily, ↓reduceIte] at h₀ h₁
  simp only [prop48LocalFieldObservation, prop48CircleAverageObservation,
    prop48AffineLocalFactor, GMSAppA.obsN, prop48AffineFieldFamily,
    prop48FieldFamily, ↓reduceIte]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at h₁ ⊢
  rw [← prop48_restrict_affine_eq_pullback hr δ z (h ω),
    ← prop48_restrict_affine_eq_pullback hr δ z (hIG ω), h₀, h₁]

/-- The translated/scaled two-field A.3 estimate for a source local functional.
The local-observation factorization is supplied in the original coordinates; the preceding
restriction and circle-average transport lemmas discharge its A.3 factorization premise. -/
theorem prop48_twoField_lemmaA3_local
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hIG : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    (hind : IndepFun h hIG P)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1)
    {p p₀ s δ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδ : 0 < δ) (hδa : δ ≤ GMSAppA.a3aN p p₀ 2)
    {X : Ω → ℝ}
    {f : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) ×
      (ℝ × ℝ)) → ℝ}
    (hf : Measurable f)
    (hX : X =ᵐ[P] fun ω => f (prop48LocalFieldObservation h hIG (r * δ) r z ω))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal
      |P[X | prop48ExteriorSigma h hIG r z] ω -
        P[X | GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z)] ω| ^ p ∂P ≤
      ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P +
          ENNReal.ofReal
              (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P) ^ (p / p₀)) := by
  have hfactor : X =ᵐ[P] fun ω =>
      prop48AffineLocalFactor hr δ z f
        (GMSAppA.obsN δ (prop48AffineFieldFamily h hIG r z) ω) :=
    hX.trans (prop48_affine_localFactor_ae hh hhIG hr δ z f)
  have H := prop48_twoField_lemmaA3_affine hh hhIG hind hr z hsmall
    hp hpp₀ hs hδ hδa (measurable_prop48AffineLocalFactor hr δ z hf)
    hfactor hXp₀
  simpa only [prop48_extSigmaN_affine_eq_exteriorSigma h hIG hr z] using H

/-- The source's scales in (4.22) become A.3's ball radius `δ = 4 ε^(4ζ)` after
rescaling by `r = ε^(q−4ζ)`. -/
theorem prop48_localRadius_eq_affine_radius
    {ε : ℝ} (hε : 0 < ε) (q ζ : ℝ) :
    ε ^ (q - 4 * ζ) * (4 * ε ^ (4 * ζ)) = 4 * ε ^ q := by
  calc
    ε ^ (q - 4 * ζ) * (4 * ε ^ (4 * ζ)) =
        4 * (ε ^ (q - 4 * ζ) * ε ^ (4 * ζ)) := by ring
    _ = 4 * ε ^ q := by
      rw [← Real.rpow_add hε]
      congr 1
      ring

/-- **Gaussian and local pointwise moment producer for the near/far estimates.**

The two conditional moment bounds are exactly the fixed-`ε` inputs of Lemma 4.9, (4.24) and
(4.25), needed in (4.32)--(4.36): moments of order `p ≥ 1` of the area ratio, and a moment of the
truncated localized density for `1 < p < 4/γ²`, uniformly in the two local circle averages and
in `z`. The constants existentially quantified below can depend on this record's fixed `ε`; this
record therefore does **not** supply the small-`ε` uniformity used by Proposition 4.8. That missing
output is separately named by `Prop48UniformConditionalMomentInput` below. This is a pointwise
moment input, not a bound on the integral in Proposition 4.8. The local event and its degree cap
are the source conditions from (4.22); the density factorization is (4.19).

Source: [18, Proposition 4.8]. Producer: **L27** for (4.19), (4.22), and the degree
condition; **the analytic construction Lemma A.2** for conditioning the local fields; **GMS4b Theorem 4.4**, whose cell
moments come from [20, Propositions 4.4 and 4.6], for the moments after rescaling. The distinct
[16, Lemma A.3] upper-mass estimate supports the lower diameter bound in (4.18), not (4.24) or
(4.25). -/
structure Prop48ConditionalMomentProducer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hIG : Ω → LQGMetric.DistC) (L : Prop48LocalizedObservable P)
    (ε q ζ γ : ℝ) where
  epsilonStar : ℝ
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_lt_one : epsilonStar < 1
  epsilon_pos : 0 < ε
  epsilon_le_star : ε ≤ epsilonStar
  gamma_range : 0 < γ ∧ γ < 2
  q_range : 0 < q ∧ q < min (2 / (2 + γ) ^ 2) γ
  zeta_range : 0 < ζ ∧ ζ < q / 100
  areaRatio : Ω → ℂ → ℝ
  degreeSum : Ω → ℂ → ℝ
  areaRatio_nonnegative : ∀ ω z, 0 ≤ areaRatio ω z
  density_formula : ∀ ω z, L.uStar ω z = areaRatio ω z * degreeSum ω z
  degreeSum_nonnegative : ∀ ω z, 0 ≤ degreeSum ω z
  local_degree_cap : ∀ z ∈ L.domain, ∀ ω ∈ L.localEvent z,
    degreeSum ω z ≤ ε ^ (-ζ)
  areaRatio_conditional_moment : ∀ p : ℝ, 1 ≤ p → ∃ K : ℝ, 0 ≤ K ∧
    ∀ z ∈ L.domain, ∀ᵐ ω ∂P,
      P[(fun ω => Real.rpow
        (max 0 ((L.localEvent z).indicator (fun ω' => areaRatio ω' z) ω)) p) |
          MeasurableSpace.comap
            (prop48CircleAverageObservation h hIG (ε ^ (q - 4 * ζ)) z) inferInstance] ω ≤ K
  maskedDensity_conditional_moment : ∀ p : ℝ,
    1 < p → p < 4 / γ ^ 2 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ z ∈ L.domain, ∀ᵐ ω ∂P,
      P[(fun ω => Real.rpow (max 0 (prop48MaskedDensity L z ω)) p) |
          MeasurableSpace.comap
            (prop48CircleAverageObservation h hIG (ε ^ (q - 4 * ζ)) z) inferInstance] ω ≤ K

/-- **Missing uniform-in-`ε` conditional-moment output.**

`Prop48ConditionalMomentProducer` is parametrized by one fixed `ε`, so its existential moment
constants do not imply the uniformity in sufficiently small `ε` used in (4.24), (4.25), and
Proposition 4.8. This interface records exactly that extra output for a family of localized
observables and area ratios: for each allowed moment exponent there is one constant which works
for every `0 < ε ≤ epsilonStar`, every point in the corresponding domain, and almost every
sample. The area-ratio exponent range is `p ≥ 1`, as in (4.24), while the truncated-density range
is `1 < p < 4/γ²`, as in (4.25). It neither assumes the near/far integral bounds nor a
Proposition 4.8 target event.

Producer classification: **the analytic construction Lemma A.2 + GMS4b Theorem 4.4**, with the latter produced from
[20, Propositions 4.4 and 4.6], together with L27's identification of the localized observable.
The [16, Lemma A.3] upper-mass estimate belongs to the separate (4.18) producer. Source: [18]
, especially (4.24)--(4.25). -/
structure Prop48UniformConditionalMomentInput {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hIG : Ω → LQGMetric.DistC) (L : ℝ → Prop48LocalizedObservable P)
    (epsilonStar q ζ γ : ℝ) where
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_lt_one : epsilonStar < 1
  gamma_range : 0 < γ ∧ γ < 2
  q_range : 0 < q ∧ q < min (2 / (2 + γ) ^ 2) γ
  zeta_range : 0 < ζ ∧ ζ < q / 100
  areaRatio : ℝ → Ω → ℂ → ℝ
  areaRatio_nonnegative : ∀ ε ω z, 0 ≤ areaRatio ε ω z
  areaRatio_conditional_moment_uniform : ∀ p : ℝ, 1 ≤ p → ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ epsilonStar → ∀ z ∈ (L ε).domain, ∀ᵐ ω ∂P,
      P[(fun ω => Real.rpow (max 0
        (((L ε).localEvent z).indicator (fun ω' => areaRatio ε ω' z) ω)) p) |
          MeasurableSpace.comap
            (prop48CircleAverageObservation h hIG (ε ^ (q - 4 * ζ)) z) inferInstance] ω ≤ K
  maskedDensity_conditional_moment_uniform : ∀ p : ℝ,
    1 < p → p < 4 / γ ^ 2 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ epsilonStar → ∀ z ∈ (L ε).domain, ∀ᵐ ω ∂P,
      P[(fun ω => Real.rpow (max 0 (prop48MaskedDensity (L ε) z ω)) p) |
          MeasurableSpace.comap
            (prop48CircleAverageObservation h hIG (ε ^ (q - 4 * ζ)) z) inferInstance] ω ≤ K

/-- **L27 near-pair control input.** The pointwise estimate is the corrected conclusion of the
close-pair calculation (4.32)--(4.33): the unconditional product of the two centered local
observables has expectation `O(ε^(-2ζ))` whenever `|z-w| ≤ 2ε^(q-4ζ)`. Integrating over this
near region gives (4.34); the already named `L27LocalizedConditionalMomentInput` records the
resulting near contribution in the second-moment split. No Proposition 4.8 event estimate is
assumed, and no target-event indicator occurs inside this expectation. Source: [18, Proposition 4.8], using the unconditional form of (4.36). Producer: **local, Gaussian, and cell-moment estimates**, from the local-event
degree cap and Lemma 4.9's conditional moment bounds. -/
structure Prop48NearPairControlProducer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Prop48LocalizedObservable P) (ε q ζ γ Cnear : ℝ) where
  epsilon_pos : 0 < ε
  epsilonStar : ℝ
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_lt_one : epsilonStar < 1
  epsilon_le_star : ε ≤ epsilonStar
  gamma_range : 0 < γ ∧ γ < 2
  q_range : 0 < q ∧ q < min (2 / (2 + γ) ^ 2) γ
  zeta_pos : 0 < ζ
  zeta_lt_q100 : ζ < q / 100
  Cnear_nonnegative : 0 ≤ Cnear
  near_pair_bound : ∀ z ∈ L.domain, ∀ w ∈ L.domain,
    dist z w ≤ 2 * ε ^ (q - 4 * ζ) →
      ∫ ω, prop48PointwiseCentered L z ω * prop48PointwiseCentered L w ω ∂P ≤
        Cnear * ε ^ (-2 * ζ)

/-- **Gaussian and local far-pair decoupling producer.**

`prop48ExteriorSigma` is exactly the join of the two field sigma-algebras outside
`B_{ε^(q-4ζ)}(z)`. `farVersion` is an exterior-measurable version of the centered local observable
at `w` when `|z-w| > 2ε^(q-4ζ)`; `farVersion_ae_eq` records the required almost-everywhere
identification without falsely asserting that the chosen arbitrary representative is measurable.
`conditionalLp_bound` is (4.35) after applying the already proved
Lemma A.3 to (4.28), and absorbing its exponentially small remainder using the Lemma 4.9 moments.
It is deliberately about the conditional expectation of the centered local variable alone; it has
no `1_{E^ε}` factor, using the unconditional form of (4.36). Together with the moment
bound on the other point, Hölder gives (4.36), whose integral is (4.37). Source: [18, Proposition 4.8]. Producer: **the analytic construction** for Lemma A.3; **local interfaces** for local determination and the
field/curve locality interface. -/
structure Prop48FarPairDecouplingProducer {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hIG : Ω → LQGMetric.DistC) (L : Prop48LocalizedObservable P)
    (ε q ζ γ p p0 Cfar : ℝ) where
  localObservable : Prop48LocalObservableProducer P h hIG L ε q ζ γ
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  epsilonStar : ℝ
  epsilonStar_pos : 0 < epsilonStar
  epsilonStar_lt_one : epsilonStar < 1
  epsilonStar_le_local : epsilonStar ≤ localObservable.epsilonStar
  epsilon_le_star : ε ≤ epsilonStar
  /-- The locality implication in (4.36) requires the local disk `B_{4ε^q}(w)` to fit
  inside `B_{ε^(q-4ζ)}(w)`. This is the explicit small-scale guard from
  `[18]`, before using the far-pair distance condition. -/
  four_scaled_radius_le : 4 * ε ^ (4 * ζ) ≤ 1
  gamma_range : 0 < γ ∧ γ < 2
  zeta_pos : 0 < ζ
  q_range : 0 < q ∧ q < min (2 / (2 + γ) ^ 2) γ
  zeta_lt_q100 : ζ < q / 100
  p_range : 1 < p ∧ p < p0 ∧ p0 < 4 / γ ^ 2
  Cfar_nonnegative : 0 ≤ Cfar
  farVersion : ℂ → ℂ → Ω → ℝ
  farVersion_measurable : ∀ z ∈ L.domain, ∀ w ∈ L.domain,
    2 * ε ^ (q - 4 * ζ) < dist z w →
      Measurable[prop48ExteriorSigma h hIG (ε ^ (q - 4 * ζ)) z]
        (farVersion z w)
  farVersion_ae_eq : ∀ z ∈ L.domain, ∀ w ∈ L.domain,
    2 * ε ^ (q - 4 * ζ) < dist z w →
      farVersion z w =ᵐ[P] prop48PointwiseCentered L w
  conditionalLp_bound : ∀ z ∈ L.domain,
    ∫⁻ ω, ENNReal.ofReal
      |P[prop48PointwiseCentered L z |
        prop48ExteriorSigma h hIG (ε ^ (q - 4 * ζ)) z] ω| ^ p ∂P ≤
      ENNReal.ofReal (Cfar * ε ^ (2 * p * ζ))

/-- The small-scale guard yields the radius comparison needed for far-pair exterior locality. -/
theorem Prop48FarPairDecouplingProducer.localRadius_le_averageRadius
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hIG : Ω → LQGMetric.DistC} {L : Prop48LocalizedObservable P}
    {ε q ζ γ p p0 Cfar : ℝ}
    (F : Prop48FarPairDecouplingProducer P h hIG L ε q ζ γ p p0 Cfar) :
    4 * ε ^ q ≤ ε ^ (q - 4 * ζ) := by
  have hpow : ε ^ q = ε ^ (q - 4 * ζ) * ε ^ (4 * ζ) := by
    rw [← Real.rpow_add F.epsilon_pos]
    congr 1
    ring
  rw [hpow]
  calc
    4 * (ε ^ (q - 4 * ζ) * ε ^ (4 * ζ)) =
        ε ^ (q - 4 * ζ) * (4 * ε ^ (4 * ζ)) := by ring
    _ ≤ ε ^ (q - 4 * ζ) * 1 :=
      mul_le_mul_of_nonneg_left F.four_scaled_radius_le
        (Real.rpow_nonneg F.epsilon_pos.le _)
    _ = ε ^ (q - 4 * ζ) := mul_one _

end MatedCRTHarmonic.GMS4
