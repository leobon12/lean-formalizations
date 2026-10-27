import MatedCRTHarmonic.MoTInput.CellModel
import MatedCRTHarmonic.MoTInput.ConeRealization
import MatedCRTHarmonic.MesoModel.FrozenIdentities
import MatedCRTHarmonic.GMS4c.MassClock
import MatedCRTHarmonic.ConeLemmaA10.LogShift
import MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable
import MatedCRTHarmonic.GMS4.Prop410Rooting
import MatedCRTHarmonic.MoTPort.Foundations.GFFWP
import LQGMetric.Field.ExistGFF
import MatedCRTHarmonic.LQGCone.AreaBridge

/-!
# The two canonical quantum surfaces of the frozen mating coupling

The cone is the existing `MoTInput.cellModelOfCoupling`. The reference surface
uses the zero-quantum cone supplied by `areaParam₀`, retaining its underlying
normalized whole-plane GFF, IG field, phase, and Lebesgue-time curve. All
area and clock identities below are almost-sure, as in the frozen bundle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The cone's field, GMC area, area-time SLE and boundary Brownian motion. -/
structure ConeSample where
  field : MatedCRT.Field
  area : Measure ℂ
  curve : C(ℝ, ℂ)
  boundary : Path2

/-- The zero-cone reference with its whole-plane GFF and IG/SLE inputs. -/
structure ReferenceSample where
  wholePlaneGFF : MatedCRT.Field
  wholePlaneArea : Measure ℂ
  igField : MatedCRT.Field
  phase : ℝ
  lebesgueCurve : C(ℝ, ℂ)
  zeroConeField : MatedCRT.Field
  area : Measure ℂ
  areaCurve : C(ℝ, ℂ)

/-- Fix the additive constant of a whole-plane GFF by its unit-circle average. -/
def normalizeWholePlane (h : MatedCRT.Field) : MatedCRT.Field :=
  LQGMetric.addConst h (-LQGMetric.circleAvg h 1 0)

/-- The `X₀` coordinate yields the required unit-circle-normalized
whole-plane GFF, with no extra probabilistic input. -/
theorem normalizedWPGFF_of_coupling
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    LQGMetric.IsNormalizedWPGFF (fun ω => normalizeWholePlane (X₀ ω)) P := by
  have hc : Measurable fun ω => -LQGMetric.circleAvg (X₀ ω) 1 0 :=
    ((LQGMetric.measurable_circleAvg_left 1 0).comp D.gff₀.measurable).neg
  refine ⟨D.gff₀.addConst hc, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero D.gff₀] with ω hω
  change LQGMetric.circleAvg
    (LQGMetric.addConst (X₀ ω) (-LQGMetric.circleAvg (X₀ ω) 1 0)) 1 0 = 0
  rw [hω, add_neg_cancel]

/-- The normalized whole-plane field is a measurable coordinate of the
frozen GFF, including its fixing additive constant. -/
theorem measurable_normalizedWholePlane
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable fun ω => normalizeWholePlane (X₀ ω) := by
  exact LQGMetric.DFGPS.L219.measurable_addConst_of D.gff₀.measurable
    (((LQGMetric.measurable_circleAvg_left 1 0).comp D.gff₀.measurable).neg)

def coneSample
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) : ConeSample :=
  { field := (MoTInput.cellModelOfCoupling D hγ).field ω
    area := (MoTInput.cellModelOfCoupling D hγ).area ω
    curve := η ω
    boundary := bm ω }

def referenceSample
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) : ReferenceSample :=
  { wholePlaneGFF := normalizeWholePlane (X₀ ω)
    wholePlaneArea := CellScaling.lqgArea γ (normalizeWholePlane (X₀ ω))
    igField := hIG₀ ω
    phase := U ω
    lebesgueCurve := ηL ω
    zeroConeField := coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
    area := CellScaling.lqgArea γ (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))
    areaCurve := η₀ ω }

/-- The frozen uniform phase law is non-atomic, so Mathlib's junk Dirac
branch for a non-a.e.-measurable `Measure.map` cannot occur. -/
theorem aemeasurable_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => (referenceSample D hγ ω).phase) P := by
  have hχ : 0 < igChi γ := by
    have hsq : γ ^ 2 < 4 := by nlinarith [hγ.1, hγ.2]
    dsimp [igChi]
    apply sub_pos.mpr
    exact (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hγ.1).2 (by nlinarith)
  have hr : 0 < 2 * Real.pi * igChi γ := by positivity
  exact MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hr D.igField.2.1

/-- Normalized Lebesgue law of the independently sampled root. -/
def rootMeasure : Measure ℂ :=
  GMS4.GMSA.normalizedLebesgueOnRootingDisk

/-- The independent marked-root extension. Its second marginal is normalized
Lebesgue area on the open unit disk, and its first marginal is `P`. -/
def rootedLaw (P : Measure Ω) : Measure (Ω × ℂ) :=
  P.prod rootMeasure

def markedRoot (v : Ω × ℂ) : ℂ := v.2

theorem rootedLaw_indep_root
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (fun v : Ω × ℂ => v.1) markedRoot (rootedLaw P) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  letI : IsProbabilityMeasure rootMeasure := by
    change IsProbabilityMeasure GMS4.GMSA.normalizedLebesgueOnRootingDisk
    infer_instance
  exact indepFun_prod measurable_id measurable_id

/-- The GMC image-mass clock of the normalized whole-plane field. The
zero-cone clock below is the one whose inverse is identified by `areaParam₀`. -/
def wholePlaneClock
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  if 0 ≤ t then (referenceSample D hγ ω).wholePlaneArea ((ηL ω) '' Icc 0 t)
  else (referenceSample D hγ ω).wholePlaneArea ((ηL ω) '' Icc t 0)

/-- The cone GMC image-mass clock of the Lebesgue-time SLE. -/
def coneClock
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  if 0 ≤ t then (coneSample D hγ ω).area ((ηL ω) '' Icc 0 t)
  else (coneSample D hγ ω).area ((ηL ω) '' Icc t 0)

/-- DMS A.10's field after adding the logarithmic root shift and resetting
its unit-circle average. -/
def rootedField (γ : ℝ) (h : MatedCRT.Field) (z₀ : ℂ) : MatedCRT.Field :=
  normalizeWholePlane (h + ConeLemmaA10.logRootingShift γ z₀)

/-- The Case 2 field removes `γ log max(|w|,1)` from the rooted field. -/
def case2Field (γ : ℝ) (h : MatedCRT.Field) (z₀ : ℂ) : MatedCRT.Field :=
  rootedField γ h z₀ - CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1))

/-- The Case 2 index `a=h_{2,1/2}(z₀)` is an observation at the marked
point, not a second independent random variable. -/
def sampledHalfCircleAverage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (v : Ω × ℂ) : ℝ :=
  LQGMetric.circleAvg
    (case2Field γ (referenceSample D hγ v.1).wholePlaneGFF v.2) (1 / 2) v.2

/-- The DMS A.10 rooted field is measurable on the independent extension. -/
theorem measurable_rootedField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable fun v : Ω × ℂ => rootedField γ (normalizeWholePlane (X₀ v.1)) v.2 := by
  have hpair : Measurable fun v : Ω × ℂ =>
      ((normalizeWholePlane (X₀ v.1), v.2) : MatedCRT.Field × ℂ) :=
    ((measurable_normalizedWholePlane D).comp measurable_fst).prodMk measurable_snd
  simpa only [Function.comp_def, rootedField, normalizeWholePlane] using
    (ConeLemmaA10.measurable_normalizedRootingMap γ).comp hpair

/-- The Case 2 field and its sampled index are measurable on the independent
root extension. The index is derived from the field and root. -/
theorem measurable_case2Field
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    Measurable fun v : Ω × ℂ => case2Field γ (normalizeWholePlane (X₀ v.1)) v.2 := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  change Measurable fun v : Ω × ℂ =>
    rootedField γ (normalizeWholePlane (X₀ v.1)) v.2 φ -
      (CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1))) φ
  exact ((LQGMetric.measurable_distOn_apply φ).comp
    (measurable_rootedField D)).sub measurable_const

theorem measurable_sampledHalfCircleAverage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    Measurable (sampledHalfCircleAverage D hγ) := by
  have hpair : Measurable fun v : Ω × ℂ =>
      ((case2Field γ (normalizeWholePlane (X₀ v.1)) v.2, ((1 / 2 : ℝ), v.2)) :
        MatedCRT.Field × (ℝ × ℂ)) :=
    (measurable_case2Field D).prodMk (measurable_const.prodMk measurable_snd)
  change Measurable fun v : Ω × ℂ => LQGMetric.circleAvg
    (case2Field γ (normalizeWholePlane (X₀ v.1)) v.2) (1 / 2) v.2
  simpa only [Function.comp_def] using LQGMetric.measurable_circleAvg.comp hpair

/-- The image-mass clock of the Lebesgue-time curve, anchored at time zero. -/
def referenceClock
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  if 0 ≤ t then (referenceSample D hγ ω).area ((ηL ω) '' Icc 0 t)
  else (referenceSample D hγ ω).area ((ηL ω) '' Icc t 0)

/-- Each cone cell has exactly its time-length in GMC area, almost surely. -/
theorem ae_cone_cell_area
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂P, ∀ x : ℤ,
      (coneSample D hγ ω).area ((coneSample D hγ ω).curve ''
        Icc (ε * ((x : ℝ) - 1)) (ε * x)) = ENNReal.ofReal ε := by
  filter_upwards [(MoTInput.cellModelOfCoupling D hγ).ae_area_curve] with ω harea x
  have hle : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have h := harea _ _ hle
  have hs : ε * (x : ℝ) - ε * ((x : ℝ) - 1) = ε := by ring
  rw [hs] at h
  exact h

/-- The cone image-mass clock is the inverse area-time change. -/
theorem ae_cone_clock_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧
      (∀ t, η ω t = ηL ω (φ t)) ∧
      ∀ t : ℝ, 0 ≤ t → coneClock D hγ ω t = ENNReal.ofReal (φ.symm t) := by
  filter_upwards [D.areaParam, (MoTInput.cellModelOfCoupling D hγ).ae_area_curve]
    with ω hparam harea
  obtain ⟨φ, hφ0, hcurve⟩ := hparam.1
  refine ⟨φ, hφ0, hcurve, ?_⟩
  intro t ht
  rw [coneClock, ite_eq_left ht]
  have h := GMS4c.area_image_interval_eq_quantum_elapsed
    ((coneSample D hγ ω).area) (ηL ω) (η ω) φ hcurve harea 0 t ht
  have hφinv0 : φ.symm 0 = 0 := by simpa only [hφ0] using (φ.symm_apply_apply (0 : ℝ))
  rw [hφinv0, sub_zero] at h
  exact h

/-- The zero-cone area is parametrized by its reference curve almost surely. -/
theorem ae_reference_area_curve
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a ≤ b →
      (referenceSample D hγ ω).area
        ((referenceSample D hγ ω).areaCurve '' Icc a b) = ENNReal.ofReal (b - a) := by
  filter_upwards [D.areaParam₀, MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ]
    with ω hparam hex a b hab
  have hex' : ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) μ := hex
  change (CellScaling.lqgArea γ (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))))
      ((η₀ ω) '' Icc a b) = ENNReal.ofReal (b - a)
  rw [CellScaling.lqgArea, dite_eq_left hex']
  exact hparam.2 _ hex'.choose_spec a b hab

/-- The zero-cone reference cells have the same exact GMC mass. -/
theorem ae_reference_cell_area
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂P, ∀ x : ℤ,
      (referenceSample D hγ ω).area ((referenceSample D hγ ω).areaCurve ''
        Icc (ε * ((x : ℝ) - 1)) (ε * x)) = ENNReal.ofReal ε := by
  filter_upwards [ae_reference_area_curve D hγ] with ω harea x
  have hle : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have h := harea _ _ hle
  have hs : ε * (x : ℝ) - ε * ((x : ℝ) - 1) = ε := by ring
  rw [hs] at h
  exact h

/-- The reference mass clock is the inverse area-time change on positive
Lebesgue-time intervals, with no additional clock hypothesis. -/
theorem ae_reference_clock_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧
      (∀ t, η₀ ω t = ηL ω (φ t)) ∧
      ∀ t : ℝ, 0 ≤ t → referenceClock D hγ ω t = ENNReal.ofReal (φ.symm t) := by
  filter_upwards [D.areaParam₀, ae_reference_area_curve D hγ]
    with ω hparam harea
  obtain ⟨φ, hφ0, hcurve⟩ := hparam.1
  refine ⟨φ, hφ0, hcurve, ?_⟩
  intro t ht
  rw [referenceClock, ite_eq_left ht]
  have h := GMS4c.area_image_interval_eq_quantum_elapsed
    ((referenceSample D hγ ω).area) (ηL ω) (η₀ ω) φ hcurve harea 0 t ht
  have hφinv0 : φ.symm 0 = 0 := by simpa only [hφ0] using (φ.symm_apply_apply (0 : ℝ))
  rw [hφinv0, sub_zero] at h
  exact h

end MatedCRTHarmonic.Canon
