import MatedCRTHarmonic.GMS4c.MassClock
import MatedCRTHarmonic.GMS4c.ContVersion
import MatedCRTHarmonic.MoTPort.Foundations.ConeArea

/-!
# Measurable local mass clocks on the configuration space

On the finite-area part of the local configuration, the area of each compact
subsegment of a rational-point excursion is a Borel function of the stored
measure and stored excursion. This is the measurable input for reconstructing
quantum time from Lebesgue time in [18] Lemma 4.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MatedCRTHarmonic.MoTPort
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

/-- The finite-area locus in the local configuration. Bounded `V` and a
locally finite LQG area measure place the source configuration here. -/
abbrev FiniteLocalConfiguration (V : TopologicalSpace.Opens ℂ) : Type :=
  {x : LocalConfiguration V // IsFiniteMeasure x.1.1}

/-- The restricted area measure, viewed as a finite measure on the
finite-area locus. -/
def finiteLocalArea {V : TopologicalSpace.Opens ℂ}
    (x : FiniteLocalConfiguration V) : FiniteMeasure ℂ :=
  ⟨x.1.1.1, x.2⟩

theorem measurable_finiteLocalArea (V : TopologicalSpace.Opens ℂ) :
    Measurable (finiteLocalArea (V := V)) :=
  (measurable_fst.comp (measurable_fst.comp measurable_subtype_coe)).subtype_mk

/-- A continuous version of the excursion segment at the rational point `q`.
For a genuine excursion this is the original segment. -/
def finiteLocalSegment {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) : C(ℝ, ℂ) :=
  contVersion (x.1.2 q)

theorem measurable_finiteLocalSegment (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) : Measurable (finiteLocalSegment (V := V) q) :=
  measurable_contVersion.comp
    ((measurable_pi_apply q).comp (measurable_snd.comp measurable_subtype_coe))

/-- The mass of a compact subsegment, determined by the finite local
configuration. -/
def localSegmentMass {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (a b : ℝ) (x : FiniteLocalConfiguration V) : ℝ≥0∞ :=
  massClock a b (finiteLocalArea x) (finiteLocalSegment q x)

theorem measurable_localSegmentMass (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) (a b : ℝ) :
    Measurable (localSegmentMass (V := V) q a b) :=
  (measurable_massClock a b).comp
    ((measurable_finiteLocalArea V).prodMk (measurable_finiteLocalSegment V q))

/-- The elapsed quantum-time coordinate of a compact excursion subsegment. -/
def localQuantumElapsed {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (a b : ℝ) (x : FiniteLocalConfiguration V) : ℝ :=
  (localSegmentMass q a b x).toReal

theorem measurable_localQuantumElapsed (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) (a b : ℝ) :
    Measurable (localQuantumElapsed (V := V) q a b) :=
  ENNReal.measurable_toReal.comp (measurable_localSegmentMass V q a b)

/-- For bounded `V`, the locally finite GMC measure gives a finite local
configuration. -/
def finiteLocalConfigurationOfField (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) (γ : ℝ)
    (h : LQGMetric.DistC) (ηL : C(ℝ, ℂ)) : FiniteLocalConfiguration V := by
  refine ⟨localConfiguration V (qAreaC γ h) h ηL, ?_⟩
  have hfin : qAreaC γ h V < ⊤ :=
    (measure_mono (subset_closure : (V : Set ℂ) ⊆ closure V)).trans_lt
      (ConeArea.qAreaC_compact_lt_top γ h hVb.isCompact_closure)
  exact isFiniteMeasure_restrict.mpr hfin.ne

/-- The configuration's segment clock is exactly the restricted GMC mass of
The source excursion, at any rational point lying in `V`. -/
theorem localSegmentMass_ofField (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) (γ : ℝ)
    (h : LQGMetric.DistC) (ηL : C(ℝ, ℂ)) (q : ℚ × ℚ)
    (hq : ratPt q ∈ V) (a b : ℝ) :
    localSegmentMass q a b (finiteLocalConfigurationOfField V hVb γ h ηL) =
      ((qAreaC γ h).restrict V)
        (MatedCRT.excursionSegment ηL V (ratPt q) '' Icc a b) := by
  have hc : Continuous (MatedCRT.excursionSegment ηL V (ratPt q)) := by
    unfold MatedCRT.excursionSegment
    fun_prop
  unfold localSegmentMass finiteLocalSegment finiteLocalArea massClock
    finiteLocalConfigurationOfField localConfiguration
  simp only [hq, ↓reduceIte, contVersion_coe hc]
  rfl

/-- On an actual area-parametrized sample, the Borel clock read from the
local configuration is the elapsed quantum time in the rational excursion. -/
theorem localSegmentMass_eq_quantum_elapsed
    (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) (γ : ℝ)
    (h : LQGMetric.DistC) (ηL η : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t →
      qAreaC γ h (η '' Icc s t) = ENNReal.ofReal (t - s))
    (q : ℚ × ℚ) (hq : ratPt q ∈ V) (u : ℝ)
    (hex : IsExcursion ηL V (MatedCRT.entryBefore ηL V (ratPt q))
      (MatedCRT.exitAfter ηL V (ratPt q)))
    (hu : 0 ≤ u)
    (hule : u ≤ MatedCRT.exitAfter ηL V (ratPt q) -
      MatedCRT.entryBefore ηL V (ratPt q)) :
    localSegmentMass q 0 u (finiteLocalConfigurationOfField V hVb γ h ηL) =
      ENNReal.ofReal (φ.symm (MatedCRT.entryBefore ηL V (ratPt q) + u) -
        φ.symm (MatedCRT.entryBefore ηL V (ratPt q))) := by
  rw [localSegmentMass_ofField V hVb γ h ηL q hq 0 u]
  exact restricted_excursion_mass_eq_quantum_elapsed_closed
    (qAreaC γ h) ηL η φ hcurve hparam V (ratPt q) u
    hex hu hule

/-- The measurable real clock reads the source quantum elapsed time exactly. -/
theorem localQuantumElapsed_eq_quantum_elapsed
    (V : TopologicalSpace.Opens ℂ)
    (hVb : Bornology.IsBounded (V : Set ℂ)) (γ : ℝ)
    (h : LQGMetric.DistC) (ηL η : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ)
    (hcurve : ∀ t, η t = ηL (φ t))
    (hparam : ∀ s t : ℝ, s ≤ t →
      qAreaC γ h (η '' Icc s t) = ENNReal.ofReal (t - s))
    (q : ℚ × ℚ) (hq : ratPt q ∈ V) (u : ℝ)
    (hex : IsExcursion ηL V (MatedCRT.entryBefore ηL V (ratPt q))
      (MatedCRT.exitAfter ηL V (ratPt q)))
    (hu : 0 ≤ u)
    (hule : u ≤ MatedCRT.exitAfter ηL V (ratPt q) -
      MatedCRT.entryBefore ηL V (ratPt q)) :
    localQuantumElapsed q 0 u (finiteLocalConfigurationOfField V hVb γ h ηL) =
      φ.symm (MatedCRT.entryBefore ηL V (ratPt q) + u) -
        φ.symm (MatedCRT.entryBefore ηL V (ratPt q)) := by
  unfold localQuantumElapsed
  rw [localSegmentMass_eq_quantum_elapsed V hVb γ h ηL η φ hcurve hparam
    q hq u hex hu hule]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr
    (φ.symm.monotone (by linarith :
      MatedCRT.entryBefore ηL V (ratPt q) ≤
        MatedCRT.entryBefore ηL V (ratPt q) + u)))

end MatedCRTHarmonic.GMS4c
