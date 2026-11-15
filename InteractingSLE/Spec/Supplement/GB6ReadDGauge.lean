/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6ReadDCoordinates

/-!
# An explicit Borel causal separation candidate

The normalized polynomial contact test detects physical contact, while its
value against the flow's starting point tends to zero when the physical trace
escapes to infinity. Countable rational prefix tests make the readout Borel
and causal on arbitrary recorded paths. Its continuous gauge version at the
source coordinates remains a named mathematical input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.ReadD

open Exist.StagedLaw RelDrv.Version

/-- Rational fractions of a closed prefix, including both endpoints. -/
abbrev RationalUnit := {q : ℚ≥0 // q ≤ 1}

/-- A bounded contact test with an escape cutoff. -/
def separationValue (z a : ℂ) : ℝ := min 1 (‖z * a + 1‖ / (1 + ‖z‖))

theorem separationValue_nonneg (z a : ℂ) : 0 ≤ separationValue z a :=
  le_min zero_le_one (div_nonneg (norm_nonneg _) (by positivity))

theorem separationValue_le_one (z a : ℂ) : separationValue z a ≤ 1 := min_le_left _ _

theorem separationValue_pos_iff (z a : ℂ) : 0 < separationValue z a ↔ z * a + 1 ≠ 0 := by
  rw [separationValue, lt_min_iff, and_iff_right zero_lt_one,
    div_pos_iff_of_pos_right (show 0 < 1 + ‖z‖ by positivity), norm_pos_iff]

theorem separationValue_zero_left (a : ℂ) : separationValue 0 a = 1 := by
  simp [separationValue]

/-- The retained flow trace, read at a fixed time from its recorded driver. -/
def recordTrace (t : ℝ≥0) (r : RecData) : ℂ := LP.traceAt t (fun u => rdrv r u)

theorem measurable_recordTrace (t : ℝ≥0) : Measurable (recordTrace t) :=
  (LP.measurable_traceAt t).comp (measurable_pi_iff.2 fun u => measurable_rdrv_apply u)

/-- The infimum over rational fractions of the explored and retained prefixes.
Every evaluation of the explored driver is at a time at most `t`. -/
def separationRead (s : ℝ≥0) : GaugeReadout := fun t p =>
  (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (separationValue (physicalTrace s (t * (q.1.val : ℝ≥0)) p)
      (recordTrace (s * (q.2.val : ℝ≥0)) p.1))).toReal

theorem measurable_separationRead (s t : ℝ≥0) : Measurable (separationRead s t) := by
  apply ENNReal.measurable_toReal.comp
  apply Measurable.iInf
  intro q
  apply Measurable.ennreal_ofReal
  unfold separationValue
  exact measurable_const.min
    (((measurable_physicalTrace s _).mul ((measurable_recordTrace _).comp measurable_fst)).add_const 1 |>.norm |>.div
      (measurable_const.add (measurable_physicalTrace s _).norm))

theorem isCausal_separationRead (s : ℝ≥0) : IsCausal (separationRead s) := by
  intro t r w w' h
  unfold separationRead
  apply congrArg ENNReal.toReal
  apply iInf_congr
  intro q
  have hq : (q.1.val : ℝ≥0) ≤ 1 := by exact_mod_cast q.1.property
  have hqt : t * (q.1.val : ℝ≥0) ≤ t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (zero_le : (0 : ℝ≥0) ≤ t)
  have he := physicalTrace_congr s (t * (q.1.val : ℝ≥0)) r (fun u hu => h u (hu.trans hqt))
  exact congrArg (fun z : ℂ => ENNReal.ofReal
    (separationValue z (recordTrace (s * (q.2.val : ℝ≥0)) r))) he

/-- Positivity of a uniform physical separation bound survives the rational
prefix infimum. This does not assert a bound for irregular readouts. -/
theorem le_separationRead (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ q : RationalUnit × RationalUnit, c ≤
      separationValue (physicalTrace s (t * (q.1.val : ℝ≥0)) p)
        (recordTrace (s * (q.2.val : ℝ≥0)) p.1)) : c ≤ separationRead s t p := by
  let q0 : RationalUnit := ⟨0, zero_le_one⟩
  have hbound : (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
      (separationValue (physicalTrace s (t * (q.1.val : ℝ≥0)) p)
        (recordTrace (s * (q.2.val : ℝ≥0)) p.1))) ≤ 1 := by
    exact (iInf_le _ (q0, q0)).trans (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (separationValue_le_one _ _))
  have hle : ENNReal.ofReal c ≤ ⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
      (separationValue (physicalTrace s (t * (q.1.val : ℝ≥0)) p)
        (recordTrace (s * (q.2.val : ℝ≥0)) p.1)) :=
    le_iInf fun q => ENNReal.ofReal_le_ofReal (h q)
  have ht := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hbound) hle
  simpa only [ENNReal.toReal_ofReal hc, separationRead] using ht

/-- The remaining regularization and terminal-geometry input for this
specific, already Borel causal readout. It is not asserted without a proof. -/
def HasRegularSeparationVersion {Ω : Type*} [MeasurableSpace Ω] (s : ℝ≥0) (P : Measure Ω)
    (rec : Ω → RecData) (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) : Prop :=
  ∃ g : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (g t)) ∧ (∀ ω, Continuous (g · ω)) ∧
    (∀ ω, 0 < g 0 ω) ∧ (∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < L ω → 0 < g t ω) ∧
    (∀ ω (t : ℝ≥0), (t : ℝ≥0∞) = L ω → g t ω = 0) ∧
    ∀ᵐ ω ∂P, separationRead s 0 (rec ω, fun _ => 0) = g 0 ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → separationRead s t (rec ω, fun u => D u ω) = g t ω

/-- The Borel and causal clauses of the readout require no new hypothesis. -/
theorem exists_aeSeparationReadout {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {P : Measure Ω}
    {rec : Ω → RecData} {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (h : HasRegularSeparationVersion s P rec D L) :
    ∃ g, SourceC.AESeparationReadout P rec D L g (separationRead s) := by
  obtain ⟨g, hm, hc, h0, hp, ht, hr⟩ := h
  exact ⟨g, hm, hc, h0, hp, ht, measurable_separationRead s, isCausal_separationRead s, hr⟩

/-- The explicit separation candidate, once it has the named regular
version, supplies the previous source readout input. -/
theorem hasSourceReadout_of_regularSeparation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κcf κ θcf θ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hcf : IsFlowLineDriver κcf b' J' θcf P h' W ζ)
    (hflow : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) (s : ℝ≥0) (hs : 0 < s)
    (hreg : HasRegularSeparationVersion s P (gb6Rec s Wα ζα)
      (SourceC.sourceDriver hcf hflow hγ hα s hs) (SourceC.sourceLife hcf hflow hγ hα s hs)) :
    SourceC.HasSourceReadout hcf hflow hγ hα s hs := by
  obtain ⟨g, hg⟩ := exists_aeSeparationReadout hreg
  exact ⟨g, separationRead s, hg⟩

end InteractingSLE.Supp8.GB6.ReadD
