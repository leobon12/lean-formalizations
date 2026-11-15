/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Trace
import InteractingSLE.Spec.Supplement.GB6GaugeEPrefix

/-!
# Compact physical separation read from two stopped records

Packet PROVE-T14-GW2ROOT2. The landed normalized polynomial contact
test and compact-square minimum apply directly to the continuous
record readers. Rational fractions make the same minimum Borel.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD

/-- A Borel normalized separation of the two recorded physical prefixes. -/
def recordSeparation (s v t : ℝ≥0) (p : RecData × RecData) : ℝ :=
  (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (separationValue (frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)))
      (frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0))))).toReal

theorem measurable_recordSeparation (s v t : ℝ≥0) : Measurable (recordSeparation s v t) := by
  have hf : ∀ q : RationalUnit × RationalUnit, Measurable fun p : RecData × RecData =>
      ENNReal.ofReal (separationValue (frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)))
        (frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0)))) := by
    intro q
    have hX : Measurable fun p : RecData × RecData =>
        frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)) :=
      (measurable_frozenTraceRead v _).comp measurable_snd
    have hA : Measurable fun p : RecData × RecData =>
        frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0)) :=
      (measurable_frozenTraceRead s _).comp measurable_fst
    exact (continuous_separationValue.measurable.comp (hX.prodMk hA)).ennreal_ofReal
  have hm := Measurable.iInf hf
  change Measurable fun p : RecData × RecData =>
    (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
      (separationValue (frozenTraceRead v p.2 (t * (q.1.val : ℝ≥0)))
        (frozenTraceRead s p.1 (s * (q.2.val : ℝ≥0))))).toReal
  exact hm.ennreal_toReal

/-- The countable readout is exactly the landed compact separation minimum. -/
theorem recordSeparation_eq_compact (s v t : ℝ≥0) (p : RecData × RecData) :
    recordSeparation s v t p =
      compactSeparation (frozenTraceRead v p.2) (frozenTraceRead s p.1) t s := by
  have hc := continuous_prefixIntegrand (continuous_frozenTraceRead v p.2).continuousOn
    (continuous_frozenTraceRead s p.1).continuousOn (t := t) (s := s)
  have hn := squareMin_nonneg hc (fun _ => separationValue_nonneg _ _)
  unfold recordSeparation
  change (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (prefixIntegrand (frozenTraceRead v p.2) (frozenTraceRead s p.1) t s
      (Prod.map fractionCast fractionCast q))).toReal = _
  rw [rationalInf_eq_squareMin hc, ENNReal.toReal_ofReal hn]
  rfl

theorem continuous_recordSeparation (s v : ℝ≥0) (p : RecData × RecData) :
    Continuous fun t => recordSeparation s v t p := by
  simp_rw [recordSeparation_eq_compact]
  exact continuous_compactSeparation (continuous_frozenTraceRead v p.2)
    (continuous_frozenTraceRead s p.1) s

theorem recordSeparation_nonneg (s v t : ℝ≥0) (p : RecData × RecData) :
    0 ≤ recordSeparation s v t p := ENNReal.toReal_nonneg

/-- Any endpoint pair bounds the compact minimum. This is a direct
specialization of the landed compact-square minimizer, including irrational times. -/
theorem recordSeparation_le_endpoint (s v t : ℝ≥0) (p : RecData × RecData)
    (hs : 0 < s) {u : ℝ≥0} (hu : u ≤ s) :
    recordSeparation s v t p ≤
      separationValue (frozenTraceRead v p.2 t) (frozenTraceRead s p.1 u) := by
  rw [recordSeparation_eq_compact]
  obtain ⟨a, ha, hmin⟩ := exists_squareMin
    (continuous_prefixIntegrand (continuous_frozenTraceRead v p.2).continuousOn
      (continuous_frozenTraceRead s p.1).continuousOn (t := t) (s := s))
  rw [compactSeparation, ha]
  let q : UnitSquare := (⟨1, zero_le_one, le_rfl⟩, ⟨u / s, zero_le, (div_le_one hs).mpr hu⟩)
  have hus : s * (u / s) = u := by field_simp
  simpa only [prefixIntegrand, q, mul_one, hus] using hmin q

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
