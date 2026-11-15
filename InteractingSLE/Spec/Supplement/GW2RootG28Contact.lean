/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Gauge
import InteractingSLE.Spec.Supplement.GB6SourceCContact

/-!
# The recorded separation gauge detects actual inversion contact

Packet PROVE-T14-GW2ROOT2. The zero/infinity convention is handled by
the landed algebraic sphere test. Compact minima give positivity before
contact and zero at finite contact, for the total continuous readers.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD

/-- The inversion contact time of the two reconstructed physical prefixes. -/
def recordContact (s v : ℝ≥0) (p : RecData × RecData) : ℝ≥0∞ :=
  firstContactTime (fun t => sphereInv (frozenTraceRead v p.2 t : OnePoint ℂ))
    ((fun u => (frozenTraceRead s p.1 u : OnePoint ℂ)) '' Icc 0 s)

/-- A trace starting at zero has normalized initial separation exactly one. -/
theorem recordSeparation_zero (s v : ℝ≥0) (p : RecData × RecData)
    (h0 : frozenTraceRead v p.2 0 = 0) : recordSeparation s v 0 p = 1 := by
  rw [recordSeparation_eq_compact]
  obtain ⟨a, ha, _⟩ := exists_squareMin
    (continuous_prefixIntegrand (continuous_frozenTraceRead v p.2).continuousOn
      (continuous_frozenTraceRead s p.1).continuousOn (t := 0) (s := s))
  rw [compactSeparation, ha]
  simp only [prefixIntegrand, zero_mul, h0, separationValue_zero_left]

/-- Every compact prefix strictly before contact has positive separation. -/
theorem recordSeparation_pos (s v t : ℝ≥0) (p : RecData × RecData)
    (ht : (t : ℝ≥0∞) < recordContact s v p) : 0 < recordSeparation s v t p := by
  rw [recordSeparation_eq_compact]
  apply squareMin_pos
    (continuous_prefixIntegrand (continuous_frozenTraceRead v p.2).continuousOn
      (continuous_frozenTraceRead s p.1).continuousOn (t := t) (s := s))
  intro q
  apply (separationValue_pos_iff _ _).mpr
  intro hzero
  have hu : ((t * q.1.val : ℝ≥0) : ℝ≥0∞) < recordContact s v p :=
    (ENNReal.coe_le_coe.mpr (fraction_mul_le t q.1)).trans_lt ht
  exact notMem_of_lt_firstContactTime hu
    ⟨s * q.2.val, ⟨zero_le, fraction_mul_le s q.2⟩,
      ((SourceC.sphereInv_eq_iff _ _).mpr hzero).symm⟩

/-- At a finite first contact the continuous separation gauge is zero. -/
theorem recordSeparation_eq_zero_at_contact (s v : ℝ≥0) (p : RecData × RecData)
    (hs : 0 < s) {T : ℝ≥0} (hT : (T : ℝ≥0∞) = recordContact s v p) :
    recordSeparation s v T p = 0 := by
  have hK : IsCompact ((fun u => (frozenTraceRead s p.1 u : OnePoint ℂ)) '' Icc 0 s) :=
    isCompact_Icc.image
      (OnePoint.continuous_coe.comp (continuous_frozenTraceRead s p.1))
  obtain ⟨u, hu, heq⟩ := firstContactTime_mem
    (continuous_sphereInv.comp
      (OnePoint.continuous_coe.comp (continuous_frozenTraceRead v p.2))) hK.isClosed hT.symm
  have hzero := (SourceC.sphereInv_eq_iff _ _).mp heq.symm
  apply le_antisymm _ (recordSeparation_nonneg _ _ _ _)
  have hle := recordSeparation_le_endpoint s v T p hs hu.2
  simpa only [separationValue, hzero, norm_zero, zero_div,
    min_eq_right zero_le_one] using hle

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
