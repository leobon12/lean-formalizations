/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEInverse
import Mathlib.Topology.Order.IsLUB

/-!
# Compact separation minima and rational prefix tests

Rational fractions are dense in the closed unit square. Hence the Borel
countable separation readout equals a compact minimum on continuous prefixes.
The compact-minimum continuity theorem is reused from Mathlib.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.GaugeE

open ReadD Exist.StagedLaw

abbrev UnitSegment := Icc (0 : ℝ≥0) 1
abbrev UnitSquare := UnitSegment × UnitSegment

/-- A rational fraction as a point of the compact real unit interval. -/
def fractionCast (q : RationalUnit) : UnitSegment :=
  ⟨(q.val : ℝ≥0), zero_le, by exact_mod_cast q.property⟩

/-- Clamp a real number to the compact nonnegative unit interval. -/
def unitClamp (x : ℝ) : UnitSegment := ⟨min 1 x.toNNReal, zero_le, min_le_left _ _⟩

theorem continuous_unitClamp : Continuous unitClamp :=
  (continuous_const.min continuous_real_toNNReal).subtype_mk _

theorem denseRange_fractionCast : DenseRange fractionCast := by
  have hsurj : Function.Surjective unitClamp := by
    intro x
    refine ⟨x.val, ?_⟩
    apply Subtype.ext
    simp only [unitClamp, Real.toNNReal_coe, min_eq_right x.property.2]
  have hd := hsurj.denseRange.comp (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)) continuous_unitClamp
  apply hd.mono
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨min 1 q.toNNRat, min_le_left _ _⟩, ?_⟩
  apply Subtype.ext
  simp only [fractionCast, Function.comp_apply, unitClamp, NNRat.cast_min, NNRat.cast_one, coe_toNNRat_eq]

theorem denseRange_fractionSquare : DenseRange (Prod.map fractionCast fractionCast) :=
  denseRange_fractionCast.prodMap denseRange_fractionCast

/-- The minimum over the compact square. -/
def squareMin (f : UnitSquare → ℝ) : ℝ := sInf (range f)

theorem exists_squareMin {f : UnitSquare → ℝ} (hc : Continuous f) :
    ∃ p : UnitSquare, squareMin f = f p ∧ ∀ q, f p ≤ f q := by
  obtain ⟨p, _, he, hle⟩ := (isCompact_univ : IsCompact (univ : Set UnitSquare)).exists_sInf_image_eq_and_le
    (show (univ : Set UnitSquare).Nonempty from ⟨(⟨0, zero_le, zero_le_one⟩, ⟨0, zero_le, zero_le_one⟩), mem_univ _⟩)
    hc.continuousOn
  exact ⟨p, by simpa only [squareMin, image_univ] using he, fun q => hle q (mem_univ q)⟩

theorem squareMin_nonneg {f : UnitSquare → ℝ} (hc : Continuous f) (h : ∀ p, 0 ≤ f p) : 0 ≤ squareMin f := by
  obtain ⟨p, he, _⟩ := exists_squareMin hc
  rw [he]
  exact h p

theorem squareMin_pos {f : UnitSquare → ℝ} (hc : Continuous f) (h : ∀ p, 0 < f p) : 0 < squareMin f := by
  obtain ⟨p, he, _⟩ := exists_squareMin hc
  rw [he]
  exact h p

theorem continuous_squareMin {Y : Type*} [TopologicalSpace Y] {f : Y → UnitSquare → ℝ}
    (hc : Continuous (Function.uncurry f)) : Continuous fun y => squareMin (f y) := by
  simpa only [squareMin, image_univ] using
    (isCompact_univ : IsCompact (univ : Set UnitSquare)).continuous_sInf hc

/-- The rational ENNReal infimum equals the finite compact minimum for a
continuous function. -/
theorem rationalInf_eq_squareMin {f : UnitSquare → ℝ} (hc : Continuous f) :
    (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal (f (Prod.map fractionCast fractionCast q))) =
      ENNReal.ofReal (squareMin f) := by
  have hf : Continuous (fun p => ENNReal.ofReal (f p)) := ENNReal.continuous_ofReal.comp hc
  have he : (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal (f (Prod.map fractionCast fractionCast q))) =
      ⨅ p : UnitSquare, ENNReal.ofReal (f p) := by
    apply le_antisymm
    · have hb : IsClosed {p : UnitSquare |
          (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal (f (Prod.map fractionCast fractionCast q))) ≤
            ENNReal.ofReal (f p)} := isClosed_le continuous_const hf
      have hlow := isClosed_property denseRange_fractionSquare hb (fun q => iInf_le
        (fun q : RationalUnit × RationalUnit => ENNReal.ofReal (f (Prod.map fractionCast fractionCast q))) q)
      exact le_iInf hlow
    · exact le_iInf fun q => iInf_le _ (Prod.map fractionCast fractionCast q)
  rw [he]
  obtain ⟨p, hp, hmin⟩ := exists_squareMin hc
  rw [hp]
  exact le_antisymm (iInf_le _ p) (le_iInf fun q => ENNReal.ofReal_le_ofReal (hmin q))

end InteractingSLE.Supp8.GB6.GaugeE
