/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.GermVersion

/-! # Measurability of harmonic distributions on a fixed open domain

The existing countable Laplacian-test form of Weyl's lemma makes harmonicity
a measurable event in distribution space. This permits transporting actual
harmonic means to the retained-history law without an extra measurability input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology TopologicalSpace
open LQGMetric
open LQGMetric.MarkovAsm (toZs)

namespace InteractingSLE.Sec5.Aux61GHist
open LocalSets

/-- Harmonicity is equivalent to annihilating the Laplacians of the
existing countable test family. -/
theorem isHarmonicDistOn_iff_lapTests_eq_zero {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    (T : DistOn upperHalfPlaneOpens) :
    IsHarmonicDistOn T U ↔ ∀ k : ℕ × ℕ, T (lapTest U (toZs (distGen U k))) = 0 := by
  constructor
  · intro hT k
    exact IsHarmonicDistOn.apply_lapTest_eq_zero U.isOpen hT hU subset_rfl _
  · exact isHarmonicDistOn_of_lapTest hU

/-- Harmonicity on every fixed open subdomain is measurable in the
cylinder sigma-algebra of distributions. -/
theorem measurableSet_isHarmonicDistOn {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) :
    MeasurableSet {T : DistOn upperHalfPlaneOpens | IsHarmonicDistOn T U} := by
  have hm : ∀ k : ℕ × ℕ,
      MeasurableSet {T : DistOn upperHalfPlaneOpens | T (lapTest U (toZs (distGen U k))) = 0} := by
    intro k
    exact measurableSet_eq_fun
      ((measurable_pi_apply _).comp (LQGMetric.measurable_distEval _)) measurable_const
  have he : {T : DistOn upperHalfPlaneOpens | IsHarmonicDistOn T U} =
      ⋂ k : ℕ × ℕ, {T | T (lapTest U (toZs (distGen U k))) = 0} := by
    ext T
    simp only [mem_ofPred_eq, mem_iInter]
    exact isHarmonicDistOn_iff_lapTests_eq_zero hU T
  rw [he]
  exact MeasurableSet.iInter hm

/-- In particular the entire-half-plane harmonicity event is measurable. -/
theorem measurableSet_isHarmonicDistOn_H :
    MeasurableSet {T : DistOn upperHalfPlaneOpens | IsHarmonicDistOn T QuantumZipper.H} :=
  measurableSet_isHarmonicDistOn (U := upperHalfPlaneOpens) le_rfl

end InteractingSLE.Sec5.Aux61GHist
