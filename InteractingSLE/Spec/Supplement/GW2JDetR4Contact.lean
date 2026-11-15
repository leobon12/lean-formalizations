/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Inverse
import InteractingSLE.Spec.Supplement.GB6SourceCContact

/-!
# Observable inverse-record availability and the source contact convention

The buffer test is Borel in the killed relative path. The contact time used by
the deterministic relative-chain API equals the source GW2 contact time,
including zero and infinity in the spherical inversion.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR4

open Supp8.GB6 Exist.StagedLaw GW2JDetR3

theorem measurableSet_exists_isBuffer (s t : ℝ≥0) :
    MeasurableSet {x : BufferInput | ∃ q, IsBuffer s t x q} := by
  simpa only [ofPred_exists] using
    (MeasurableSet.iUnion fun q => measurableSet_isBuffer s t q)

/-- The availability criterion proved exact for the actual relative chain is
an event of precisely the retained record and killed relative path. -/
theorem measurableSet_inverse_available (s t : ℝ≥0) :
    MeasurableSet {p : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞) |
      ∃ q, IsBuffer s t (p.1, killedCode p.2, p.2.2) q} := by
  have hm : Measurable fun p : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      (p.1, killedCode p.2, p.2.2) :=
    measurable_fst.prodMk ((measurable_killedCode.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  exact hm (measurableSet_exists_isBuffer s t)

/-- Moving spherical inversion from the growing trace to the retained trace
preserves the first contact time, as required by the original GW2 statement. -/
theorem firstContactTime_sphereInv (γ α : ℝ≥0 → ℂ) (s : ℝ≥0) :
    firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) =
    firstContactTime (fun t => (γ t : OnePoint ℂ))
      ((fun u => sphereInv (α u : OnePoint ℂ)) '' Icc 0 s) := by
  have hm : ∀ t : ℝ≥0,
      sphereInv (γ t : OnePoint ℂ) ∈ ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) ↔
        (γ t : OnePoint ℂ) ∈ ((fun u => sphereInv (α u : OnePoint ℂ)) '' Icc 0 s) := by
    intro t
    constructor
    · rintro ⟨u, hu, he⟩
      refine ⟨u, hu, (SourceC.sphereInv_eq_iff _ _).mpr ?_⟩
      simpa only [mul_comm] using (SourceC.sphereInv_eq_iff _ _).mp he.symm
    · rintro ⟨u, hu, he⟩
      refine ⟨u, hu, ((SourceC.sphereInv_eq_iff _ _).mpr ?_).symm⟩
      simpa only [mul_comm] using (SourceC.sphereInv_eq_iff _ _).mp he
  unfold firstContactTime
  simp_rw [hm]

end InteractingSLE.Theorem14.GW2JDetR4
