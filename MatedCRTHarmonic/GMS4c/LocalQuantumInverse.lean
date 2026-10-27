import MatedCRTHarmonic.GMS4c.LocalClockMeasurable
import MatedCRTHarmonic.GMS4c.MultiVisitNull
import MatedCRTHarmonic.GMS4c.ContVersion
import MatedCRTHarmonic.GMS4c.LocalConfiguration

/-!
# Borel quantum-time evaluations of a stored local excursion

The rational upper cut from `CellScaling` inverts the restricted area clock of an
excursion. The value at each quantum time is Borel on the finite local
configuration space.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open Set

open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

/-- The mass of an initial part of a stored excursion grows with its endpoint. -/
theorem localQuantumElapsed_mono {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V)
    {u v : ℝ} (huv : u ≤ v) :
    localQuantumElapsed q 0 u x ≤ localQuantumElapsed q 0 v x := by
  unfold localQuantumElapsed localSegmentMass massClock
  apply ENNReal.toReal_mono
  · exact (measure_lt_top (finiteLocalArea x)
      ((finiteLocalSegment q x) '' Icc 0 v)).ne
  · apply measure_mono
    apply image_mono
    exact Icc_subset_Icc le_rfl huv

/-- A negative endpoint has zero initial excursion mass. -/
theorem localQuantumElapsed_eq_zero_of_neg {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V)
    {u : ℝ} (hu : u < 0) : localQuantumElapsed q 0 u x = 0 := by
  simp [localQuantumElapsed, localSegmentMass, massClock, Icc_eq_empty_of_lt hu]

/-- The rational upper cut of a real number is the number itself. -/
theorem local_iInf_rational_upperCut (x : ℝ) :
    (⨅ r : ℚ, if x ≤ (r : ℝ) then (((r : ℝ) : EReal)) else ⊤) =
      (x : EReal) := by
  apply le_antisymm
  · by_contra h
    have hx : (x : EReal) <
        (⨅ r : ℚ, if x ≤ (r : ℝ) then (((r : ℝ) : EReal)) else ⊤) :=
      lt_of_not_ge h
    obtain ⟨r, hxr, hr⟩ := EReal.exists_rat_btwn_of_lt hx
    have hxr' : x ≤ (r : ℝ) := (EReal.coe_lt_coe_iff.mp hxr).le
    have hi : (⨅ s : ℚ, if x ≤ (s : ℝ) then (((s : ℝ) : EReal)) else ⊤) ≤
        ((r : ℝ) : EReal) := by
      calc
        _ ≤ (if x ≤ (r : ℝ) then (((r : ℝ) : EReal)) else ⊤) :=
          iInf_le (fun s : ℚ => if x ≤ (s : ℝ) then (((s : ℝ) : EReal)) else ⊤) r
        _ ≤ ((r : ℝ) : EReal) := by simp [hxr']
    exact (not_le_of_gt hr) hi
  · refine le_iInf fun r => ?_
    by_cases hr : x ≤ (r : ℝ)
    · simp only [hr, ite_true]
      exact EReal.coe_le_coe_iff.mpr hr
    · simp [hr]

/-- A rational-cut inverse of the restricted mass clock on one excursion. -/
def localQuantumInverse {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) (t : ℝ) : ℝ :=
  (⨅ r : ℚ, if t ≤ localQuantumElapsed q 0 r x then
    (((r : ℝ) : EReal)) else ⊤).toReal

theorem measurable_localQuantumInverse (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) :
    Measurable fun p : FiniteLocalConfiguration V × ℝ =>
      localQuantumInverse q p.1 p.2 := by
  apply Measurable.ereal_toReal
  refine Measurable.iInf fun r : ℚ => ?_
  exact Measurable.ite
    (measurableSet_le measurable_snd
      ((measurable_localQuantumElapsed V q 0 r).comp measurable_fst))
    measurable_const measurable_const

/-- On an excursion whose local mass clock is a translated inverse order
isomorphism, the Borel rational cut recovers the exact inverse time. -/
theorem localQuantumInverse_eq_orderIso
    {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V)
    (φ : ℝ ≃o ℝ) {a b t : ℝ}
    (hab : a < b) (ht : 0 < t)
    (htop : t ≤ φ.symm b - φ.symm a)
    (hclock : ∀ u : ℝ, 0 ≤ u → u ≤ b - a →
      localQuantumElapsed q 0 u x = φ.symm (a + u) - φ.symm a) :
    localQuantumInverse q x t = φ (φ.symm a + t) - a := by
  let r₀ := φ (φ.symm a + t) - a
  have hr₀pos : 0 < r₀ := by
    have h := φ.strictMono (show φ.symm a < φ.symm a + t by linarith)
    rw [φ.apply_symm_apply] at h
    dsimp [r₀]
    linarith
  have hr₀le : r₀ ≤ b - a := by
    have h := φ.monotone (show φ.symm a + t ≤ φ.symm b by linarith)
    rw [φ.apply_symm_apply] at h
    dsimp [r₀]
    linarith
  have hiff (r : ℚ) : t ≤ localQuantumElapsed q 0 r x ↔ r₀ ≤ (r : ℝ) := by
    by_cases hrneg : (r : ℝ) < 0
    · rw [localQuantumElapsed_eq_zero_of_neg q x hrneg]
      exact iff_of_false (not_le.mpr ht) (not_le.mpr (hrneg.trans hr₀pos))
    have hrnonneg : 0 ≤ (r : ℝ) := le_of_not_gt hrneg
    by_cases hrle : (r : ℝ) ≤ b - a
    · rw [hclock r hrnonneg hrle]
      constructor
      · intro h
        have h' : φ.symm a + t ≤ φ.symm (a + r) := by linarith
        have h'' := (φ.le_symm_apply).1 h'
        dsimp [r₀]
        linarith
      · intro h
        have h' : φ (φ.symm a + t) ≤ a + r := by
          dsimp [r₀] at h
          linarith
        have h'' := (φ.le_symm_apply).2 h'
        linarith
    · have hrgt : b - a < (r : ℝ) := lt_of_not_ge hrle
      have hm := localQuantumElapsed_mono q x hrgt.le
      rw [hclock (b - a) (by linarith [hab]) le_rfl] at hm
      have hmass : t ≤ localQuantumElapsed q 0 r x := by
        calc
          t ≤ φ.symm b - φ.symm a := htop
          _ = φ.symm (a + (b - a)) - φ.symm a := by simp
          _ ≤ localQuantumElapsed q 0 r x := hm
      exact iff_of_true hmass (hr₀le.trans hrgt.le)
  unfold localQuantumInverse
  simp_rw [hiff]
  rw [local_iInf_rational_upperCut, EReal.toReal_coe]

/-- The point of the stored excursion at elapsed quantum time `t`. -/
def localQuantumEval {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) (t : ℝ) : ℂ :=
  finiteLocalSegment q x (localQuantumInverse q x t)

theorem measurable_localQuantumEval (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) :
    Measurable fun p : FiniteLocalConfiguration V × ℝ =>
      localQuantumEval q p.1 p.2 := by
  exact continuous_eval.measurable.comp
    ((measurable_finiteLocalSegment V q).comp measurable_fst |>.prodMk
      (measurable_localQuantumInverse V q))

/-- Time-indexed local evaluations, with the product measurable space.
Correctness is asserted only at interior quantum times: outside the mass
range, `EReal.toReal` supplies a junk value. -/
def localQuantumPath {V : TopologicalSpace.Opens ℂ}
    (q : ℚ × ℚ) (x : FiniteLocalConfiguration V) : ℝ → ℂ :=
  fun t => localQuantumEval q x t

theorem measurable_localQuantumPath (V : TopologicalSpace.Opens ℂ)
    (q : ℚ × ℚ) : Measurable (localQuantumPath (V := V) q) := by
  refine measurable_pi_iff.mpr fun t => ?_
  exact (measurable_localQuantumEval V q).comp
    (measurable_id.prodMk measurable_const)

/-- Countable measurable selection preserves measurability of a family of
measurable maps. -/
private theorem measurable_rationalSelect {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (q : α → ℚ × ℚ) (hq : Measurable q)
    (f : ℚ × ℚ → α → β) (hf : ∀ r, Measurable (f r)) :
    Measurable fun x => f (q x) x := by
  intro s hs
  have heq : {x : α | f (q x) x ∈ s} =
      ⋃ r : ℚ × ℚ, {x : α | q x = r ∧ f r x ∈ s} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨fun h => ⟨q x, rfl, h⟩, fun ⟨r, hr, h⟩ => hr ▸ h⟩
  change MeasurableSet {x : α | f (q x) x ∈ s}
  rw [heq]
  exact MeasurableSet.iUnion fun r =>
    (measurableSet_eq_fun hq measurable_const).inter ((hf r) hs)

end MatedCRTHarmonic.GMS4c

