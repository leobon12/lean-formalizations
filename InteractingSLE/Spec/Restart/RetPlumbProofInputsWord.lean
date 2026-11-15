/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsObserved
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# Force types depend only on the harmonic mean

Packet PROVE-RETPLUMB. This removes a representation issue in applying a
finite-type bound to a mean-identifying word: sorted words with identical mean
pairings have the same genuine jumps, one-sided boundary limits, and padded
force data. Redundant entries of a word need not be bounded or removed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open LQGMetric (TestOn)
open PiecewiseConstantBoundaryData Sec2.Assembly

/-- A definitional adapter exposing the three boundary-data arguments of the
existing padded flow word. Keeping the dependent indices inside this adapter
allows ordinary congruence in its jump-set argument. -/
private def forcePadOf (κ θ : ℝ) (S : Finset ℝ) (L R : ℝ → ℝ) : Exist.Staged.PadWord :=
  (((fun i => if h : i < (S.filter (· < 0)).card + 1 then
      Fin.cons (α := fun _ => ℝ) 0
        (fun j => (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev j) - 0) ⟨i, h⟩ else 0),
    fun j => if h : j < (S.filter (0 < ·)).card + 1 then
      Fin.cons (α := fun _ => ℝ) 0
        (fun k => (S.filter (0 < ·)).orderEmbOfFin rfl k - 0) ⟨j, h⟩ else 0),
    ((fun i => if h : i < (S.filter (· < 0)).card + 1 then
      Fin.cons (α := fun _ => ℝ) (-(L 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun j => let y := (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev j)
          (R y - L y) / sleLambda κ) ⟨i, h⟩ else 0),
    fun j => if h : j < (S.filter (0 < ·)).card + 1 then
      Fin.cons (α := fun _ => ℝ) ((R 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun k => let y := (S.filter (0 < ·)).orderEmbOfFin rfl k
          (R y - L y) / sleLambda κ) ⟨j, h⟩ else 0))

/-- Equality of all mean pairings identifies the boundary functions away from
the two finite sets of word marks. Harmonic uniqueness and the real-boundary
approach filter are reused from the landed staged-law development. -/
theorem word_fn_eq_of_mean_integrals {c d : BoundaryWord}
    (hc : c.IsSorted) (hd : d.IsSorted)
    (he : ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ z, c.mean z * φ z = ∫ z, d.mean z * φ z) :
    ∀ y ∉ c.jumps ∪ d.jumps, c.fn y = d.fn y := by
  have hu := c.isBoundedHarmonicExtension_mean hc
  have hv := d.isBoundedHarmonicExtension_mean hd
  have hmean := Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl
    hu.1 hv.1 (fun φ _ => he φ)
  intro y hy
  have hyc : y ∉ (c.jumps : Set ℝ) := fun h => hy (Finset.mem_union_left _ h)
  have hyd : y ∉ (d.jumps : Set ℝ) := fun h => hy (Finset.mem_union_right _ h)
  have ht : Tendsto d.mean (𝓝[QuantumZipper.H] (y : ℂ)) (𝓝 (c.fn y)) :=
    (hu.2.2 y hyc).congr' (eventually_nhdsWithin_of_forall fun _ hz => hmean hz)
  have := Exist.StagedLaw.neBot_nhdsWithin_H_real y
  exact tendsto_nhds_unique ht (hv.2.2 y hyd)

/-- All finite force-word coordinates are invariant under equality of the
harmonic means. In particular redundant marks introduce no extra force types. -/
theorem word_forces_eq_of_mean_integrals {c d : BoundaryWord} (κ θ : ℝ)
    (hc : c.IsSorted) (hd : d.IsSorted)
    (he : ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ z, c.mean z * φ z = ∫ z, d.mean z * φ z) :
    flowLineNL c.fn c.jumps 0 = flowLineNL d.fn d.jumps 0 ∧
      flowLineNR c.fn c.jumps 0 = flowLineNR d.fn d.jumps 0 ∧
        flowPad κ θ (c, 0) = flowPad κ θ (d, 0) := by
  have hf := word_fn_eq_of_mean_integrals hc hd he
  have hL : leftLim c.fn = leftLim d.fn := leftLim_congr hf
  have hR : rightLim c.fn = rightLim d.fn := rightLim_congr hf
  have hS : jumpSet c.fn c.jumps = jumpSet d.fn d.jumps := by
    rw [← Exist.StagedLaw.jumpSet_eq_of_subset c.isPiecewiseConstantBoundaryData
        (show c.jumps ⊆ c.jumps ∪ d.jumps from Finset.subset_union_left),
      ← Exist.StagedLaw.jumpSet_eq_of_subset d.isPiecewiseConstantBoundaryData
        (show d.jumps ⊆ c.jumps ∪ d.jumps from Finset.subset_union_right)]
    unfold jumpSet
    rw [hL, hR]
  refine ⟨by simp only [flowLineNL, hS], by simp only [flowLineNR, hS], ?_⟩
  change forcePadOf κ θ (jumpSet c.fn c.jumps) (leftLim c.fn) (rightLim c.fn) =
    forcePadOf κ θ (jumpSet d.fn d.jumps) (leftLim d.fn) (rightLim d.fn)
  rw [hS, hL, hR]

/-- The finite-type bound transfers to any sorted word with the same mean
pairings. No bound on its number of redundant word entries is needed. -/
theorem hasBoundedForceType_of_mean_integrals {c d : BoundaryWord} {κ θ : ℝ}
    {N : ℕ} {weights : Finset ℝ} (hc : c.IsSorted) (hd : d.IsSorted)
    (he : ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ z, c.mean z * φ z = ∫ z, d.mean z * φ z)
    (hb : HasBoundedForceType κ θ N weights c) :
    HasBoundedForceType κ θ N weights d := by
  obtain ⟨hL, hR, hpad⟩ := word_forces_eq_of_mean_integrals κ θ hc hd he
  unfold HasBoundedForceType at hb ⊢
  rw [← hL, ← hR, ← hpad]
  exact hb

end InteractingSLE.Restart.RetAux79
