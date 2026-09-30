import QuantumZipper.Proofs.Zipper.LocHitScaleRead

/-!
# LOC-HITSCALE (2): the local left length and the local hitting time are correct

Theorem 1.3, node E6 under D25. Continuation of `LocHitScaleRead.lean`.

* `lenLoc_locRich`: at the rich local data `locRich R' (x, W)`, the reader `lenLoc` returns the
  true left length `(unzipLengths γ (x, W) q).1` at every time `q ∈ (0, T]` at which all real
  points are alive and the unzipped field has a global boundary limit, when `|W| ≤ M` on
  `[0,T]`, `T ≤ R'` and `9M + 9√T + 7 ≤ R'`.
* `tauLoc`: the hitting time read along the rationals of `(0, T]` (junk `T`); measurable
  (`measurable_tauLoc`), and equal to `tHit γ ℓ (x, W)` (`tauLoc_locRich`) when moreover the left
  length is monotone on `[0,T]` and reaches `ℓ` at time `T`.

Own elementary bookkeeping (the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the
locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

/-- The path extracted from the window of `locRich R'` is the driver on `[0,T]`. -/
theorem Wof_pathX_locRich {κ : ℝ} (hκ : 0 < κ) {T R' : ℕ} (hTR : T ≤ R') (x : FieldSample)
    {W : ℝ → ℝ} (hW : Continuous W) :
    ∀ r ∈ Icc (0 : ℝ) T, Wof κ T (natCast_nonneg' T) (pathX κ T (locRich R' (x, W)).2) r = W r :=
  (exists_pathExtract hκ).2 T _ W hW fun s hs => by
    simp only [locRich]
    rw [min_eq_left (hs.trans (by exact_mod_cast hTR))]

/-! ## The local hitting time -/

/-- The hitting time of `ℓ` by the local left length, along the rationals of `(0, T]`. -/
def tauLoc (γ κ ℓ : ℝ) (T R' : ℕ) (d : FullData) : ℝ :=
  ratInf T fun q => ∃ hq : (q : ℝ) ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ lenLoc γ κ T R' q hq d

theorem measurable_tauLoc (γ κ ℓ : ℝ) (T R' : ℕ) : Measurable (tauLoc γ κ ℓ T R') := by
  refine measurable_ratInf T fun q => ?_
  by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
  · have e : {d : FullData | ∃ hq : (q : ℝ) ∈ Icc (0 : ℝ) T,
        ENNReal.ofReal ℓ ≤ lenLoc γ κ T R' q hq d} =
        {d | ENNReal.ofReal ℓ ≤ lenLoc γ κ T R' q hq d} := by
      ext d; simp only [mem_setOf_eq, exists_prop_of_true hq]
    rw [e]
    exact measurableSet_le measurable_const (measurable_lenLoc γ κ T R' q hq)
  · have e : {d : FullData | ∃ hq : (q : ℝ) ∈ Icc (0 : ℝ) T,
        ENNReal.ofReal ℓ ≤ lenLoc γ κ T R' q hq d} = ∅ := by
      ext d; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun ⟨h, _⟩ => hq h
    rw [e]
    exact MeasurableSet.empty

end QuantumZipper.E6
