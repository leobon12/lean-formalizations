import MeshOnly.MeshOnlySobolevCells

/-! The actual volume of the cells supporting a finite vertex function.
The estimate uses the exact cellwise integral identity and ambient volume.
-/

open scoped BigOperators Classical ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma meshOnlyCellFunction_eq_zero_of_not_mem
    (R : Set T.V) [Fintype R] (u : R → ℝ) (Q : Set (Euc d))
    (hcell : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ Q)
    {x : Euc d} (hx : x ∉ Q) : T.meshOnlyCellFunction R u x = 0 := by
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : u v = 0
  · simp [hv]
  · exact Set.indicator_of_notMem (fun h => hx (hcell v hv h)) _

/-- The sum of primal volumes on the actual nonzero support is at most
the volume of any measurable finite-volume set containing those cells. -/
theorem meshOnly_supportVolume_le (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (u : R → ℝ) (Q : Set (Euc d))
    (hQ : MeasurableSet Q) (hfinite : volume Q ≠ ∞)
    (hcell : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ Q) :
    (∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0) ≤ volume.real Q := by
  have hmass : (∑ v : R, if u v ≠ 0 then (T.cell v).volume else 0) ≤ volume Q := by
    calc
      _ = ∫⁻ x, (if T.meshOnlyCellFunction R u x ≠ 0 then 1 else 0 : ℝ≥0∞)
          ∂volume := by
        rw [T.meshOnlyCellFunction_lintegral_transform hd R u
          (fun a => if a ≠ 0 then 1 else 0) (by simp)]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp
      _ ≤ ∫⁻ x, Q.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ Q
        · simp only [Set.indicator_of_mem hx]
          split_ifs <;> simp
        · simp [Set.indicator_of_notMem hx,
            T.meshOnlyCellFunction_eq_zero_of_not_mem R u Q hcell hx]
      _ = volume Q := by rw [lintegral_indicator hQ, lintegral_one, Measure.restrict_apply_univ]
  have hterm (v : R) : (if u v ≠ 0 then (T.cell v).volume else 0 : ℝ≥0∞) ≠ ∞ := by
    split_ifs
    · rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact (T.cell v).compact.measure_lt_top.ne
    · simp
  have hreal := ENNReal.toReal_mono hfinite hmass
  rw [ENNReal.toReal_sum (fun (v : R) _ => hterm v)] at hreal
  simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero, Measure.real] using hreal

end BouRabeeGwynne.OrthogonalTiling
