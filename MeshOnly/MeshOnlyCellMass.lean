import MeshOnly.MeshOnlySobolevCells

/-! Finite, strictly positive actual primal-cell masses. -/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

lemma meshOnly_cellVolume_ne_top (v : T.V) : (T.cell v).volume ≠ ∞ := by
  rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact (T.cell v).compact.measure_lt_top.ne

lemma meshOnly_cellVolume_toReal_pos (v : T.V) : 0 < (T.cell v).volume.toReal := by
  rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume (T.cell v).interior_nonempty).ne'
    (T.cell v).compact.measure_lt_top.ne

end BouRabeeGwynne.OrthogonalTiling
