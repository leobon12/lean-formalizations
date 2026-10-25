import SupercriticalLQGUniqueness.B2.Iface.Statements
import Mathlib.Topology.Semicontinuity.Basic

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 


theorem setDistance_eq_at_min (D : LSCMetric) {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty) :
    ∃ u ∈ A, ∃ v ∈ B, Iface.setDistance D.1 A B = D.1 (u, v) := by
  obtain ⟨p, hp, hmin⟩ :=
    (D.2.2.lowerSemicontinuousOn (A ×ˢ B)).exists_isMinOn
      (hneA.prod hneB) (hA.prod hB)
  rcases p with ⟨u, v⟩
  obtain ⟨hu, hv⟩ := hp
  refine ⟨u, hu, v, hv, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le u (iInf_le_of_le hu
      (iInf_le_of_le v (iInf_le _ hv)))
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    exact isMinOn_iff.mp hmin ⟨x, y⟩ ⟨hx, hy⟩

 

theorem rationalCircle_distance_attained (D : LSCMetric) {O O' : Set ℂ}
    (hO : Iface.IsRationalCircle O) (hO' : Iface.IsRationalCircle O') :
    ∃ u ∈ O, ∃ v ∈ O', Iface.setDistance D.1 O O' = D.1 (u, v) := by
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  obtain ⟨x', y', r', hr', rfl⟩ := hO'
  exact setDistance_eq_at_min D (isCompact_sphere _ _) (isCompact_sphere _ _)
    (NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr hr))
    (NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr hr'))

end SupercriticalLQGUniqueness.B2.PfeLocal
