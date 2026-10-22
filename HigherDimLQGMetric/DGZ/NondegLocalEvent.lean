import HigherDimLQGMetric.DGZ.NondegLocalCell

/-! The local selected-cell code is a measurable function of one local coordinate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ} {rGrid : ℝ} (i : nd_DomainIndex d rGrid)

open Classical in
def nd_insertLocal (m : ℕ)
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ)) : nd_Joint d rGrid :=
  (0, Pi.single (i, m) D)

theorem nd_insertLocal_same (m : ℕ)
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ)) :
    (nd_insertLocal i m D).2 (i, m) = D := by
  simp [nd_insertLocal]

theorem nd_measurable_insertLocal (m : ℕ) :
    Measurable (nd_insertLocal i m) := by
  classical
  have hlocal : Measurable (fun D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ) =>
      (nd_insertLocal i m D).2) := by
    apply measurable_pi_iff.mpr
    intro p
    by_cases hp : p = (i, m)
    · subst p
      have heq : (fun D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ) =>
          (nd_insertLocal i m D).2 (i, m)) = id := by
        funext D
        exact nd_insertLocal_same i m D
      rw [heq]
      exact measurable_id
    · have heq : (fun D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ) =>
          (nd_insertLocal i m D).2 p) = fun _ => 0 := by
        funext D
        change (Pi.single (i, m) D :
          ∀ p : nd_DomainIndex d rGrid × ℕ,
            C(nd_domain rGrid p.1 × nd_domain rGrid p.1, ℝ)) p = 0
        exact Pi.single_eq_of_ne
          (M := fun p : nd_DomainIndex d rGrid × ℕ =>
            C(nd_domain rGrid p.1 × nd_domain rGrid p.1, ℝ)) hp D
      rw [heq]
      exact measurable_const
  exact measurable_const.prodMk hlocal

def nd_localSelectedEqC (A : Set (nd_domain rGrid i))
    (_m j : ℕ) (S : Finset (Zd d)) :
    Set C(nd_domain rGrid i × nd_domain rGrid i, ℝ) :=
  {D | ∀ z : Zd d,
    (∃ x : nd_domain rGrid i,
      nd_localPointInf i A D x = 0 ∧
        (x : Rd d) ∈ obox (latPt (nd_gridRadius rGrid j) z)
          (2 * nd_gridRadius rGrid j)) ↔ z ∈ S}

theorem nd_measurableSet_localSelectedEqC
    {A : Set (nd_domain rGrid i)} (hA : IsCompact A)
    (m j : ℕ) (S : Finset (Zd d)) :
    MeasurableSet (nd_localSelectedEqC i A m j S) := by
  have heq : nd_localSelectedEqC i A m j S =
      (nd_insertLocal i m) ⁻¹' nd_localSelectedEq i A m j S := by
    ext D
    simp only [nd_localSelectedEqC, nd_localSelectedEq, Set.mem_ofPred_eq,
      Set.mem_preimage, nd_localSelectedCell, nd_localZeroSet,
      nd_insertLocal_same]
  rw [heq]
  exact (nd_measurableSet_localSelectedEq i hA m j S).preimage
    (nd_measurable_insertLocal i m)

theorem nd_localSelectedEq_eq_preimage
    (A : Set (nd_domain rGrid i)) (m j : ℕ) (S : Finset (Zd d)) :
    nd_localSelectedEq i A m j S =
      (fun s : nd_Joint d rGrid => s.2 (i, m)) ⁻¹'
        nd_localSelectedEqC i A m j S := by
  ext s
  simp only [nd_localSelectedEq, nd_localSelectedEqC, Set.mem_ofPred_eq,
    Set.mem_preimage, nd_localSelectedCell, nd_localZeroSet]

end HigherDimLQGMetric.DGZ
