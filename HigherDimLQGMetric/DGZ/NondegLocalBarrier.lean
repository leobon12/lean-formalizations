import HigherDimLQGMetric.DGZ.NondegCollarLevel

/-! Positive distance from a compact collar to the local zero set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid : ℝ} (i : nd_DomainIndex d rGrid)

theorem nd_exists_internalSetInf_eq {A B : Set (nd_domain rGrid i)}
    (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ)) :
    ∃ p ∈ A ×ˢ B, nd_internalSetInf A B D = D p := by
  have hK : IsCompact (A ×ˢ B) := hA.prod hB
  have hKne : (A ×ˢ B).Nonempty := hAne.prod hBne
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne D.continuous.continuousOn
  refine ⟨p, hp, le_antisymm (nd_pairInf_le hK D hp) ?_⟩
  exact le_csInf (hKne.image _) (by rintro _ ⟨q, hq, rfl⟩; exact hmin hq)

theorem nd_internalSetInf_pos_of_disjoint_localZero
    {A B : Set (nd_domain rGrid i)}
    (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ))
    (hD : ∀ x y, 0 ≤ D (x, y))
    (hdisj : Disjoint A {x | nd_localPointInf i B D x = 0}) :
    0 < nd_internalSetInf A B D := by
  obtain ⟨p, hp, hpmin⟩ := nd_exists_internalSetInf_eq i hA hB hAne hBne D
  rw [hpmin]
  have hnonneg : 0 ≤ D p := hD p.1 p.2
  rcases lt_or_eq_of_le hnonneg with hpos | hzero
  · exact hpos
  · have hle := nd_localPointInf_le i hB D p.1 hp.2
    rw [← hzero] at hle
    have hpzero : nd_localPointInf i B D p.1 = 0 :=
      le_antisymm hle (nd_localPointInf_nonneg i B D hD p.1)
    exact False.elim ((Set.disjoint_left.mp hdisj) hp.1 hpzero)

end HigherDimLQGMetric.DGZ
