import HigherDimLQGMetric.DGZ.NondegLocalDiag

/-! Continuous local distance-to-compact-set observables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ} {rGrid : ℝ} (i : nd_DomainIndex d rGrid)

def nd_localPointInf (A : Set (nd_domain rGrid i))
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ))
    (x : nd_domain rGrid i) : ℝ :=
  sInf ((fun y => D (x, y)) '' A)

theorem nd_continuous_localPointInf {A : Set (nd_domain rGrid i)}
    (hA : IsCompact A) :
    Continuous (fun p : C(nd_domain rGrid i × nd_domain rGrid i, ℝ) ×
      nd_domain rGrid i => nd_localPointInf i A p.1 p.2) := by
  have hf : Continuous (fun p :
      (C(nd_domain rGrid i × nd_domain rGrid i, ℝ) × nd_domain rGrid i) ×
        nd_domain rGrid i => p.1.1 (p.1.2, p.2)) :=
    continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact hA.continuous_sInf hf

theorem nd_localPointInf_eq_internalSetInf (A : Set (nd_domain rGrid i))
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ))
    (x : nd_domain rGrid i) :
    nd_localPointInf i A D x = nd_internalSetInf {x} A D := by
  unfold nd_localPointInf nd_internalSetInf nd_pairInf
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_prod]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(x, y), ⟨rfl, hy⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hy⟩, hv⟩
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨p.2, hy, hv⟩

theorem nd_localPointInf_nonneg (A : Set (nd_domain rGrid i))
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ))
    (hD : ∀ x y, 0 ≤ D (x, y)) (x : nd_domain rGrid i) :
    0 ≤ nd_localPointInf i A D x :=
  Real.sInf_nonneg (by rintro _ ⟨y, -, rfl⟩; exact hD x y)

theorem nd_localPointInf_le {A : Set (nd_domain rGrid i)} (hA : IsCompact A)
    (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ))
    (x : nd_domain rGrid i) {y : nd_domain rGrid i} (hy : y ∈ A) :
    nd_localPointInf i A D x ≤ D (x, y) := by
  rw [nd_localPointInf_eq_internalSetInf]
  exact nd_pairInf_le (isCompact_singleton.prod hA) D ⟨rfl, hy⟩

theorem nd_exists_localPointInf_eq {A : Set (nd_domain rGrid i)} (hA : IsCompact A)
    (hAne : A.Nonempty) (D : C(nd_domain rGrid i × nd_domain rGrid i, ℝ))
    (x : nd_domain rGrid i) :
    ∃ y ∈ A, nd_localPointInf i A D x = D (x, y) := by
  have hc : Continuous fun y : nd_domain rGrid i => D (x, y) :=
    D.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, hy, hmin⟩ := hA.exists_isMinOn hAne hc.continuousOn
  refine ⟨y, hy, le_antisymm (nd_localPointInf_le i hA D x hy) ?_⟩
  unfold nd_localPointInf
  exact le_csInf (hAne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hmin hz)

def nd_localZeroSet (A : Set (nd_domain rGrid i)) (m : ℕ)
    (s : nd_Joint d rGrid) : Set (nd_domain rGrid i) :=
  {x | nd_localPointInf i A (s.2 (i, m)) x = 0}

theorem nd_isClosed_localZeroSet {A : Set (nd_domain rGrid i)}
    (hA : IsCompact A) (m : ℕ) (s : nd_Joint d rGrid) :
    IsClosed (nd_localZeroSet i A m s) := by
  have hc : Continuous (fun x : nd_domain rGrid i =>
      nd_localPointInf i A (s.2 (i, m)) x) :=
    (nd_continuous_localPointInf i hA).comp
      (continuous_const.prodMk continuous_id)
  exact isClosed_eq hc continuous_const

end HigherDimLQGMetric.DGZ
