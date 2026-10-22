import HigherDimLQGMetric.DGZ.NondegPseudo

/-!
# Zero sets of distances to compact spheres

For a continuous candidate pseudometric, distance to a fixed compact set is a
continuous function of the point and the metric. The zero sets used in the
DGZ zero-one argument are therefore closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}
variable {rGrid : ℝ}

/-- The minimum candidate distance from a point to a fixed compact target. -/
def nd_pointSetInf (A : Set (Rd d)) (D : C(Rd d × Rd d, ℝ)) (x : Rd d) : ℝ :=
  sInf ((fun y : Rd d => D (x, y)) '' A)

theorem nd_pointSetInf_eq_setInf (A : Set (Rd d)) (D : C(Rd d × Rd d, ℝ))
    (x : Rd d) : nd_pointSetInf A D x = nd_setInf {x} A D := by
  unfold nd_pointSetInf nd_setInf nd_pairInf
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

theorem nd_continuous_pointSetInf {A : Set (Rd d)} (hA : IsCompact A) :
    Continuous (fun p : C(Rd d × Rd d, ℝ) × Rd d =>
      nd_pointSetInf A p.1 p.2) := by
  have hf : Continuous (fun p : (C(Rd d × Rd d, ℝ) × Rd d) × Rd d =>
      p.1.1 (p.1.2, p.2)) :=
    continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact hA.continuous_sInf hf

/-- Points at zero candidate distance from the sphere of radius `r`. -/
def nd_zeroSet (r : ℝ) (s : nd_Joint d rGrid) : Set (Rd d) :=
  {x | nd_pointSetInf (lsph 0 r) s.1 x = 0}

theorem nd_isClosed_zeroSet (r : ℝ) (s : nd_Joint d rGrid) :
    IsClosed (nd_zeroSet r s) := by
  have hc : Continuous (fun x : Rd d => nd_pointSetInf (lsph 0 r) s.1 x) :=
    (nd_continuous_pointSetInf (tn_isCompact_lsph 0 r)).comp
      (continuous_const.prodMk continuous_id)
  exact isClosed_eq hc continuous_const

theorem nd_pointSetInf_nonneg {A : Set (Rd d)} {D : C(Rd d × Rd d, ℝ)}
    (hD : ∀ x y, 0 ≤ D (x, y)) (x : Rd d) :
    0 ≤ nd_pointSetInf A D x :=
  Real.sInf_nonneg (by rintro _ ⟨y, -, rfl⟩; exact hD x y)

theorem nd_pointSetInf_le {A : Set (Rd d)} (hA : IsCompact A)
    (D : C(Rd d × Rd d, ℝ)) (x : Rd d) {y : Rd d} (hy : y ∈ A) :
    nd_pointSetInf A D x ≤ D (x, y) := by
  rw [nd_pointSetInf_eq_setInf]
  exact nd_pairInf_le (isCompact_singleton.prod hA) D ⟨rfl, hy⟩

theorem nd_sphere_subset_zeroSet (r : ℝ) {s : nd_Joint d rGrid}
    (hs : s ∈ nd_pseudoSet rGrid) : lsph 0 r ⊆ nd_zeroSet r s := by
  intro x hx
  have hle : nd_pointSetInf (lsph 0 r) s.1 x ≤ 0 := by
    simpa only [hs.1 x] using nd_pointSetInf_le (tn_isCompact_lsph 0 r) s.1 x hx
  exact le_antisymm hle (nd_pointSetInf_nonneg hs.2.1 x)

theorem nd_exists_pointSetInf_eq {A : Set (Rd d)} (hA : IsCompact A)
    (hAne : A.Nonempty) (D : C(Rd d × Rd d, ℝ)) (x : Rd d) :
    ∃ y ∈ A, nd_pointSetInf A D x = D (x, y) := by
  have hc : Continuous fun y : Rd d => D (x, y) :=
    D.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, hy, hmin⟩ := hA.exists_isMinOn hAne hc.continuousOn
  refine ⟨y, hy, le_antisymm (nd_pointSetInf_le hA D x hy) ?_⟩
  unfold nd_pointSetInf
  exact le_csInf (hAne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hmin hz)

theorem nd_zeroSet_mem_iff {r : ℝ} (hr : 0 ≤ r) (hd : 0 < d)
    {s : nd_Joint d rGrid} (hs : s ∈ nd_pseudoSet rGrid) (x : Rd d) :
    x ∈ nd_zeroSet r s ↔ ∃ y ∈ lsph 0 r, s.1 (x, y) = 0 := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := nd_exists_pointSetInf_eq (tn_isCompact_lsph 0 r)
      (lsph_nonempty hd 0 hr) s.1 x
    exact ⟨y, hy, by simpa [nd_zeroSet] using heq.symm.trans hx⟩
  · rintro ⟨y, hy, hxy⟩
    have hle := nd_pointSetInf_le (tn_isCompact_lsph 0 r) s.1 x hy
    exact le_antisymm (by simpa only [hxy] using hle)
      (nd_pointSetInf_nonneg hs.2.1 x)

/-- The crossing is positive exactly when the two compact zero sets are disjoint. -/
theorem nd_cross_pos_iff_disjoint_zeroSets {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    {s : nd_Joint d rGrid} (hs : s ∈ nd_pseudoSet rGrid) :
    0 < nd_crossPhi 0 (2 * r) r s.1 ↔
      Disjoint (nd_zeroSet r s) (nd_zeroSet (2 * r) s) := by
  constructor
  · intro hcross
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨y₁, hy₁, hxy₁⟩ :=
      (nd_zeroSet_mem_iff hr.le hd hs x).1 hx₁
    obtain ⟨y₂, hy₂, hxy₂⟩ :=
      (nd_zeroSet_mem_iff (by linarith : 0 ≤ 2 * r) hd hs x).1 hx₂
    have htri := hs.2.2.2 y₁ x y₂
    have hsym := hs.2.2.1 y₁ x
    have hle : nd_crossPhi 0 (2 * r) r s.1 ≤ s.1 (y₁, y₂) :=
      nd_crossPhi_le 0 (2 * r) r s.1 ⟨hy₁, hy₂⟩
    have hnonneg := hs.2.1 y₁ y₂
    rw [hsym, hxy₁, hxy₂] at htri
    linarith
  · intro hdisj
    have hnonneg : 0 ≤ nd_crossPhi 0 (2 * r) r s.1 :=
      nd_pairInf_nonneg s.1 (fun p => hs.2.1 p.1 p.2)
    by_contra hnot
    have hzero : nd_crossPhi 0 (2 * r) r s.1 = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    obtain ⟨p, hp, hmin⟩ := nd_exists_crossPhi_eq hd 0
      (by linarith : 0 ≤ 2 * r) hr.le s.1
    have hp₁ : p.1 ∈ nd_zeroSet r s := nd_sphere_subset_zeroSet r hs hp.1
    have hp₂ : p.1 ∈ nd_zeroSet (2 * r) s :=
      (nd_zeroSet_mem_iff (by linarith : 0 ≤ 2 * r) hd hs p.1).2
        ⟨p.2, hp.2, by simpa [hzero] using hmin.symm⟩
    exact (Set.disjoint_left.1 hdisj) hp₁ hp₂

theorem nd_zeroSet_isBounded_of_event {r : ℝ} {s : nd_Joint d rGrid}
    (hs : s ∈ nd_boundedZeroEvent rGrid r) :
    Bornology.IsBounded (nd_zeroSet r s) := by
  obtain ⟨R, -, hR⟩ := hs
  apply (isBounded_obox (0 : Rd d) R).subset
  intro x hx
  by_contra hxR
  have hpos := hR x hxR
  rw [← nd_pointSetInf_eq_setInf] at hpos
  change nd_pointSetInf (lsph 0 r) s.1 x = 0 at hx
  rw [hx] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

theorem nd_zeroSet_isCompact_of_event {r : ℝ} {s : nd_Joint d rGrid}
    (hs : s ∈ nd_boundedZeroEvent rGrid r) :
    IsCompact (nd_zeroSet r s) :=
  Metric.isCompact_of_isClosed_isBounded (nd_isClosed_zeroSet r s)
    (nd_zeroSet_isBounded_of_event hs)

end HigherDimLQGMetric.DGZ
