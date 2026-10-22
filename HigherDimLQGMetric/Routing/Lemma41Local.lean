import HigherDimLQGMetric.Routing.Lemma41BCF

/-! The checked data retained from routing one lattice edge. -/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

structure Lemma41LocalPiece {X : Type*} [MetricSpace X]
    (pL pR : X) (RegL RegR Box : Set X)
    (E : X → X → ℝ≥0∞) (a₁ c₃ : ℝ) where
  K : Set X
  L : Set X
  R : Set X
  σ : ℝ → X
  graph : IsFiniteRectGraph K
  cut_eq : K \ (σ '' Ioo (0 : ℝ) 1) = L ∪ R
  σK : σ '' Icc (0 : ℝ) 1 ⊆ K
  σ0L : σ 0 ∈ L
  σ1R : σ 1 ∈ R
  Lcompact : IsCompact L
  Lconnected : IsConnected L
  Rcompact : IsCompact R
  Rconnected : IsConnected R
  LRdisjoint : Disjoint L R
  pLmem : pL ∈ L
  pRmem : pR ∈ R
  Lregion : L ⊆ RegL
  Rregion : R ⊆ RegR
  σbox : σ '' Icc (0 : ℝ) 1 ⊆ Box
  σcontinuous : ContinuousOn σ (Icc 0 1)
  σinjective : InjOn σ (Icc 0 1)
  σseparated : a₁ / 2 < dist (σ 0) (σ 1)
  σshort : curveLengthWith E σ 0 1 < ENNReal.ofReal (c₃ * dist (σ 0) (σ 1))

theorem Lemma41LocalPiece.mark_disjoint_left {X : Type*} [MetricSpace X]
    {pL pR : X} {RegL RegR Box : Set X}
    {E : X → X → ℝ≥0∞} {a₁ c₃ : ℝ}
    (P : Lemma41LocalPiece pL pR RegL RegR Box E a₁ c₃) :
    Disjoint (P.σ '' Ioo (0 : ℝ) 1) P.L := by
  apply Set.disjoint_left.mpr
  intro x hxσ hxL
  have hxK : x ∈ P.K := P.σK (image_mono Ioo_subset_Icc_self hxσ)
  have hxnot : x ∉ P.σ '' Ioo (0 : ℝ) 1 :=
    ((P.cut_eq.symm ▸ Or.inl hxL) : x ∈ P.K \ (P.σ '' Ioo (0 : ℝ) 1)).2
  exact hxnot hxσ

theorem Lemma41LocalPiece.mark_disjoint_right {X : Type*} [MetricSpace X]
    {pL pR : X} {RegL RegR Box : Set X}
    {E : X → X → ℝ≥0∞} {a₁ c₃ : ℝ}
    (P : Lemma41LocalPiece pL pR RegL RegR Box E a₁ c₃) :
    Disjoint (P.σ '' Ioo (0 : ℝ) 1) P.R := by
  apply Set.disjoint_left.mpr
  intro x hxσ hxR
  have hxnot : x ∉ P.σ '' Ioo (0 : ℝ) 1 :=
    ((P.cut_eq.symm ▸ Or.inr hxR) : x ∈ P.K \ (P.σ '' Ioo (0 : ℝ) 1)).2
  exact hxnot hxσ

theorem Lemma41LocalPiece.graph_eq {X : Type*} [MetricSpace X]
    {pL pR : X} {RegL RegR Box : Set X}
    {E : X → X → ℝ≥0∞} {a₁ c₃ : ℝ}
    (P : Lemma41LocalPiece pL pR RegL RegR Box E a₁ c₃) :
    P.K = P.L ∪ P.σ '' Icc (0 : ℝ) 1 ∪ P.R := by
  ext x
  constructor
  · intro hx
    by_cases hmark : x ∈ P.σ '' Ioo (0 : ℝ) 1
    · exact Or.inl (Or.inr ((image_mono Ioo_subset_Icc_self) hmark))
    · rcases P.cut_eq ▸ (show x ∈ P.K \ (P.σ '' Ioo (0 : ℝ) 1) from ⟨hx, hmark⟩)
        with hxL | hxR
      · exact Or.inl (Or.inl hxL)
      · exact Or.inr hxR
  · intro hx
    rcases hx with (hxL | hxσ) | hxR
    · have h : x ∈ P.L ∪ P.R := Or.inl hxL
      rw [← P.cut_eq] at h
      exact h.1
    · exact P.σK hxσ
    · have h : x ∈ P.L ∪ P.R := Or.inr hxR
      rw [← P.cut_eq] at h
      exact h.1

theorem Lemma41LocalPiece.left_meets_mark_at_start {X : Type*} [MetricSpace X]
    {pL pR : X} {RegL RegR Box : Set X}
    {E : X → X → ℝ≥0∞} {a₁ c₃ : ℝ}
    (P : Lemma41LocalPiece pL pR RegL RegR Box E a₁ c₃) :
    P.L ∩ (P.σ '' Icc (0 : ℝ) 1) = {P.σ 0} := by
  ext x
  constructor
  · rintro ⟨hxL, ⟨r, hr, heq⟩⟩
    by_cases hr0 : r = 0
    · simpa only [mem_singleton_iff, ← hr0] using heq.symm
    by_cases hr1 : r = 1
    · have hxR : x ∈ P.R := by
        have h : P.σ r ∈ P.R := by simpa only [hr1] using P.σ1R
        exact heq ▸ h
      exact False.elim (Set.disjoint_left.mp P.LRdisjoint hxL hxR)
    · have hri : r ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),
        lt_of_le_of_ne hr.2 hr1⟩
      have hxM : x ∈ P.σ '' Ioo (0 : ℝ) 1 := ⟨r, hri, heq⟩
      exact False.elim (Set.disjoint_left.mp P.mark_disjoint_left hxM hxL)
  · intro hx
    have hxe : x = P.σ 0 := by simpa only [mem_singleton_iff] using hx
    subst x
    exact ⟨P.σ0L, ⟨0, by norm_num, rfl⟩⟩

theorem Lemma41LocalPiece.right_meets_mark_at_end {X : Type*} [MetricSpace X]
    {pL pR : X} {RegL RegR Box : Set X}
    {E : X → X → ℝ≥0∞} {a₁ c₃ : ℝ}
    (P : Lemma41LocalPiece pL pR RegL RegR Box E a₁ c₃) :
    P.R ∩ (P.σ '' Icc (0 : ℝ) 1) = {P.σ 1} := by
  ext x
  constructor
  · rintro ⟨hxR, ⟨r, hr, heq⟩⟩
    by_cases hr1 : r = 1
    · simpa only [mem_singleton_iff, ← hr1] using heq.symm
    by_cases hr0 : r = 0
    · have hxL : x ∈ P.L := by
        have h : P.σ r ∈ P.L := by simpa only [hr0] using P.σ0L
        exact heq ▸ h
      exact False.elim (Set.disjoint_right.mp P.LRdisjoint hxR hxL)
    · have hri : r ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),
        lt_of_le_of_ne hr.2 hr1⟩
      have hxM : x ∈ P.σ '' Ioo (0 : ℝ) 1 := ⟨r, hri, heq⟩
      exact False.elim (Set.disjoint_left.mp P.mark_disjoint_right hxM hxR)
  · intro hx
    have hxe : x = P.σ 1 := by simpa only [mem_singleton_iff] using hx
    subst x
    exact ⟨P.σ1R, ⟨1, by norm_num, rfl⟩⟩

end HigherDimLQGMetric
