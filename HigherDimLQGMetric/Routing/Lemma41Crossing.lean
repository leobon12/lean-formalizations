import HigherDimLQGMetric.Routing.Lemma41FiniteUnion
import Mathlib.Topology.Subpath

/-! A path crossing a closed two-piece cover meets the overlap. -/

set_option autoImplicit false

open Set Topology

namespace HigherDimLQGMetric

theorem lemma41_path_hits_overlap {X : Type*} [TopologicalSpace X]
    {x y : X} (P : Path x y) (A B K : Set X)
    (hA : IsClosed A) (hB : IsClosed B) (hK : K ⊆ A ∪ B)
    (hPK : Set.range P ⊆ K) (hx : x ∈ A) (hy : y ∈ B) :
    ∃ r : unitInterval, P r ∈ A ∩ B := by
  by_contra h
  have h : ∀ r : unitInterval, P r ∉ A ∩ B := by
    simpa only [not_exists] using h
  have hcover : Set.range P ⊆ Aᶜ ∪ Bᶜ := by
    rintro z ⟨r, rfl⟩
    by_cases ha : P r ∈ A
    · exact Or.inr (fun hb => h r ⟨ha, hb⟩)
    · exact Or.inl ha
  have hleft : (Set.range P ∩ Bᶜ).Nonempty := by
    refine ⟨x, ⟨0, P.source⟩, ?_⟩
    intro hxb
    exact h 0 (by simpa only [P.source] using (show x ∈ A ∩ B from ⟨hx, hxb⟩))
  have hright : (Set.range P ∩ Aᶜ).Nonempty := by
    refine ⟨y, ⟨1, P.target⟩, ?_⟩
    intro hya
    exact h 1 (by simpa only [P.target] using (show y ∈ A ∩ B from ⟨hya, hy⟩))
  obtain ⟨z, hz, hzA, hzB⟩ :=
    (isPreconnected_range P.continuous) Bᶜ Aᶜ hB.isOpen_compl hA.isOpen_compl
      (by simpa only [union_comm] using hcover) hleft hright
  rcases hK (hPK hz) with hzA' | hzB'
  · exact hzB hzA'
  · exact hzA hzB'

/-- A path in a finite closed cover whose pieces do not overlap on the path stays in one piece. -/
theorem lemma41_path_in_one_closed_piece {X V : Type*} [TopologicalSpace X] [Fintype V]
    {x y : X} (P : Path x y) (D : V → Set X)
    (hclosed : ∀ v, IsClosed (D v))
    (hcover : Set.range P ⊆ ⋃ v, D v)
    (hdisj : ∀ v w, v ≠ w → Disjoint (Set.range P ∩ D v) (D w)) :
    ∃ v, Set.range P ⊆ D v := by
  classical
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover ⟨0, P.source⟩)
  let B : Set X := ⋃ w ∈ {w : V | w ≠ v}, D w
  have hBc : IsClosed B := (Set.toFinite _).isClosed_biUnion fun w _ => hclosed w
  have hcover' : Set.range P ⊆ D v ∪ B := by
    intro z hz
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (hcover hz)
    by_cases hwv : w = v
    · exact Or.inl (hwv ▸ hw)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, hwv, hw⟩)
  by_cases hsub : Set.range P ⊆ D v
  · exact ⟨v, hsub⟩
  · have hys : ∃ z ∈ Set.range P, z ∈ B := by
      obtain ⟨z, hz, hzv⟩ := Set.not_subset.mp hsub
      exact ⟨z, hz, (hcover' hz).resolve_left hzv⟩
    obtain ⟨z, ⟨r, hr⟩, hzB⟩ := hys
    let P' : Path x z := (P.subpath 0 r).cast P.source.symm hr.symm
    have hP' : Set.range P' ⊆ Set.range P := by
      change Set.range (P.subpath 0 r) ⊆ Set.range P
      rw [Path.range_subpath]
      exact Set.image_subset_range _ _
    have hxv : x ∈ D v := by simpa only [P.source] using hv
    have hzB' : z ∈ B := hzB
    obtain ⟨q, hq⟩ :=
      lemma41_path_hits_overlap P' (D v) B (D v ∪ B) (hclosed v) hBc
        (Subset.rfl) (hP'.trans hcover') hxv hzB'
    obtain ⟨w, hwv, hqw⟩ := Set.mem_iUnion₂.mp hq.2
    exact ((Set.disjoint_left.mp (hdisj v w (Ne.symm hwv)))
      ⟨hP' ⟨q, rfl⟩, hq.1⟩ hqw).elim

end HigherDimLQGMetric
