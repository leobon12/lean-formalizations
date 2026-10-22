import HigherDimLQGMetric.Determ.Grid

/-!
# Geometry of shifted open cubes

Each cell is bounded and open; its boundary lies on the translated grid.
Finite unions therefore satisfy the locality interface's `IsNiceOpen` condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} (ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ)

private def determClosedCube : Set (Rd d) :=
  {x | ∀ i, ε * ((k i : ℝ) + θ i) ≤ x i ∧
    x i ≤ ε * ((k i : ℝ) + 1 + θ i)}

theorem determ_isOpen_cube : IsOpen (determCube ε θ k) := by
  have heq : determCube ε θ k = ⋂ i : Fin d,
      {x : Rd d | ε * ((k i : ℝ) + θ i) < x i ∧
        x i < ε * ((k i : ℝ) + 1 + θ i)} := by
    ext x
    simp [determCube]
  rw [heq]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i) continuous_const)

private theorem determ_closedCube_compact : IsCompact (determClosedCube ε θ k) := by
  let K : Set (Fin d → ℝ) := Set.pi univ fun i =>
    Icc (ε * ((k i : ℝ) + θ i)) (ε * ((k i : ℝ) + 1 + θ i))
  have hK : IsCompact K := isCompact_univ_pi fun i => isCompact_Icc
  have heq : determClosedCube ε θ k = (WithLp.toLp 2) '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i => x i, ?_, ?_⟩
      · exact fun i _ => hx i
      · apply PiLp.ext
        intro i
        rfl
    · rintro ⟨f, hf, rfl⟩
      exact fun i => hf i (mem_univ i)
  rw [heq]
  exact hK.image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

theorem determ_cube_bounded : Bornology.IsBounded (determCube ε θ k) := by
  have hsub : determCube ε θ k ⊆ determClosedCube ε θ k := by
    intro x hx i
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  exact (determ_closedCube_compact ε θ k).isBounded.subset hsub

theorem determ_closure_cube_bounds :
    closure (determCube ε θ k) ⊆ determClosedCube ε θ k :=
  closure_minimal (fun _ hx i => ⟨(hx i).1.le, (hx i).2.le⟩)
    (determ_closedCube_compact ε θ k).isClosed

theorem determ_frontier_cube_subset_grid : frontier (determCube ε θ k) ⊆
    determGrid ε θ := by
  intro x hx
  have hxK := determ_closure_cube_bounds ε θ k (frontier_subset_closure hx)
  have hxnot : x ∉ determCube ε θ k :=
    ((determ_isOpen_cube ε θ k).frontier_eq ▸ hx).2
  by_contra hgrid
  have hne (i : Fin d) (j : ℤ) : x i ≠ ε * ((j : ℝ) + θ i) :=
    fun he => hgrid ⟨i, j, he⟩
  apply hxnot
  intro i
  have hlo := (hxK i).1
  have hhi := (hxK i).2
  refine ⟨lt_of_le_of_ne hlo (hne i (k i)).symm, ?_⟩
  have hnehi : x i ≠ ε * ((k i : ℝ) + 1 + θ i) := by
    convert hne i (k i + 1) using 1
    push_cast
    ring
  exact lt_of_le_of_ne hhi hnehi

/-- An open cell is disjoint from the closure of every distinct cell. -/
theorem determ_cube_disjoint_closure {ε : ℝ} (hε : 0 < ε) (θ : Fin d → ℝ)
    {k l : Fin d → ℤ} (hkl : k ≠ l) :
    determCube ε θ l ⊆ (closure (determCube ε θ k))ᶜ := by
  have hdiff : ∃ i : Fin d, k i ≠ l i := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact hkl (funext hn)
  obtain ⟨i, hi⟩ := hdiff
  intro x hx hxc
  have hk := (determ_closure_cube_bounds ε θ k hxc) i
  have hl := hx i
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hstep : (k i : ℝ) + 1 ≤ (l i : ℝ) := by
      exact_mod_cast (show k i + 1 ≤ l i by omega)
    have hm : ε * ((k i : ℝ) + 1 + θ i) ≤ ε * ((l i : ℝ) + θ i) :=
      mul_le_mul_of_nonneg_left (by linarith) hε.le
    linarith
  · have hstep : (l i : ℝ) + 1 ≤ (k i : ℝ) := by
      exact_mod_cast (show l i + 1 ≤ k i by omega)
    have hm : ε * ((l i : ℝ) + 1 + θ i) ≤ ε * ((k i : ℝ) + θ i) :=
      mul_le_mul_of_nonneg_left (by linarith) hε.le
    linarith

/-- A cell omitted from a finite family misses the closure of its union. -/
theorem determ_cube_sep_finite {ε : ℝ} (hε : 0 < ε) (θ : Fin d → ℝ)
    (T : Finset (Fin d → ℤ)) {j : Fin d → ℤ} (hj : j ∉ T) :
    determCube ε θ j ⊆ (closure (⋃ k ∈ T, determCube ε θ k))ᶜ := by
  intro x hx hxc
  rw [T.closure_biUnion] at hxc
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hxc
  exact (determ_cube_disjoint_closure hε θ (by
    intro hkj
    subst k
    exact hj hk) hx) hxk

/-- A finite union of shifted cubes has null boundary and is bounded. -/
theorem determ_cubes_nice (T : Finset (Fin d → ℤ)) :
    IsNiceOpen (⟨⋃ k ∈ T, determCube ε θ k,
      isOpen_biUnion fun k _ => determ_isOpen_cube ε θ k⟩ : TopologicalSpace.Opens (Rd d)) := by
  constructor
  · exact (Bornology.isBounded_biUnion_finset T).2 fun k _ => determ_cube_bounded ε θ k
  · have hsub : frontier (⋃ k ∈ T, determCube ε θ k) ⊆ determGrid ε θ := by
      intro x hx
      have hxcl : x ∈ closure (⋃ k ∈ T, determCube ε θ k) := frontier_subset_closure hx
      rw [T.closure_biUnion] at hxcl
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hxcl
      have hnot : x ∉ ⋃ k ∈ T, determCube ε θ k := by
        have ho : IsOpen (⋃ k ∈ T, determCube ε θ k) :=
          isOpen_biUnion fun k _ => determ_isOpen_cube ε θ k
        exact (ho.frontier_eq ▸ hx).2
      have hfk : x ∈ frontier (determCube ε θ k) := by
        rw [(determ_isOpen_cube ε θ k).frontier_eq]
        exact ⟨hxk, fun hkx => hnot (mem_iUnion₂.2 ⟨k, hk, hkx⟩)⟩
      exact determ_frontier_cube_subset_grid ε θ k hfk
    exact measure_mono_null hsub (determ_volume_grid_zero ε θ)

end HigherDimLQGMetric
