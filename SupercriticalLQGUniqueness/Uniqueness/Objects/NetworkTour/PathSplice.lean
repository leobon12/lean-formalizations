import SLUMetricAPI2
import LQGMetric.Metric.LengthSpace
import Mathlib.Topology.Subpath




 





set_option autoImplicit false
noncomputable section
open Set unitInterval
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
open LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

 
theorem pathLength_subpath_of_le {a b : X} (γ : Path a b)
    (s t : unitInterval) (hst : s ≤ t) :
    pathLength (γ.subpath s t) = curveLength γ.extend s t := by
  let φ : ℝ → ℝ := fun u => (1-u)*(s:ℝ)+u*(t:ℝ)
  have hφmem : ∀ u ∈ Icc (0:ℝ) 1, φ u ∈ Icc (0:ℝ) 1 := by
    intro u hu
    simpa only [φ, Icc.coe_convexComb] using
      (Icc.convexComb s t ⟨u, hu⟩).property
  have hcongr : EqOn (γ.subpath s t).extend (γ.extend ∘ φ) (Icc (0:ℝ) 1) := by
    intro u hu
    have hs : (γ.subpath s t).extend u = γ (Icc.convexComb s t ⟨u, hu⟩) := by
      rw [Path.extend_apply _ hu]
      rfl
    rw [hs, Function.comp_apply]
    have hφ := hφmem u hu
    rw [Path.extend_apply γ hφ]
    congr 1
  rw [pathLength, curveLength_congr hcongr]
  rw [curveLength_comp_of_continuousOn_monotoneOn γ.extend zero_le_one
    (by fun_prop) (by
      intro u hu v hv huv
      dsimp [φ]
      have hst' : (s:ℝ) ≤ t := hst
      nlinarith)]
  simp [φ]


 
def loopAt {a b : X} (γ : Path a b) (t : unitInterval) : Path (γ t) (γ t) :=
  ((γ.subpath t 0).trans (γ.subpath 0 1)).trans (γ.subpath 1 t)

theorem loopAt_range {a b : X} (γ : Path a b) (t : unitInterval) :
    range (loopAt γ t) = range γ := by
  have hsub (s u : unitInterval) : range (γ.subpath s u) ⊆ range γ := by
    rw [Path.range_subpath]
    rintro z ⟨v, -, rfl⟩
    exact mem_range_self v
  have hwhole : range (γ.subpath (0:unitInterval) 1) = range γ := by
    rw [Path.range_subpath, Set.uIcc_of_le (zero_le_one : (0:unitInterval) ≤ 1)]
    have heq : Icc (0:unitInterval) 1 = Set.univ := by
      ext x
      simp only [mem_Icc, mem_univ, iff_true]
      exact x.property
    rw [heq, Set.image_univ]
  simp only [loopAt, Path.trans_range]
  exact Subset.antisymm (Set.union_subset (Set.union_subset (hsub t 0) hwhole.subset) (hsub 1 t))
    (by intro z hz; exact Set.mem_union_left _ (Set.mem_union_right _ (hwhole.symm ▸ hz)))

theorem loopAt_length {a b : X} (γ : Path a b) (t : unitInterval) :
    pathLength (loopAt γ t) = 2 * pathLength γ := by
  have hleft : pathLength (γ.subpath t 0) = curveLength γ.extend 0 t := by
    rw [← Path.symm_subpath γ 0 t, pathLength_symm,
      pathLength_subpath_of_le γ 0 t t.property.1]
    rfl
  have hright : pathLength (γ.subpath 1 t) = curveLength γ.extend t 1 := by
    rw [← Path.symm_subpath γ t 1, pathLength_symm,
      pathLength_subpath_of_le γ t 1 (le_one t)]
    rfl
  have hfull : pathLength (γ.subpath 0 1) = pathLength γ := by
    rw [pathLength_subpath_of_le γ 0 1 zero_le_one]
    rfl
  rw [loopAt, pathLength_trans, pathLength_trans, hleft, hright, hfull]
  have hadd := curveLength_add γ.extend t.property.1 t.property.2
  calc
    curveLength γ.extend 0 t + pathLength γ + curveLength γ.extend t 1
        = pathLength γ + (curveLength γ.extend 0 t + curveLength γ.extend t 1) := by ac_rfl
    _ = pathLength γ + curveLength γ.extend 0 1 := by rw [hadd]
    _ = 2 * pathLength γ := by simp only [pathLength, two_mul]


 
def spliceAt {a b c d : X} (α : Path a b) (β : Path c d)
    (t s : unitInterval) (h : α t = β s) : Path (α 0) (α 1) :=
  ((α.subpath 0 t).trans ((loopAt β s).cast h h)).trans (α.subpath t 1)

theorem spliceAt_range {a b c d : X} (α : Path a b) (β : Path c d)
    (t s : unitInterval) (h : α t = β s) :
    range (spliceAt α β t s h) = range α ∪ range β := by
  have hsub (γ : Path a b) (u v : unitInterval) :
      range (γ.subpath u v) ⊆ range γ := by
    rw [Path.range_subpath]
    rintro z ⟨w, -, rfl⟩
    exact mem_range_self w
  have hleft : range (α.subpath 0 t) ⊆ range α := hsub α 0 t
  have hright : range (α.subpath t 1) ⊆ range α := hsub α t 1
  have hcover : range α ⊆ range (α.subpath 0 t) ∪ range (α.subpath t 1) := by
    rintro z ⟨u, rfl⟩
    rcases le_total u t with hut | htu
    · left
      rw [Path.range_subpath,
        Set.uIcc_of_le (show (0:unitInterval) ≤ t from t.property.1)]
      exact ⟨u, ⟨u.property.1, hut⟩, rfl⟩
    · right
      rw [Path.range_subpath,
        Set.uIcc_of_le (show t ≤ (1:unitInterval) from t.property.2)]
      exact ⟨u, ⟨htu, u.property.2⟩, rfl⟩
  have hloop : range ((loopAt β s).cast h h) = range β := by
    rw [← loopAt_range β s]
    exact congrArg range (Path.cast_coe _ h h)
  simp only [spliceAt, Path.trans_range, hloop]
  apply Subset.antisymm
  · intro z hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl (hleft hz)
    · exact Or.inr hz
    · exact Or.inl (hright hz)
  · intro z hz
    rcases hz with hz | hz
    · rcases hcover hz with hz | hz
      · exact Or.inl (Or.inl hz)
      · exact Or.inr hz
    · exact Or.inl (Or.inr hz)

theorem spliceAt_length {a b c d : X} (α : Path a b) (β : Path c d)
    (t s : unitInterval) (h : α t = β s) :
    pathLength (spliceAt α β t s h) = pathLength α + 2 * pathLength β := by
  have hleft : pathLength (α.subpath 0 t) = curveLength α.extend 0 t := by
    rw [pathLength_subpath_of_le α 0 t t.property.1]
    rfl
  have hright : pathLength (α.subpath t 1) = curveLength α.extend t 1 := by
    rw [pathLength_subpath_of_le α t 1 t.property.2]
    rfl
  have hcast : pathLength ((loopAt β s).cast h h) = pathLength (loopAt β s) := by
    simp only [pathLength, Path.extend_cast]
  rw [spliceAt, pathLength_trans, pathLength_trans, hleft, hright, hcast, loopAt_length]
  have hadd := curveLength_add α.extend t.property.1 t.property.2
  calc
    curveLength α.extend 0 t + 2 * pathLength β + curveLength α.extend t 1
        = (curveLength α.extend 0 t + curveLength α.extend t 1) +
            2 * pathLength β := by ac_rfl
    _ = pathLength α + 2 * pathLength β := by rw [hadd]; rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
