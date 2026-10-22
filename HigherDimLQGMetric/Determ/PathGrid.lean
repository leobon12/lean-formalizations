import HigherDimLQGMetric.Determ.Resample
import LQGMetric.Papers.LM.T1_7G2

/-!
# Length of a path split across translated cubes

The length measure and its Stieltjes construction are reused from the 2D
library because those definitions are polymorphic in the metric space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- A near-minimal path for an internal distance, parametrized on `[0,1]`. -/
theorem determ_near_path (D : ContMetric d) {V : Set (Rd d)} {z w : Rd d}
    (hfin : D.internal V z w ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : ℝ → Rd d, Continuous P ∧ P 0 = z ∧ P 1 = w ∧
      MapsTo P (Icc 0 1) V ∧
      D.len P 0 1 ≤ D.internal V z w + ENNReal.ofReal δ := by
  have hlt : D.internal V z w < D.internal V z w + ENNReal.ofReal δ :=
    ENNReal.lt_add_right hfin (by simpa using hδ)
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1
    (show internalEDist (D.pt '' V) (D.pt z) (D.pt w) <
      D.internal V z w + ENNReal.ofReal δ from hlt)
  refine ⟨D.unpt ∘ γ.1.extend, D.continuous_unpt.comp γ.1.continuous_extend,
    ?_, ?_, ?_, hγ.le⟩
  · show D.unpt (γ.1.extend 0) = z
    rw [Path.extend_zero]
    rfl
  · show D.unpt (γ.1.extend 1) = w
    rw [Path.extend_one]
    rfl
  · intro t ht
    have h2 : D.pt (D.unpt (γ.1.extend t)) ∈ D.pt '' V := by
      rw [Path.extend_apply _ ht]
      exact γ.2 ⟨t, ht⟩
    exact D.mem_image_pt.1 h2

theorem determ_sfinite_lenMeas (D : ContMetric d) (P : ℝ → Rd d) (a b : ℝ) :
    SFinite (LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b) := by
  unfold LQGMetric.LM.t17LenMeas
  split_ifs <;> infer_instance

/-- Measure decomposition when the grid-time set is null. -/
theorem determ_sum_pieces {μ : Measure ℝ} {T : Set ℝ} (hT : MeasurableSet T)
    {P : ℝ → Rd d} (hP : Measurable P) {G : Set (Rd d)}
    {ι : Type*} (s : Finset ι) (S : ι → Set (Rd d))
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : (s : Set ι).PairwiseDisjoint S)
    (hcover : ∀ t ∈ T, P t ∉ G → ∃ i ∈ s, P t ∈ S i)
    (hnull : μ (T ∩ P ⁻¹' G) = 0) :
    μ T = ∑ i ∈ s, μ (T ∩ P ⁻¹' S i) := by
  have hU : ∑ i ∈ s, μ (T ∩ P ⁻¹' S i) =
      μ (⋃ i ∈ s, T ∩ P ⁻¹' S i) :=
    (measure_biUnion_finset (fun i hi j hj hij =>
      Disjoint.mono inter_subset_right inter_subset_right
        ((hdisj hi hj hij).preimage P))
      fun i _ => hT.inter (hP (hS i))).symm
  rw [hU]
  refine le_antisymm ?_ (measure_mono (iUnion₂_subset fun i _ => inter_subset_left))
  calc μ T ≤ μ ((T ∩ P ⁻¹' G) ∪ ⋃ i ∈ s, T ∩ P ⁻¹' S i) := measure_mono fun t ht => by
        by_cases hG : P t ∈ G
        · exact Or.inl ⟨ht, hG⟩
        · obtain ⟨i, hi, hti⟩ := hcover t ht hG
          exact Or.inr (mem_iUnion₂.2 ⟨i, hi, ht, hti⟩)
    _ ≤ μ (T ∩ P ⁻¹' G) + μ (⋃ i ∈ s, T ∩ P ⁻¹' S i) := measure_union_le _ _
    _ = μ (⋃ i ∈ s, T ∩ P ⁻¹' S i) := by rw [hnull, zero_add]

/-- For a unit-cube translation, the fixed finite box covers the off-grid
part of every path inside `B̄_R(0)`. -/
theorem determ_sum_cubes (μ : Measure ℝ) {ε R : ℝ} (hε : 0 < ε)
    {θ : Fin d → ℝ} (hθ : θ ∈ determUnitShift d)
    {P : ℝ → Rd d} (hP : Continuous P) {a b : ℝ}
    (hPR : MapsTo P (Icc a b) (Metric.closedBall 0 R))
    (hnull : μ (Icc a b ∩ P ⁻¹' determGrid ε θ) = 0) :
    μ (Icc a b) = ∑ k ∈ determFixedBox ε R,
      μ (Icc a b ∩ P ⁻¹' determCube ε θ k) := by
  apply determ_sum_pieces measurableSet_Icc hP.measurable
    (determFixedBox ε R) (determCube ε θ)
    (fun k => (determ_isOpen_cube ε θ k).measurableSet)
  · intro k _ l _ hkl
    refine Set.disjoint_left.2 fun x hxk hxl => ?_
    exact (determ_cube_disjoint_closure hε θ hkl hxl) (subset_closure hxk)
  · intro t ht hg
    refine ⟨determIdx ε θ (P t), ?_, determ_mem_cube_of_not_grid hε θ hg⟩
    exact determ_idx_mem_fixedBox hε hθ (by simpa using hPR ht)
  · exact hnull

/-- Length measure of the part of a curve inside one cell, as a real number. -/
def determPiece (D : ContMetric d) (P : ℝ → Rd d)
    (a b ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ) : ℝ :=
  (LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b
    (Icc a b ∩ P ⁻¹' determCube ε θ k)).toReal

end HigherDimLQGMetric
