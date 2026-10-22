import HigherDimLQGMetric.Determ.SeqCI
import LQGMetric.Papers.LM.T1_7G1

/-!
# Randomly shifted cubical grids in Euclidean space

For every fixed measurable path, its time spent on the grid is zero for
almost every translation.  The shift is represented in the product space
`Fin d → ℝ`, whose volume is directly the product of one-dimensional volumes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- Coordinate hyperplanes of the translated mesh. -/
def determGrid {d : ℕ} (ε : ℝ) (θ : Fin d → ℝ) : Set (Rd d) :=
  {x | ∃ i : Fin d, ∃ k : ℤ, x i = ε * ((k : ℝ) + θ i)}

/-- Open cells of the translated mesh. -/
def determCube {d : ℕ} (ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ) : Set (Rd d) :=
  {x | ∀ i, ε * ((k i : ℝ) + θ i) < x i ∧
    x i < ε * ((k i : ℝ) + 1 + θ i)}

/-- A coordinate hyperplane in Euclidean space has zero volume. -/
theorem determ_volume_coord_eq_zero {d : ℕ} (i : Fin d) (a : ℝ) :
    (volume : Measure (Rd d)) {x | x i = a} = 0 := by
  have hs : MeasurableSet {x : Rd d | x i = a} := measurableSet_eq_fun
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable measurable_const
  rw [← (PiLp.volume_preserving_toLp (Fin d)).map_eq]
  rw [Measure.map_apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable hs]
  change (volume : Measure (Fin d → ℝ)) {f | f i = a} = 0
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i a

/-- The fixed translated grid is volume-null in space. -/
theorem determ_volume_grid_zero {d : ℕ} (ε : ℝ) (θ : Fin d → ℝ) :
    (volume : Measure (Rd d)) (determGrid ε θ) = 0 := by
  have heq : determGrid ε θ = ⋃ i : Fin d, ⋃ k : ℤ,
      {x : Rd d | x i = ε * ((k : ℝ) + θ i)} := by
    ext x
    simp [determGrid]
  rw [heq]
  exact measure_iUnion_null fun i => measure_iUnion_null fun k =>
    determ_volume_coord_eq_zero i _

/-- A fixed spatial point lies on the randomly shifted grid with probability zero. -/
theorem determ_volume_grid_shift {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    (volume : Measure (Fin d → ℝ)) {θ | x ∈ determGrid ε θ} = 0 := by
  have hsub : {θ : Fin d → ℝ | x ∈ determGrid ε θ} ⊆
      ⋃ i : Fin d, ⋃ k : ℤ, {θ | θ i = x i / ε - k} := by
    rintro θ ⟨i, k, hk⟩
    refine mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨k, ?_⟩⟩
    change θ i = x i / ε - k
    have he : ε ≠ 0 := ne_of_gt hε
    apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff he).2
    nlinarith
  have hz (i : Fin d) (k : ℤ) :
      (volume : Measure (Fin d → ℝ)) {θ | θ i = x i / ε - k} = 0 := by
    rw [show {θ : Fin d → ℝ | θ i = x i / ε - k} =
      (Function.eval i) ⁻¹' ({x i / ε - k} : Set ℝ) from rfl, volume_pi]
    exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i _
  exact measure_mono_null hsub
    (measure_iUnion_null fun i => measure_iUnion_null fun k => hz i k)

/-- The relation `path time × shift lies on the grid` is measurable. -/
theorem determ_measurableSet_grid {d : ℕ} (ε : ℝ) {P : ℝ → Rd d} (hP : Measurable P) :
    MeasurableSet {p : ℝ × (Fin d → ℝ) | P p.1 ∈ determGrid ε p.2} := by
  have heq : {p : ℝ × (Fin d → ℝ) | P p.1 ∈ determGrid ε p.2} =
      ⋃ i : Fin d, ⋃ k : ℤ,
        {p | (P p.1) i = ε * ((k : ℝ) + p.2 i)} := by
    ext p
    simp [determGrid]
  rw [heq]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k => ?_
  exact measurableSet_eq_fun
    ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp
      (hP.comp measurable_fst))
    (measurable_const.mul (measurable_const.add
      ((measurable_pi_apply i).comp measurable_snd)))

/-- A measurable path spends zero time on a randomly shifted grid, with respect
to any sigma-finite or s-finite length measure on its parameter interval. -/
theorem determ_grid_null {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {P : ℝ → Rd d} (hP : Measurable P) (μ : Measure ℝ) [SFinite μ] :
    ∀ᵐ θ ∂(volume : Measure (Fin d → ℝ)), μ {t | P t ∈ determGrid ε θ} = 0 := by
  have hE := determ_measurableSet_grid ε hP
  have h1 : (μ.prod (volume : Measure (Fin d → ℝ)))
      {p | P p.1 ∈ determGrid ε p.2} = 0 :=
    (Measure.measure_prod_null hE).2 (Eventually.of_forall fun t =>
      determ_volume_grid_shift hε (P t))
  have hE' : MeasurableSet
      (Prod.swap ⁻¹' {p : ℝ × (Fin d → ℝ) | P p.1 ∈ determGrid ε p.2}) :=
    measurable_swap hE
  have h2 : ((volume : Measure (Fin d → ℝ)).prod μ)
      (Prod.swap ⁻¹' {p : ℝ × (Fin d → ℝ) | P p.1 ∈ determGrid ε p.2}) = 0 := by
    rw [← Measure.map_apply measurable_swap hE, Measure.prod_swap, h1]
  have h3 := (Measure.measure_prod_null hE').1 h2
  filter_upwards [h3] with θ hθ
  exact hθ

end HigherDimLQGMetric
