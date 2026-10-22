import HigherDimLQGMetric.Determ.GridBox
import LQGMetric.Papers.LM.T1_7V10

/-!
# Joint measurability of translated-cell observations

The internal distance is represented by the countable chain formula. Its only
set-dependent datum is the distance to the complement of the cell. The latter
is the infimum over a dense sequence of points strictly outside its closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal Classical
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The points strictly outside the closed shifted cell. -/
def determOut (ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ) : Set (Rd d) :=
  {y | ∃ i : Fin d,
    y i < ε * ((k i : ℝ) + θ i) ∨
      ε * ((k i : ℝ) + 1 + θ i) < y i}

theorem determ_isOpen_out (ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ) :
    IsOpen (determOut ε θ k) := by
  have heq : determOut ε θ k = ⋃ i : Fin d,
      ({y : Rd d | y i < ε * ((k i : ℝ) + θ i)} ∪
        {y | ε * ((k i : ℝ) + 1 + θ i) < y i}) := by
    ext y
    simp [determOut]
  rw [heq]
  exact isOpen_iUnion fun i =>
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i) continuous_const).union
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i))

theorem determ_out_sub_compl (ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ) :
    determOut ε θ k ⊆ (determCube ε θ k)ᶜ := by
  rintro y ⟨i, hi⟩ hc
  rcases hi with hi | hi
  · exact (not_lt_of_ge hi.le) (hc i).1
  · exact (not_lt_of_ge hi.le) (hc i).2

private def determAxis (i : Fin d) (t : ℝ) : Rd d :=
  WithLp.toLp 2 (Pi.single i t)

private theorem determ_axis_apply (i : Fin d) (t : ℝ) : determAxis i t i = t := by
  simp [determAxis]

private theorem determ_axis_norm (i : Fin d) (t : ℝ) : ‖determAxis i t‖ = |t| := by
  simpa only [determAxis, PiLp.toLp_single, Real.norm_eq_abs] using
    (PiLp.norm_single 2 (fun _ : Fin d => ℝ) i t)

/-- Every point outside the open cell is a limit of points strictly outside. -/
theorem determ_compl_sub_closure_out (ε : ℝ) (θ : Fin d → ℝ) (k : Fin d → ℤ) :
    (determCube ε θ k)ᶜ ⊆ closure (determOut ε θ k) := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro r hr
  have hbad : ∃ i : Fin d,
      y i ≤ ε * ((k i : ℝ) + θ i) ∨
        ε * ((k i : ℝ) + 1 + θ i) ≤ y i := by
    simpa only [determCube, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_and_or, not_lt]
      using hy
  obtain ⟨i, hi | hi⟩ := hbad
  · refine ⟨y + determAxis i (-r / 2), ⟨i, Or.inl ?_⟩, ?_⟩
    · rw [PiLp.add_apply, determ_axis_apply]
      linarith
    · have he : y - (y + determAxis i (-r / 2)) = -determAxis i (-r / 2) := by abel
      rw [dist_eq_norm, he, norm_neg, determ_axis_norm]
      rw [abs_of_nonpos (by linarith : -r / 2 ≤ 0)]
      linarith
  · refine ⟨y + determAxis i (r / 2), ⟨i, Or.inr ?_⟩, ?_⟩
    · rw [PiLp.add_apply, determ_axis_apply]
      linarith
    · have he : y - (y + determAxis i (r / 2)) = -determAxis i (r / 2) := by abel
      rw [dist_eq_norm, he, norm_neg, determ_axis_norm]
      rw [abs_of_nonneg (by linarith : 0 ≤ r / 2)]
      linarith

/-- A countable formula for the distance to the complement of a shifted cell. -/
theorem determ_bdDist_eq (D : ContMetric d) (ε : ℝ) (θ : Fin d → ℝ)
    (k : Fin d → ℤ) (x : Rd d) :
    D.bdDist (determCube ε θ k) x =
      ⨅ n : ℕ, if TopologicalSpace.denseSeq (Rd d) n ∈ determOut ε θ k
        then ENNReal.ofReal (D.1 (x, TopologicalSpace.denseSeq (Rd d) n)) else ⊤ := by
  let q := TopologicalSpace.denseSeq (Rd d)
  rw [ContMetric.bdDist_eq]
  refine le_antisymm (le_iInf fun n => ?_) (le_iInf₂ fun y hy => ?_)
  · split_ifs with hn
    · exact biInf_le (fun y => ENNReal.ofReal (D.1 (x, y)))
        (determ_out_sub_compl ε θ k hn)
    · exact le_top
  · have hg : Continuous fun y : Rd d => ENNReal.ofReal (D.1 (x, y)) :=
      ENNReal.continuous_ofReal.comp
        (D.1.continuous.comp (continuous_const.prodMk continuous_id))
    have hcl : closure (determOut ε θ k) ⊆
        closure (determOut ε θ k ∩ range q) :=
      closure_minimal ((TopologicalSpace.denseRange_denseSeq (Rd d)).open_subset_closure_inter
        (determ_isOpen_out ε θ k)) isClosed_closure
    have hC : IsClosed {y : Rd d | (⨅ n : ℕ,
        if q n ∈ determOut ε θ k then ENNReal.ofReal (D.1 (x, q n)) else ⊤) ≤
          ENNReal.ofReal (D.1 (x, y))} := isClosed_le continuous_const hg
    refine closure_minimal (fun u hu => ?_) hC
      (hcl (determ_compl_sub_closure_out ε θ k hy))
    obtain ⟨hu, n, rfl⟩ := hu
    refine (iInf_le (fun n : ℕ => if q n ∈ determOut ε θ k
      then ENNReal.ofReal (D.1 (x, q n)) else ⊤) n).trans ?_
    simp [hu]

theorem determ_measurableSet_out (ε : ℝ) (k : Fin d → ℤ) (y : Rd d) :
    MeasurableSet {θ : Fin d → ℝ | y ∈ determOut ε θ k} := by
  have heq : {θ : Fin d → ℝ | y ∈ determOut ε θ k} =
      ⋃ i : Fin d,
        ({θ | y i < ε * ((k i : ℝ) + θ i)} ∪
          {θ | ε * ((k i : ℝ) + 1 + θ i) < y i}) := by
    ext θ
    simp [determOut]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_lt measurable_const
      (measurable_const.mul (measurable_const.add (measurable_pi_apply i)))).union
      (measurableSet_lt
        (measurable_const.mul
          ((measurable_const.add measurable_const).add (measurable_pi_apply i)))
        measurable_const)

/-- Distance to a moving cell complement is jointly Borel in shift and metric. -/
theorem determ_measurable_bdDist (ε : ℝ) (k : Fin d → ℤ) (x : Rd d) :
    Measurable fun p : (Fin d → ℝ) × ContMetric d =>
      p.2.bdDist (determCube ε p.1 k) x := by
  simp_rw [determ_bdDist_eq]
  refine Measurable.iInf fun n => Measurable.ite ?_ ?_ measurable_const
  · exact measurable_fst (determ_measurableSet_out ε k _)
  · exact (ENNReal.measurable_ofReal.comp
      ((continuous_eval_const _).measurable.comp measurable_subtype_coe)).comp measurable_snd

theorem determ_measurable_chainStep (ε : ℝ) (k : Fin d → ℤ) (x y : Rd d) :
    Measurable fun p : (Fin d → ℝ) × ContMetric d =>
      p.2.chainStep (determCube ε p.1 k) x y := by
  have he : Measurable fun p : (Fin d → ℝ) × ContMetric d =>
      edist (p.2.pt x) (p.2.pt y) := by
    simp_rw [ContMetric.edist_pt]
    exact (ENNReal.measurable_ofReal.comp
      ((continuous_eval_const _).measurable.comp measurable_subtype_coe)).comp measurable_snd
  unfold ContMetric.chainStep
  exact Measurable.ite (measurableSet_lt he (determ_measurable_bdDist ε k x))
    he measurable_const

theorem determ_measurable_chainVal (ε : ℝ) (k : Fin d → ℤ) (l : List (Rd d)) :
    ∀ x y : Rd d, Measurable fun p : (Fin d → ℝ) × ContMetric d =>
      p.2.chainVal (determCube ε p.1 k) x l y := by
  induction l with
  | nil => exact fun x y => determ_measurable_chainStep ε k x y
  | cons a l ih =>
    intro x y
    simp only [ContMetric.chainVal]
    exact (determ_measurable_chainStep ε k x a).add (ih a y)

theorem determ_measurable_chainInf (ε : ℝ) (k : Fin d → ℤ) (z w : Rd d) :
    Measurable fun p : (Fin d → ℝ) × ContMetric d =>
      p.2.chainInf (determCube ε p.1 k) z w :=
  Measurable.iInf fun _ => determ_measurable_chainVal ε k _ z w

/-- Joint measurability of the vector of encoded cell distances. -/
theorem determ_measurable_gridY (ε : ℝ) (S : Finset (Fin d → ℤ)) :
    Measurable fun p : (Fin d → ℝ) × ContMetric d =>
      fun i : S => determ_enc (determCube ε p.1 i.1) p.2 :=
  Measurable.of_eval fun i => Measurable.of_eval fun n =>
    determ_measurable_chainInf ε i.1
      (TopologicalSpace.denseSeq (Rd d × Rd d) n).1
      (TopologicalSpace.denseSeq (Rd d × Rd d) n).2

end HigherDimLQGMetric
