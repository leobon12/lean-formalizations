import HigherDimLQGMetric.Limits.JointInternalDet
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Bases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-! Almost-sure relative compactness of a random sequence gives tightness of its marginal laws. -/

noncomputable section
open MeasureTheory Set Topology Metric Filter TopologicalSpace
open scoped ENNReal

namespace HigherDimLQGMetric

variable {E Ω : Type*} [MetricSpace E] [SeparableSpace E] [Nonempty E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : ℕ → Ω → E) (hY : ∀ n, Measurable (Y n))

private def coverEv (m N : ℕ) : Set Ω :=
  {ω | ∀ n, ∃ i < N, dist (Y n ω) (TopologicalSpace.denseSeq E i) < (1 : ℝ) / (m + 1)}

private theorem coverEv_meas (hY : ∀ n, Measurable (Y n)) (m N : ℕ) : MeasurableSet (coverEv Y m N) := by
  have heq : coverEv Y m N = ⋂ n, ⋃ i ∈ Finset.range N,
      {ω | dist (Y n ω) (TopologicalSpace.denseSeq E i) < (1 : ℝ) / (m + 1)} := by
    ext ω
    simp [coverEv, Finset.mem_range]
  rw [heq]
  exact MeasurableSet.iInter fun n => Finset.measurableSet_biUnion _ fun i _ =>
    measurableSet_lt ((continuous_id.dist continuous_const).measurable.comp (hY n)) measurable_const

private theorem coverEv_mono (m : ℕ) : Monotone (coverEv Y m) := by
  intro N M hNM ω hω n
  obtain ⟨i, hi, hd⟩ := hω n
  exact ⟨i, hi.trans_le hNM, hd⟩

private theorem coverEv_exists_of_compact (m : ℕ) (ω : Ω)
    (hcompact : IsCompact (closure (range fun n => Y n ω))) :
    ∃ N, ω ∈ coverEv Y m N := by
  let δ : ℝ := (1 : ℝ) / (m + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcover : closure (range fun n => Y n ω) ⊆ ⋃ i : ℕ, ball (TopologicalSpace.denseSeq E i) δ := by
    intro x _
    obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq E).exists_dist_lt x hδ
    exact mem_iUnion.mpr ⟨i, by simpa only [mem_ball, dist_comm] using hi⟩
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover (fun i => ball (TopologicalSpace.denseSeq E i) δ)
    (fun i => isOpen_ball) hcover
  obtain ⟨N, hN⟩ := s.exists_nat_subset_range
  refine ⟨N, fun n => ?_⟩
  have hyn : Y n ω ∈ closure (range fun n => Y n ω) := subset_closure ⟨n, rfl⟩
  obtain ⟨i, hi, hball⟩ := mem_iUnion₂.mp (hs hyn)
  exact ⟨i, Finset.mem_range.mp (hN hi), by simpa only [mem_ball, dist_comm] using hball⟩

private theorem exists_cover_bound
    (hY : ∀ n, Measurable (Y n))
    (hcompact : ∀ᵐ ω ∂P, IsCompact (closure (range fun n => Y n ω)))
    (m : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ N, P (coverEv Y m N)ᶜ < η := by
  have hnull : P (⋂ N, (coverEv Y m N)ᶜ) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcompact] with ω hc hω
    obtain ⟨N, hN⟩ := coverEv_exists_of_compact Y m ω hc
    exact (mem_iInter.mp hω N) hN
  have hlim : Tendsto (fun N => P (coverEv Y m N)ᶜ) atTop (𝓝 0) := by
    have ht := tendsto_measure_iInter_atTop
      (fun N => (coverEv_meas Y hY m N).compl.nullMeasurableSet)
      (fun a b hab => compl_subset_compl.mpr (coverEv_mono Y m hab))
      ⟨0, measure_ne_top P _⟩
    simpa only [Function.comp_def, hnull] using ht
  exact (hlim.eventually (gt_mem_nhds hη)).exists

private def compactCover (N : ℕ → ℕ) : Set E :=
  ⋂ m, ⋃ i ∈ Finset.range (N m), closedBall (TopologicalSpace.denseSeq E i) ((1 : ℝ) / (m + 1))

private theorem compactCover_isCompact [CompleteSpace E] (N : ℕ → ℕ) :
    IsCompact (compactCover (E := E) N) := by
  classical
  have hclosed : IsClosed (compactCover (E := E) N) := by
    unfold compactCover
    exact isClosed_iInter fun m => isClosed_biUnion_finset fun i _ => isClosed_closedBall
  have htot : TotallyBounded (compactCover (E := E) N) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine ⟨(Finset.range (N m)).image (TopologicalSpace.denseSeq E), Finset.finite_toSet _, ?_⟩
    intro x hx
    have hx' := mem_iInter.mp hx m
    obtain ⟨i, hi, hball⟩ := mem_iUnion₂.mp hx'
    have hle : (1 : ℝ) / (m + 1) < ε := hm
    exact mem_iUnion₂.mpr ⟨TopologicalSpace.denseSeq E i,
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩),
      mem_ball.mpr ((mem_closedBall.mp hball).trans_lt hle)⟩
  exact htot.isCompact_of_isClosed hclosed

theorem l6c_random_precompact_tight [CompleteSpace E]
    (hY : ∀ n, Measurable (Y n))
    (hcompact : ∀ᵐ ω ∂P, IsCompact (closure (range fun n => Y n ω))) :
    IsTightMeasureSet {μ : Measure E | ∃ n, μ = P.map (Y n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  choose N hN using fun m => exists_cover_bound P Y hY hcompact m (hδ m)
  let K := compactCover (E := E) N
  refine ⟨K, compactCover_isCompact N, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hsub : Y n ⁻¹' Kᶜ ⊆ ⋃ m, (coverEv Y m (N m))ᶜ := by
    intro ω hω
    change Y n ω ∉ K at hω
    simp only [K, compactCover, mem_iInter, not_forall] at hω
    obtain ⟨m, hm⟩ := hω
    apply mem_iUnion.mpr
    refine ⟨m, ?_⟩
    intro hc
    obtain ⟨i, hi, hd⟩ := hc n
    apply hm
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, mem_closedBall.mpr hd.le⟩
  rw [Measure.map_apply (hY n) (compactCover_isCompact N).isClosed.isOpen_compl.measurableSet]
  calc P (Y n ⁻¹' Kᶜ) ≤ P (⋃ m, (coverEv Y m (N m))ᶜ) := measure_mono hsub
    _ ≤ ∑' m, P (coverEv Y m (N m))ᶜ := measure_iUnion_le _
    _ ≤ ∑' m, δ m := ENNReal.tsum_le_tsum fun m => (hN m).le
    _ ≤ ε := hsum.le

end HigherDimLQGMetric
