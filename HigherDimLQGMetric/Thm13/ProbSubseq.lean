import HigherDimLQGMetric.Thm13.Coupling
import LQGMetric.Papers.DFGPS.T12P2D

/-! A local-uniform convergence-in-probability sequence has one a.s.
compact-open convergent deterministic subsequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- MA5 A21(1): a common a.s. subsequence for all compact ball squares. -/
theorem l8_exists_subseq_ae_of_prob {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P)
    (hprob : TendstoInProbLU P (fun n ω => X n ω) atTop
      (fun ω => Y ω)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => X (ns n) ω) atTop (𝓝 (Y ω)) := by
  let K : ℕ → Set (Rd d × Rd d) := fun m =>
    closedBall (0 : Rd d) ((m : ℝ) + 1) ×ˢ
      closedBall (0 : Rd d) ((m : ℝ) + 1)
  letI (m : ℕ) : CompactSpace (K m) :=
    isCompact_iff_compactSpace.mp
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  let Z : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n => (hX n).mk _
  have hZe (n : ℕ) : X n =ᵐ[P] Z n := (hX n).ae_eq_mk
  let f : ∀ m, ℕ → Ω → C(K m, ℝ) := fun m n ω => (Z n ω).restrict (K m)
  let g : ∀ m, Ω → C(K m, ℝ) := fun m ω => (Y ω).restrict (K m)
  have hTm : ∀ m, TendstoInMeasure P (f m) atTop (g m) := by
    intro m e he
    rcases eq_or_ne e ⊤ with rfl | htop
    · simp only [top_le_iff, edist_ne_top, ofPred_false, measure_empty,
        tendsto_const_nhds]
    have hδ : 0 < e.toReal := ENNReal.toReal_pos he.ne' htop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hprob ((m : ℝ) + 1) (by positivity) e.toReal hδ)
      (fun _ => zero_le) fun n => measure_mono_ae ?_
    filter_upwards [hZe n] with ω hω hmem
    change e ≤ edist (f m n ω) (g m ω) at hmem
    rw [ENNReal.ofReal_toReal htop]
    refine hmem.trans ?_
    rw [ContinuousMap.edist_eq_iSup]
    apply iSup_le
    intro p
    have hp : p.1 ∈ closedBall (0 : Rd d) ((m : ℝ) + 1) ×ˢ
        closedBall (0 : Rd d) ((m : ℝ) + 1) := p.2
    have hle := le_iSup₂
      (f := fun q (_ : q ∈ K m) => edist (X n ω q) (Y ω q)) p.1 hp
    simpa only [f, g, ContinuousMap.restrict_apply, hω] using hle
  obtain ⟨ns, hns, hae⟩ :=
    LQGMetric.DFGPS.T12.exists_subseq_ae_tendsto_all
      (μ := P) (ι := ℕ) hTm
  have hc : ∀ᵐ ω ∂P, ∀ n, X n ω = Z n ω :=
    ae_all_iff.mpr hZe
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hc] with ω hω hωZ
  apply l8_tendsto_contMap_of_balls
  intro R hR
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hsub : closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R ⊆ K m :=
    prod_mono (closedBall_subset_closedBall (by linarith))
      (closedBall_subset_closedBall (by linarith))
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have ht := (tendsto_iff_dist_tendsto_zero.mp (hω m)).eventually
    (gt_mem_nhds hη)
  filter_upwards [ht] with n hn p hp
  have hle := ContinuousMap.dist_apply_le_dist
    (f := f m (ns n) ω) (g := g m ω) ⟨p, hsub hp⟩
  change dist (Z (ns n) ω p) (Y ω p) ≤
    dist (f m (ns n) ω) (g m ω) at hle
  rw [← hωZ (ns n)] at hle
  rw [dist_comm]
  exact hle.trans_lt hn

end HigherDimLQGMetric
