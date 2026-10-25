import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.MovingBall




 


set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.MovingEndpoints

 
theorem upperSemicontinuous_of_seq {β γ : Type*}
    [TopologicalSpace β] [FirstCountableTopology β]
    [CompleteLinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    {f : β → γ}
    (h : ∀ (u : ℕ → β) (x : β), Tendsto u atTop (nhds x) →
      limsup (fun n => f (u n)) atTop ≤ f x) :
    UpperSemicontinuous f := by
  intro x t ht
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨u, hu, hfu⟩ := exists_seq_forall_of_frequently hne
  have h2 : t ≤ limsup (fun n => f (u n)) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun n => not_lt.mp (hfu n))
  exact (not_le_of_gt ht) (h2.trans (h u x hu))

 
def movingOpenSetDist (D : LSCMetric) (s : ℝ) (z w : ℂ) : ENNReal :=
  ⨅ q ∈ Metric.ball z s ×ˢ Metric.ball w s, D q

 

theorem movingOpenSetDist_joint_usc (s : ℝ) :
    UpperSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) =>
      movingOpenSetDist p.1 s p.2.1 p.2.2) := by
  apply upperSemicontinuous_of_seq
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hz : Tendsto (fun n => (G n).2.1) atTop (nhds p.2.1) := by
    have hc : Continuous (fun q : LSCMetric × (ℂ × ℂ) => q.2.1) := by fun_prop
    exact (hc.tendsto p).comp hG
  have hw : Tendsto (fun n => (G n).2.2) atTop (nhds p.2.2) := by
    have hc : Continuous (fun q : LSCMetric × (ℂ × ℂ) => q.2.2) := by fun_prop
    exact (hc.tendsto p).comp hG
  refine le_iInf fun q => le_iInf fun hq => ?_
  obtain ⟨ρ, hρ, hval⟩ := (LSCMetric.tendsto_iff.mp hm).2 q
  have hρz : Tendsto (fun n => (ρ n).1) atTop (nhds q.1) :=
    (continuous_fst.tendsto q).comp hρ
  have hρw : Tendsto (fun n => (ρ n).2) atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp hρ
  have hez : ∀ᶠ n in atTop, (ρ n).1 ∈ Metric.ball (G n).2.1 s := by
    have hd := hρz.dist hz
    exact hd.eventually (Iio_mem_nhds (Metric.mem_ball.mp hq.1))
  have hew : ∀ᶠ n in atTop, (ρ n).2 ∈ Metric.ball (G n).2.2 s := by
    have hd := hρw.dist hw
    exact hd.eventually (Iio_mem_nhds (Metric.mem_ball.mp hq.2))
  have hbound : ∀ᶠ n in atTop,
      movingOpenSetDist (G n).1 s (G n).2.1 (G n).2.2 ≤ (G n).1 (ρ n) := by
    filter_upwards [hez, hew] with n hnz hnw
    exact iInf₂_le (ρ n) ⟨hnz, hnw⟩
  calc
    limsup (fun n => movingOpenSetDist (G n).1 s (G n).2.1 (G n).2.2) atTop
        ≤ limsup (fun n => (G n).1 (ρ n)) atTop := Filter.limsup_le_limsup hbound
    _ = p.1 q := hval.limsup_eq

 
theorem movingOpenSetDist_joint_borel (s : ℝ) :
    @Measurable (LSCMetric × (ℂ × ℂ)) ENNReal (borel _) inferInstance
      (fun p => movingOpenSetDist p.1 s p.2.1 p.2.2) := by
  letI : MeasurableSpace (LSCMetric × (ℂ × ℂ)) := borel _
  letI : OpensMeasurableSpace (LSCMetric × (ℂ × ℂ)) := ⟨le_rfl⟩
  exact (movingOpenSetDist_joint_usc s).measurable


end Uniqueness.Toolkit.MovingEndpoints
end SupercriticalLQGUniqueness
