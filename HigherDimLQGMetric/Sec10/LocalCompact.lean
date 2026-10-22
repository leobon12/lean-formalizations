import HigherDimLQGMetric.Sec10.LocalBounds

/-!
# Compactness criterion for local metric moduli

Countable upper near-diagonal moduli and lower off-diagonal separation conditions give compact
sets of continuous metrics in the local uniform topology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology Metric Filter

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

def s8a_upperModSet (δ : ℕ → ℕ → ℝ) (n m : ℕ) : Set C(Rd d × Rd d, ℝ) :=
  {E | ∀ x ∈ closedBall (0 : Rd d) n, ∀ y ∈ closedBall (0 : Rd d) n,
    ‖x - y‖ ≤ δ n m → E (x, y) ≤ 1 / ((m : ℝ) + 1)}

theorem s8a_upperModSet_isClosed (δ : ℕ → ℕ → ℝ) (n m : ℕ) :
    IsClosed (s8a_upperModSet (d := d) δ n m) := by
  unfold s8a_upperModSet
  simp only [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun y =>
    isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const _) continuous_const

def s8a_localModulusSet (δ : ℕ → ℕ → ℝ) (k : ℕ → ℕ → ℕ) :
    Set C(Rd d × Rd d, ℝ) :=
  metricAlgSet_select (d := d) ∩
    (⋂ n : ℕ, ⋂ m : ℕ, s8a_upperModSet (d := d) δ n m) ∩
    (⋂ n : ℕ, ⋂ m : ℕ, metricSepSet_select (d := d) n m (k n m))

theorem s8a_localModulusSet_isClosed (δ : ℕ → ℕ → ℝ) (k : ℕ → ℕ → ℕ) :
    IsClosed (s8a_localModulusSet (d := d) δ k) := by
  unfold s8a_localModulusSet
  exact ((isClosed_metricAlgSet_select d).inter
    (isClosed_iInter fun n => isClosed_iInter fun m => s8a_upperModSet_isClosed δ n m)).inter
    (isClosed_iInter fun n => isClosed_iInter fun m =>
      isClosed_metricSepSet_select d n m (k n m))

theorem s8a_localModulusSet_metric (δ : ℕ → ℕ → ℝ) (k : ℕ → ℕ → ℕ) :
    s8a_localModulusSet (d := d) δ k ⊆ {E | IsContinuousMetric E} := by
  intro E hE
  exact (isContinuousMetric_iff_select E).2 ⟨hE.1.1, fun n m =>
    ⟨k n m, (mem_iInter.1 (mem_iInter.1 hE.2 n) m)⟩⟩

private theorem s8a_metric_abs_diff {E : C(Rd d × Rd d, ℝ)}
    (hE : IsContinuousMetric E) (p q : Rd d × Rd d) :
    |E p - E q| ≤ E (p.1, q.1) + E (p.2, q.2) := by
  have h1 := hE.triangle p.1 q.1 p.2
  have h2 := hE.triangle q.1 q.2 p.2
  have h3 := hE.triangle q.1 p.1 q.2
  have h4 := hE.triangle p.1 p.2 q.2
  rw [hE.symm q.2 p.2] at h2
  rw [hE.symm q.1 p.1] at h3
  apply abs_le.mpr
  constructor <;> linarith

/-- The modulus set is compact and every member is a genuine continuous metric. -/
theorem s8a_localModulusSet_isCompact (δ : ℕ → ℕ → ℝ) (k : ℕ → ℕ → ℕ)
    (hδ : ∀ n m, 0 < δ n m) :
    IsCompact (s8a_localModulusSet (d := d) δ k) := by
  let S := s8a_localModulusSet (d := d) δ k
  have hSclosed : IsClosed S := s8a_localModulusSet_isClosed δ k
  have hSmetric : S ⊆ {E | IsContinuousMetric E} := s8a_localModulusSet_metric δ k
  have hEqui : Equicontinuous (fun E : S => (E.1 : Rd d × Rd d → ℝ)) := by
    intro p
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖p.1‖ ‖p.2‖)
    have hp1 : p.1 ∈ ball (0 : Rd d) n := by
      rw [mem_ball, dist_zero_right]
      exact (le_max_left _ _).trans_lt hn
    have hp2 : p.2 ∈ ball (0 : Rd d) n := by
      rw [mem_ball, dist_zero_right]
      exact (le_max_right _ _).trans_lt hn
    have hq1 : ∀ᶠ q : Rd d × Rd d in 𝓝 p, q.1 ∈ closedBall (0 : Rd d) n :=
      (continuous_fst.tendsto p).eventually
        (isOpen_ball.mem_nhds hp1) |>.mono fun _ h => ball_subset_closedBall h
    have hq2 : ∀ᶠ q : Rd d × Rd d in 𝓝 p, q.2 ∈ closedBall (0 : Rd d) n :=
      (continuous_snd.tendsto p).eventually
        (isOpen_ball.mem_nhds hp2) |>.mono fun _ h => ball_subset_closedBall h
    filter_upwards [hq1, hq2, Metric.ball_mem_nhds p (hδ n m)] with q hq1' hq2' hqp E
    have hdist : dist p q < δ n m := by simpa only [dist_comm] using (Metric.mem_ball.mp hqp)
    have hc1 : ‖p.1 - q.1‖ ≤ δ n m := by
      rw [← dist_eq_norm]
      have hle : dist p.1 q.1 ≤ dist p q := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      exact (hle.trans_lt hdist).le
    have hc2 : ‖p.2 - q.2‖ ≤ δ n m := by
      rw [← dist_eq_norm]
      have hle : dist p.2 q.2 ≤ dist p q := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      exact (hle.trans_lt hdist).le
    have hfirst : E.1 (p.1, q.1) ≤ 1 / ((m : ℝ) + 1) :=
      (mem_iInter.1 (mem_iInter.1 E.2.1.2 n) m) p.1
        (ball_subset_closedBall hp1) q.1 hq1' hc1
    have hsecond : E.1 (p.2, q.2) ≤ 1 / ((m : ℝ) + 1) :=
      (mem_iInter.1 (mem_iInter.1 E.2.1.2 n) m) p.2
        (ball_subset_closedBall hp2) q.2 hq2' hc2
    rw [Real.dist_eq]
    exact (s8a_metric_abs_diff (hSmetric E.2) p q).trans_lt (by linarith)
  exact s8a_isCompact_of_closed_equicontinuous_metric hSclosed hSmetric hEqui

end HigherDimLQGMetric
