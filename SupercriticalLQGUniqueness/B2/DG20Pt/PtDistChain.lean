import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAroundBridge

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_chain_edges {ξ : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    (v : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (N : ℕ) (hv : v 0 ∈ U)
    (hstep : ∀ j < N, lfppDOn ξ f U (v j) (v (j + 1)) ≤ a j) :
    lfppDOn ξ f U (v 0) (v N) ≤ ∑ j ∈ Finset.range N, a j := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact (lfppDOn_le (isPiecewiseC1Path_const (v 0))
      (fun _ _ => hv)).trans (by rw [lfppLen_const])
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (lfppDOn_triangle _ (v N) _).trans
      (add_le_add (ih fun j hj => hstep j (by omega)) (hstep N (by omega)))

 

theorem pt_dist_selected_crossing_chain {ξ : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    (N : ℕ) (x : ℕ → ℂ) (p : ℕ → ℝ → ℂ) (L : ℕ → ℝ≥0∞)
    (hcross : ∀ j ≤ N,
      AdmPath U (sphere (x j) (((2 : ℝ)⁻¹ ^ j) / 4))
        (sphere (x j) (16 * ((2 : ℝ)⁻¹ ^ j))) (p j))
    (hnear : ∀ j < N,
      dist (x (j + 1)) (x j) ≤ 3 * ((2 : ℝ)⁻¹ ^ (j + 1)) / 4)
    (hloop : ∀ j < N,
      Inputs.HasAroundLoop ξ f (x (j + 1)) ((2 : ℝ)⁻¹ ^ (j + 1))
        (by positivity) (L j))
    (hball : ∀ j < N,
      ball (x (j + 1)) (8 * ((2 : ℝ)⁻¹ ^ (j + 1))) ⊆ U) :
    lfppDOn ξ f U (p 0 0) (p N 0) ≤
      ∑ j ∈ Finset.range N,
        (lfppLen ξ f (p (j + 1)) + L j + lfppLen ξ f (p j)) := by
  have hfirst : p 0 0 ∈ U := by
    obtain ⟨a, _, _, _, hp, hU⟩ := hcross 0 (Nat.zero_le N)
    exact hU 0 (by norm_num)
  apply pt_dist_chain_edges (fun j => p j 0)
    (fun j => lfppLen ξ f (p (j + 1)) + L j + lfppLen ξ f (p j)) N hfirst
  intro j hj
  let r : ℝ := (2 : ℝ)⁻¹ ^ (j + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : ((2 : ℝ)⁻¹) ^ j = 2 * r := by
    dsimp [r]
    rw [pow_succ]
    ring
  obtain ⟨a, ha, b, hb, hq, hqU⟩ := hcross j (by omega)
  obtain ⟨c, hc, d, hd, hp, hpU⟩ := hcross (j + 1) (by omega)
  have hp0 : dist (p (j + 1) 0) (x (j + 1)) ≤ r / 4 := by
    rw [hp.source]
    exact (mem_sphere.mp hc).le
  have hp1 : 16 * r ≤ dist (p (j + 1) 1) (x (j + 1)) := by
    rw [hp.target]
    exact (mem_sphere.mp hd).ge
  have hq0 : dist (p j 0) (x j) ≤ r / 2 := by
    rw [hq.source]
    simpa only [hscale, show 2 * r / 4 = r / 2 by ring] using
      (mem_sphere.mp ha).le
  have hq1 : 32 * r ≤ dist (p j 1) (x j) := by
    rw [hq.target]
    simpa only [hscale, show 16 * (2 * r) = 32 * r by ring] using
      (mem_sphere.mp hb).ge
  have hp' : IsPiecewiseC1Path (p (j + 1)) (p (j + 1) 0) (p (j + 1) 1) := by
    rw [hp.source, hp.target]
    exact hp
  have hq' : IsPiecewiseC1Path (p j) (p j 0) (p j 1) := by
    rw [hq.source, hq.target]
    exact hq
  have h := lfppDOn_le_adjacent_of_hasAroundLoop hr (hnear j hj)
    (hloop j hj) (hball j hj) (p (j + 1)) (p j)
    hp' hq' hpU hqU hp0 hp1 hq0 hq1
  rw [lfppDOn_comm] at h
  exact h

end SupercriticalLQGUniqueness.B2.DG20Pt
