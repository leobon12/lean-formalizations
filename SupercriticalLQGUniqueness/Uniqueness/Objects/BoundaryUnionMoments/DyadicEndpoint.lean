import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.EndpointControl




 





set_option autoImplicit false
noncomputable section

open Set Metric Filter

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

private theorem dist_smul_smul (w : ℂ) (s t : ℝ) :
    dist (s • w) (t • w) = |s - t| * ‖w‖ := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]

private theorem dyadicQ_pos (k : ℕ) : 0 < Objects.BoundaryUnionDyadic.dyadicQ k := by
  dsimp [Objects.BoundaryUnionDyadic.dyadicQ]
  positivity

private theorem dyadicQ_le_half (k : ℕ) : Objects.BoundaryUnionDyadic.dyadicQ k ≤ 1 / 2 := by
  change (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2
  rw [pow_succ]
  have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k)
  nlinarith

theorem dyadic_outer_le_dist_zero (w : ℂ) (i : ℕ × Bool) :
    Objects.BoundaryUnionDyadic.dyadicOuter w i ≤ dist (0 : ℂ) (Objects.BoundaryUnionDyadic.dyadicCenter w i) := by
  rcases i with ⟨k, b⟩
  cases b with
  | false =>
      change Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ ≤ dist 0 (Objects.BoundaryUnionDyadic.dyadicQ k • w)
      rw [dist_zero_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (dyadicQ_pos k).le]
  | true =>
      change Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ ≤ dist 0 ((1 - Objects.BoundaryUnionDyadic.dyadicQ k) • w)
      rw [dist_zero_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [dyadicQ_le_half k] : 0 ≤ 1 - Objects.BoundaryUnionDyadic.dyadicQ k)]
      have h := mul_nonneg
        (by linarith [dyadicQ_le_half k] : 0 ≤ 1 - 2 * Objects.BoundaryUnionDyadic.dyadicQ k)
        (norm_nonneg w)
      nlinarith only [h]

theorem dyadic_outer_le_dist_right (w : ℂ) (i : ℕ × Bool) :
    Objects.BoundaryUnionDyadic.dyadicOuter w i ≤ dist w (Objects.BoundaryUnionDyadic.dyadicCenter w i) := by
  rcases i with ⟨k, b⟩
  cases b with
  | false =>
      change Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ ≤ dist w (Objects.BoundaryUnionDyadic.dyadicQ k • w)
      have hdist : dist w (Objects.BoundaryUnionDyadic.dyadicQ k • w) =
          (1 - Objects.BoundaryUnionDyadic.dyadicQ k) * ‖w‖ := by
        simpa only [one_smul, abs_of_nonneg
          (by linarith [dyadicQ_le_half k] : 0 ≤ 1 - Objects.BoundaryUnionDyadic.dyadicQ k)]
          using dist_smul_smul w 1 (Objects.BoundaryUnionDyadic.dyadicQ k)
      rw [hdist]
      have h := mul_nonneg
        (by linarith [dyadicQ_le_half k] : 0 ≤ 1 - 2 * Objects.BoundaryUnionDyadic.dyadicQ k)
        (norm_nonneg w)
      nlinarith only [h]
  | true =>
      change Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ ≤ dist w ((1 - Objects.BoundaryUnionDyadic.dyadicQ k) • w)
      have hdist : dist w ((1 - Objects.BoundaryUnionDyadic.dyadicQ k) • w) =
          Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ := by
        calc
          _ = |1 - (1 - Objects.BoundaryUnionDyadic.dyadicQ k)| * ‖w‖ := by
            simpa only [one_smul] using dist_smul_smul w 1 (1 - Objects.BoundaryUnionDyadic.dyadicQ k)
          _ = Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ := by
            rw [show 1 - (1 - Objects.BoundaryUnionDyadic.dyadicQ k) = Objects.BoundaryUnionDyadic.dyadicQ k by ring,
              abs_of_nonneg (dyadicQ_pos k).le]
      rw [hdist]

theorem dyadic_center_outer_le_radius (w : ℂ) (i : ℕ × Bool) :
    dist (Objects.BoundaryUnionDyadic.dyadicCenter w i) 0 + Objects.BoundaryUnionDyadic.dyadicOuter w i ≤ ‖w‖ := by
  rcases i with ⟨k, b⟩
  cases b with
  | false =>
      change dist (Objects.BoundaryUnionDyadic.dyadicQ k • w) 0 + Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ ≤ ‖w‖
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (dyadicQ_pos k).le]
      have h := mul_nonneg
        (by linarith [dyadicQ_le_half k] : 0 ≤ 1 - 2 * Objects.BoundaryUnionDyadic.dyadicQ k)
        (norm_nonneg w)
      nlinarith only [h]
  | true =>
      change dist ((1 - Objects.BoundaryUnionDyadic.dyadicQ k) • w) 0 +
        Objects.BoundaryUnionDyadic.dyadicQ k * ‖w‖ ≤ ‖w‖
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [dyadicQ_le_half k] : 0 ≤ 1 - Objects.BoundaryUnionDyadic.dyadicQ k)]
      ring_nf
      exact le_rfl

 
theorem dyadic_trace_subset_closedBall (w : ℂ) (K : ℕ × Bool → Set ℂ)
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (i : ℕ × Bool) : K i ⊆ closedBall 0 ‖w‖ := by
  intro z hz
  have hrad := dyadic_center_outer_le_radius w i
  have htri := dist_triangle z (Objects.BoundaryUnionDyadic.dyadicCenter w i) 0
  have hzdist := (hann i hz).2
  change dist z 0 ≤ ‖w‖
  linarith only [htri, hzdist, hrad]

theorem dyadic_eventually_avoids_component
    (w e : ℂ) (K : ℕ × Bool → Set ℂ)
    (hw : w ≠ 0)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (he : ∀ i, Objects.BoundaryUnionDyadic.dyadicOuter w i ≤ dist e (Objects.BoundaryUnionDyadic.dyadicCenter w i))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (nhds e)) (i : ℕ × Bool) :
    ∀ᶠ n in atTop, u n ∉ connectedComponentIn (K i)ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w i) := by
  have hr : 0 < Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 := by
    dsimp [Objects.BoundaryUnionDyadic.dyadicOuter, Objects.BoundaryUnionDyadic.dyadicQ]
    exact div_pos (mul_pos (pow_pos (by norm_num) _) (norm_pos_iff.mpr hw))
      (by norm_num)
  have hrR : Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 < Objects.BoundaryUnionDyadic.dyadicOuter w i := by
    linarith only [hr]
  exact eventually_not_mem_annular_component hr hrR (hcompact i) (hann i)
    (hsep i) (he i) hu

 

theorem selected_left_index_tendsto_atTop
    (w : ℂ) (hw : w ≠ 0) (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (u : ℕ → ℂ) (hu : Tendsto u atTop (nhds 0)) (i : ℕ → ℕ × Bool)
    (hsel : ∀ n, u n ∈ connectedComponentIn (K (i n))ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w (i n))) :
    Tendsto (fun n => (i n).1) atTop atTop := by
  exact selected_index_tendsto_atTop
    (fun j => connectedComponentIn (K j)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w j))
    u i hsel (fun k b => dyadic_eventually_avoids_component w 0 K hw
      hcompact hann hsep (dyadic_outer_le_dist_zero w) hu (k, b))

 
theorem selected_right_index_tendsto_atTop
    (w : ℂ) (hw : w ≠ 0) (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (u : ℕ → ℂ) (hu : Tendsto u atTop (nhds w)) (i : ℕ → ℕ × Bool)
    (hsel : ∀ n, u n ∈ connectedComponentIn (K (i n))ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w (i n))) :
    Tendsto (fun n => (i n).1) atTop atTop := by
  exact selected_index_tendsto_atTop
    (fun j => connectedComponentIn (K j)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w j))
    u i hsel (fun k b => dyadic_eventually_avoids_component w w K hw
      hcompact hann hsep (dyadic_outer_le_dist_right w) hu (k, b))

 



theorem selected_trace_tendsto_endpoint
    (w e : ℂ) (hw : w ≠ 0) (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (he : ∀ i, Objects.BoundaryUnionDyadic.dyadicOuter w i ≤ dist e (Objects.BoundaryUnionDyadic.dyadicCenter w i))
    (u y : ℕ → ℂ) (i : ℕ → ℕ × Bool)
    (hu : Tendsto u atTop (nhds e))
    (hsel : ∀ n, u n ∈ connectedComponentIn (K (i n))ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w (i n)))
    (hy : ∀ n, y n ∈ K (i n)) :
    Tendsto y atTop (nhds e) := by
  have hi : Tendsto (fun n => (i n).1) atTop atTop :=
    selected_index_tendsto_atTop
      (fun j => connectedComponentIn (K j)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w j))
      u i hsel (fun k b => dyadic_eventually_avoids_component w e K hw
        hcompact hann hsep he hu (k, b))
  have hq : Tendsto Objects.BoundaryUnionDyadic.dyadicQ atTop (nhds 0) := by
    have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    change Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) atTop (nhds 0)
    simpa only [Function.comp_def] using hp.comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun n => Objects.BoundaryUnionDyadic.dyadicOuter w (i n)) atTop (nhds 0) := by
    change Tendsto (fun n => Objects.BoundaryUnionDyadic.dyadicQ (i n).1 * ‖w‖) atTop (nhds 0)
    simpa only [Function.comp_def, zero_mul] using (hq.comp hi).mul_const ‖w‖
  have hdist (n : ℕ) :
      dist (y n) (u n) < 2 * Objects.BoundaryUnionDyadic.dyadicOuter w (i n) := by
    let j := i n
    have hr : 0 < Objects.BoundaryUnionDyadic.dyadicOuter w j / 2 := by
      dsimp [Objects.BoundaryUnionDyadic.dyadicOuter, Objects.BoundaryUnionDyadic.dyadicQ]
      exact div_pos (mul_pos (pow_pos (by norm_num) _) (norm_pos_iff.mpr hw))
        (by norm_num)
    have hrR : Objects.BoundaryUnionDyadic.dyadicOuter w j / 2 < Objects.BoundaryUnionDyadic.dyadicOuter w j := by
      linarith only [hr]
    have huc : dist (u n) (Objects.BoundaryUnionDyadic.dyadicCenter w j) < Objects.BoundaryUnionDyadic.dyadicOuter w j :=
      (Toolkit.PlanarSeparation.annular_component_bounds hr hrR (hcompact j) (hann j) (hsep j)).2
        (hsel n)
    have hyc : dist (y n) (Objects.BoundaryUnionDyadic.dyadicCenter w j) < Objects.BoundaryUnionDyadic.dyadicOuter w j :=
      (hann j (hy n)).2
    have htri := dist_triangle (y n) (Objects.BoundaryUnionDyadic.dyadicCenter w j) (u n)
    rw [dist_comm (Objects.BoundaryUnionDyadic.dyadicCenter w j) (u n)] at htri
    dsimp [j] at *
    linarith only [htri, huc, hyc]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨Nu, hNu⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (by linarith)
  obtain ⟨NR, hNR⟩ := Metric.tendsto_atTop.mp hR (ε / 4) (by linarith)
  refine ⟨max Nu NR, ?_⟩
  intro n hn
  have huε := hNu n (le_trans (le_max_left Nu NR) hn)
  have hRε := hNR n (le_trans (le_max_right Nu NR) hn)
  have hRnonneg : 0 ≤ Objects.BoundaryUnionDyadic.dyadicOuter w (i n) := by
    dsimp [Objects.BoundaryUnionDyadic.dyadicOuter]
    exact mul_nonneg (dyadicQ_pos _).le (norm_nonneg w)
  have hRsmall : Objects.BoundaryUnionDyadic.dyadicOuter w (i n) < ε / 4 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hRnonneg] using hRε
  have htri := dist_triangle (y n) (u n) e
  linarith only [hdist n, huε, hRsmall, htri]

theorem selected_left_trace_tendsto
    (w : ℂ) (hw : w ≠ 0) (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (u y : ℕ → ℂ) (i : ℕ → ℕ × Bool)
    (hu : Tendsto u atTop (nhds 0))
    (hsel : ∀ n, u n ∈ connectedComponentIn (K (i n))ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w (i n)))
    (hy : ∀ n, y n ∈ K (i n)) :
    Tendsto y atTop (nhds 0) :=
  selected_trace_tendsto_endpoint w 0 hw K hcompact hann hsep
    (dyadic_outer_le_dist_zero w) u y i hu hsel hy

theorem selected_right_trace_tendsto
    (w : ℂ) (hw : w ≠ 0) (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (u y : ℕ → ℂ) (i : ℕ → ℕ × Bool)
    (hu : Tendsto u atTop (nhds w))
    (hsel : ∀ n, u n ∈ connectedComponentIn (K (i n))ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w (i n)))
    (hy : ∀ n, y n ∈ K (i n)) :
    Tendsto y atTop (nhds w) :=
  selected_trace_tendsto_endpoint w w hw K hcompact hann hsep
    (dyadic_outer_le_dist_right w) u y i hu hsel hy


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
