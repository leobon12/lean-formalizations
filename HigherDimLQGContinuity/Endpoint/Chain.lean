import HigherDimLQGContinuity.Endpoint.Grid

/-!
# The Euclidean endpoint (packet E3), part 5: the good event controls a block (deterministic)

Blueprint Part C `c:lem-end-good` (`supd_profile_le_of_not_endBad`), the last paragraph of `c:thm-endpoint`, and
Convention `c:conv`(iii). Everything here is deterministic, for one continuous path `F : ℝ → C(ℝ^d × ℝ^d, ℝ)`.

* `endpt_chain`: if every base node is within `ε` of the Euclidean profile, every level-`0` node within `ε/8` of its
  base parent and every level-`(j+1)` node within `ε 2^{-j-6}` of its level-`j` parent (all in `supd_R` of the
  logarithmic profiles), then every node of level `j` is within `ε(9/8 + (1 - 2^{-j})/32) ≤ 2ε` of the Euclidean
  profile.
* `supd_profile_le_of_not_endBad`: with nonnegativity at the nodes, levels tending to infinity and continuity of `F` on
  the block, `|F ξ (x, y) - |x - y|| ≤ 4(1 + 2R) ε` for every `ξ` in the block and `x, y ∈ B̄_R`.
* `endpt_tendsto_of_blocks`: block bounds `≤ K_R ε_k` for all large `k` and every radius give
  `F ξ → euclidDistC d` in `C(ℝ^d × ℝ^d, ℝ)` as `ξ → 0` within any set of positive parameters
  (`ContinuousMap.tendsto_iff_tendstoLocallyUniformly`);
* `endpt_rate_of_blocks`: the same block bounds give `supd_R(F ξ, eu) ≤ K √ξ` on an interval `(0, ξ_R]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- **The chain** (`c:lem-end-good`, first part). -/
theorem endpt_chain {F : ℝ → C(Rd d × Rd d, ℝ)} {R ε : ℝ} {k qb : ℕ} {q : ℕ → ℕ} (hε : 0 ≤ ε)
    (hbase : ∀ m ≤ 2 ^ qb, supDistLU d R (logProfile (F (endNode k qb m)))
      (logProfile (euclidDistC d)) ≤ ENNReal.ofReal ε)
    (hbridge : ∀ m ≤ 2 ^ q 0, supDistLU d R (logProfile (F (endNode k qb (endPar (q 0) qb m))))
      (logProfile (F (endNode k (q 0) m))) ≤ ENNReal.ofReal (ε / 8))
    (hfine : ∀ j, ∀ m ≤ 2 ^ q (j + 1),
      supDistLU d R (logProfile (F (endNode k (q j) (endPar (q (j + 1)) (q j) m))))
        (logProfile (F (endNode k (q (j + 1)) m))) ≤ ENNReal.ofReal (ε * (1 / 2) ^ (j + 6))) :
    ∀ j, ∀ m ≤ 2 ^ q j, supDistLU d R (logProfile (F (endNode k (q j) m)))
      (logProfile (euclidDistC d)) ≤ ENNReal.ofReal (ε * (9 / 8 + 1 / 32 * (1 - (1 / 2) ^ j))) := by
  intro j
  induction j with
  | zero =>
    intro m hm
    have h1 := hbase _ (endPar_le hm)
    have h2 := hbridge m hm
    calc supDistLU d R (logProfile (F (endNode k (q 0) m))) (logProfile (euclidDistC d))
        ≤ supDistLU d R (logProfile (F (endNode k (q 0) m)))
            (logProfile (F (endNode k qb (endPar (q 0) qb m)))) +
          supDistLU d R (logProfile (F (endNode k qb (endPar (q 0) qb m))))
            (logProfile (euclidDistC d)) := endpt_supDistLU_triangle
      _ ≤ ENNReal.ofReal (ε / 8) + ENNReal.ofReal ε := by
          rw [endpt_supDistLU_comm]
          exact add_le_add h2 h1
      _ = ENNReal.ofReal (ε * (9 / 8 + 1 / 32 * (1 - (1 / 2) ^ 0))) := by
          rw [← ENNReal.ofReal_add (by positivity) hε]
          congr 1
          ring
  | succ j ih =>
    intro m hm
    have h1 := ih _ (endPar_le hm)
    have h2 := hfine j m hm
    calc supDistLU d R (logProfile (F (endNode k (q (j + 1)) m))) (logProfile (euclidDistC d))
        ≤ supDistLU d R (logProfile (F (endNode k (q (j + 1)) m)))
            (logProfile (F (endNode k (q j) (endPar (q (j + 1)) (q j) m)))) +
          supDistLU d R (logProfile (F (endNode k (q j) (endPar (q (j + 1)) (q j) m))))
            (logProfile (euclidDistC d)) := endpt_supDistLU_triangle
      _ ≤ ENNReal.ofReal (ε * (1 / 2) ^ (j + 6)) +
            ENNReal.ofReal (ε * (9 / 8 + 1 / 32 * (1 - (1 / 2) ^ j))) := by
          rw [endpt_supDistLU_comm]
          exact add_le_add h2 h1
      _ = ENNReal.ofReal (ε * (9 / 8 + 1 / 32 * (1 - (1 / 2) ^ (j + 1)))) := by
          have h3 : (0 : ℝ) ≤ 9 / 8 + 1 / 32 * (1 - (1 / 2) ^ j) := by
            have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            linarith
          rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hε h3)]
          congr 1
          rw [pow_add, pow_succ]
          ring

/-- **The good event controls a whole block** (`c:lem-end-good`): under the hypotheses of `endpt_chain`, with
nonnegativity at the nodes, levels `q j ≥ j` and continuity of `F` on the block, every parameter of the block is
within `4(1 + 2R) ε` of the Euclidean distance on `B̄_R × B̄_R`. -/
theorem supd_profile_le_of_not_endBad {F : ℝ → C(Rd d × Rd d, ℝ)} {R ε : ℝ} {k qb : ℕ} {q : ℕ → ℕ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hq : ∀ j, j ≤ q j)
    (hcont : ContinuousOn F (Icc (endA k) (2 * endA k)))
    (hnn : ∀ j, ∀ m ≤ 2 ^ q j, ∀ p, 0 ≤ F (endNode k (q j) m) p)
    (hbase : ∀ m ≤ 2 ^ qb, supDistLU d R (logProfile (F (endNode k qb m)))
      (logProfile (euclidDistC d)) ≤ ENNReal.ofReal ε)
    (hbridge : ∀ m ≤ 2 ^ q 0, supDistLU d R (logProfile (F (endNode k qb (endPar (q 0) qb m))))
      (logProfile (F (endNode k (q 0) m))) ≤ ENNReal.ofReal (ε / 8))
    (hfine : ∀ j, ∀ m ≤ 2 ^ q (j + 1),
      supDistLU d R (logProfile (F (endNode k (q j) (endPar (q (j + 1)) (q j) m))))
        (logProfile (F (endNode k (q (j + 1)) m))) ≤ ENNReal.ofReal (ε * (1 / 2) ^ (j + 6))) :
    ∀ ξ ∈ Icc (endA k) (2 * endA k), ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
      |F ξ p - euclidDistC d p| ≤ 4 * (1 + 2 * R) * ε := by
  have hchain := endpt_chain hε hbase hbridge hfine
  have hgrid : ∀ j, ∀ m ≤ 2 ^ q j, ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
      |F (endNode k (q j) m) p - euclidDistC d p| ≤ 4 * (1 + 2 * R) * ε := by
    intro j m hm p hp
    have hj : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
    have hj1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h1 : supDistLU d R (logProfile (F (endNode k (q j) m))) (logProfile (euclidDistC d)) ≤
        ENNReal.ofReal (2 * ε) := by
      refine (hchain j m hm).trans (ENNReal.ofReal_le_ofReal ?_)
      nlinarith
    have h2 := endpt_abs_sub_euclid_le (by positivity) (by linarith) h1 hp (hnn j m hm p)
    linarith
  intro ξ hξ p hp
  choose m hm hclose using fun j => exists_endNode_near hξ (q j)
  set t : ℕ → ℝ := fun j => endNode k (q j) (m j) with htdef
  have hA0 : Tendsto (fun j : ℕ => endA (k + j)) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat k).2 tendsto_endA
    simpa only [add_comm] using this
  have ht0 : Tendsto t atTop (𝓝 ξ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hA0
    rw [Real.norm_eq_abs]
    exact (hclose j).trans (endA_anti (by have := hq j; omega))
  have ht : Tendsto t atTop (𝓝[Icc (endA k) (2 * endA k)] ξ) :=
    tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall fun j => endNode_mem (hm j)⟩
  have hF : Tendsto (fun j => F (t j) p) atTop (𝓝 (F ξ p)) :=
    ((continuous_eval_const p).tendsto (F ξ)).comp ((hcont ξ hξ).tendsto.comp ht)
  have hab : Tendsto (fun j => |F (t j) p - euclidDistC d p|) atTop (𝓝 |F ξ p - euclidDistC d p|) :=
    (hF.sub_const _).abs
  exact le_of_tendsto' hab fun j => hgrid j (m j) (hm j) p hp

/-- A point of `ball x 1` lies in `B̄_R × B̄_R` when `‖x‖ + 1 ≤ R`. -/
theorem endpt_mem_closedBall_prod {x y : Rd d × Rd d} {R : ℝ} (hR : ‖x‖ + 1 ≤ R) (hy : y ∈ ball x 1) :
    y ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R := by
  have hy' : ‖y‖ ≤ R := by
    rw [mem_ball, dist_eq_norm] at hy
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R := by linarith
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    exact (norm_fst_le y).trans hy'
  · rw [mem_closedBall, dist_zero_right]
    exact (norm_snd_le y).trans hy'

/-- **From block bounds to convergence in `C(ℝ^d × ℝ^d, ℝ)`** (last paragraph of `c:thm-endpoint`). -/
theorem endpt_tendsto_of_blocks {F : ℝ → C(Rd d × Rd d, ℝ)} {S : Set ℝ} (hS : ∀ ξ ∈ S, 0 < ξ)
    (h : ∀ R : ℕ, 1 ≤ R → ∃ K : ℝ, ∃ k₁ : ℕ, ∀ k ≥ k₁, ∀ ξ ∈ Icc (endA k) (2 * endA k),
      ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        |F ξ p - euclidDistC d p| ≤ K * endEps k) :
    Tendsto F (𝓝[S] 0) (𝓝 (euclidDistC d)) := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨R, hR⟩ := exists_nat_ge (‖x‖ + 1)
  have hR1 : 1 ≤ R := by
    have h1 : (1 : ℝ) ≤ R := by linarith [norm_nonneg x]
    exact_mod_cast h1
  obtain ⟨K, k₁, hK⟩ := h R hR1
  have hev : ∀ᶠ k in atTop, (|K| + 1) * endEps k < ε := by
    have h0 : Tendsto (fun k => (|K| + 1) * endEps k) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_endEps.const_mul (|K| + 1)
    exact h0.eventually (gt_mem_nhds hε)
  obtain ⟨k₂, hk₂, hk₂'⟩ := (hev.and (eventually_ge_atTop k₁)).exists
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨endA k₂, endA_pos k₂, fun ξ hξd hξS y hy => ?_⟩
  have hξ0 : 0 < ξ := hS ξ hξS
  rw [Real.dist_eq, sub_zero, abs_of_pos hξ0] at hξd
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hξ0 (hξd.le.trans (endA_le_one _))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hk : k₂ ≤ n + 1 := by
    have h1 : (1 / 2 : ℝ) ^ (n + 1) < (1 / 2) ^ k₂ := hn1.trans hξd
    have h2 := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).1 h1
    omega
  have hblock : ξ ∈ Icc (endA (n + 1)) (2 * endA (n + 1)) := by
    refine ⟨hn1.le, ?_⟩
    rw [endA_succ]
    have : endA n = (1 / 2) ^ n := rfl
    linarith
  have hy' := endpt_mem_closedBall_prod hR hy
  have hb := hK (n + 1) (by omega) ξ hblock y hy'
  have he1 : endEps (n + 1) ≤ endEps k₂ := endEps_anti hk
  have he0 : 0 ≤ endEps (n + 1) := (endEps_pos _).le
  rw [dist_comm, Real.dist_eq]
  calc |F ξ y - euclidDistC d y| ≤ K * endEps (n + 1) := hb
    _ ≤ (|K| + 1) * endEps (n + 1) := by
        gcongr
        linarith [le_abs_self K]
    _ ≤ (|K| + 1) * endEps k₂ := by gcongr
    _ < ε := hk₂

/-- **From block bounds to a rate**: block bounds `≤ K ε_k` for all `k ≥ k₁` give
`supd_R(F ξ, eu) ≤ K √ξ` for every `ξ ∈ (0, a_{k₁}]` (`ξ ∈ [a_k, 2a_k]` with `k ≥ k₁` and `ε_k = √(a_k) ≤ √ξ`). -/
theorem endpt_rate_of_blocks {F : ℝ → C(Rd d × Rd d, ℝ)} {R K : ℝ} (hK : 0 ≤ K) {k₁ : ℕ}
    (h : ∀ k ≥ k₁, ∀ ξ ∈ Icc (endA k) (2 * endA k),
      ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R,
        |F ξ p - euclidDistC d p| ≤ K * endEps k) :
    ∃ ξR : ℝ, 0 < ξR ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξR,
      supDistLU d R (F ξ) (euclidDistC d) ≤ ENNReal.ofReal (K * Real.sqrt ξ) := by
  refine ⟨endA k₁, endA_pos k₁, fun ξ hξ => ?_⟩
  obtain ⟨hξ0, hξ1⟩ := hξ
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hξ0 (hξ1.trans (endA_le_one _))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hk : k₁ ≤ n + 1 := by
    have h1 : (1 / 2 : ℝ) ^ (n + 1) < (1 / 2) ^ k₁ := hn1.trans_le hξ1
    have h2 := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).1 h1
    omega
  have hblock : ξ ∈ Icc (endA (n + 1)) (2 * endA (n + 1)) := by
    refine ⟨hn1.le, ?_⟩
    rw [endA_succ]
    have : endA n = (1 / 2) ^ n := rfl
    linarith
  have hε : endEps (n + 1) ≤ Real.sqrt ξ := Real.sqrt_le_sqrt hn1.le
  refine endpt_supDistLU_le_iff.2 fun p hp => ?_
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal ((h (n + 1) hk ξ hblock p hp).trans (by gcongr))

end HigherDimLQGContinuity
